{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Vehicle.Compile.Type.Constraint.UnificationSolver
  ( runUnificationSolver,
    solveUnificationConstraint,
    unify,
    UnificationResult (..),
  )
where

import Control.Monad (forM)
import Control.Monad.Except (MonadError (..))
import Data.EnumMap (EnumMap)
import Data.EnumMap qualified as EnumMap
import Data.EnumSet qualified as EnumSet
import Data.List (intersect)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty (toList)
import Data.Map.Ordered.Strict qualified as OMap
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Proxy (Proxy (..))
import Prettyprinter (sep)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Normalise.Quote (unnormalise)
import Vehicle.Compile.Normalise.Value (forceValue)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyExternal, prettyFriendly, prettyVerbose)
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Meta
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet (null, singleton)
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.Monad.Class
import Vehicle.Data.Builtin.Interface.Type (TypableBuiltin (..))
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Generic
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Bound.Level (dbLevelToIndex)
import Vehicle.Data.Variable.Free.Context (MonadFreeContext (..))

--------------------------------------------------------------------------------
-- Unification solver

-- See https://github.com/AndrasKovacs/elaboration-zoo/
-- for an excellent tutorial on the algorithm.

-- | Attempts to solve as many unification constraints as possible.
runUnificationSolver :: (MonadUnify builtin m) => Proxy builtin -> Bool -> m ()
runUnificationSolver proxy topLevel =
  logCompilerSection2 MaxDetail "unification solver run" $
    runConstraintSolver
      getActiveUnificationConstraints
      setUnificationConstraints
      solveUnificationConstraint
      topLevel
      proxy

--------------------------------------------------------------------------------
-- Unification algorithm

type MonadUnify builtin m =
  ( MonadTypeChecker builtin m,
    TypableBuiltin builtin
  )

type UnificationProblem builtin =
  ( BoundCtx (Type builtin),
    Thunk builtin,
    Thunk builtin
  )

type ConstraintInfo builtin =
  ( UnificationProblem builtin,
    MetaSet
  )

infoBoundCtx :: ConstraintInfo builtin -> BoundCtx (Type builtin)
infoBoundCtx ((ctx, _, _), _) = ctx

data UnificationResult builtin
  = Success
  | -- | Always an error
    HardFailure (NonEmpty (UnificationProblem builtin))
  | -- | Only an error when further reduction will never occur.
    Blocked (NonEmpty (ConstraintInfo builtin))

solveUnificationConstraint ::
  forall builtin m.
  (MonadUnify builtin m) =>
  WithContext (UnificationConstraint builtin) ->
  m ()
solveUnificationConstraint (WithContext (Unify origin e1 e2) ctx) = do
  result <- unify (boundContextOf ctx) e1 e2
  case result of
    Success -> return ()
    Blocked blockedProblems -> do
      newConstraints <- forM blockedProblems $ createNewConstraint ctx origin
      addUnificationConstraints $ NonEmpty.toList newConstraints
    HardFailure failedProblems -> do
      finalFailedConstraints <- forM failedProblems $ \problem ->
        createNewConstraint ctx origin (problem, mempty)
      freeCtx <- getFreeCtx (Proxy @builtin)
      throwError $ TypingError $ FailedUnificationConstraints $ FailedUnificationConstraintsError freeCtx finalFailedConstraints

createNewConstraint ::
  (MonadUnify builtin m) =>
  ConstraintContext builtin ->
  UnificationConstraintOrigin builtin ->
  (UnificationProblem builtin, MetaSet) ->
  m (WithContext (UnificationConstraint builtin))
createNewConstraint constraintCtx origin ((boundCtx, e1, e2), blockingMetas) = do
  newConstraint <- WithContext (Unify origin e1 e2) <$> copyContext constraintCtx (Just boundCtx)
  return $ blockConstraintOn newConstraint blockingMetas

unify ::
  forall builtin m.
  (MonadUnify builtin m) =>
  BoundCtx (Type builtin) ->
  Thunk builtin ->
  Thunk builtin ->
  m (UnificationResult builtin)
unify ctx e1 e2 = do
  -- Force the heads of both expressions
  let namedCtx = toNamedBoundCtx ctx
  (fe1, e1BlockingMetas) <- runNameBoundContextT namedCtx $ forceValue e1
  (fe2, e2BlockingMetas) <- runNameBoundContextT namedCtx $ forceValue e2

  -- Construct the new constraint information
  let blockingMetas = e1BlockingMetas <> e2BlockingMetas
  let constraintInfo = ((ctx, Forced fe1, Forced fe2), blockingMetas)

  -- Perform the unification
  let prettyExpr e = prettyExternal (WithContext e namedCtx)
  let passDoc = "unifying" <+> prettyExpr fe1 <+> "~" <+> prettyExpr fe2 -- <+> "in context" <+> prettyVerbose ctx
  logIndent MaxDetail passDoc $ do
    unification constraintInfo (e1, e2) (fe1, fe2)

instance Semigroup (UnificationResult builtin) where
  HardFailure r1 <> HardFailure r2 = HardFailure (r1 <> r2)
  r1@HardFailure {} <> _ = r1
  _ <> r2@HardFailure {} = r2
  Blocked m1 <> Blocked m2 = Blocked (m1 <> m2)
  r1@Blocked {} <> _ = r1
  _ <> r2@Blocked {} = r2
  Success <> Success = Success

instance Monoid (UnificationResult builtin) where
  mempty = Success

-- | Create a new unification constraint, copying the context as appropriate.
subUnify ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  Thunk builtin ->
  Thunk builtin ->
  m (UnificationResult builtin)
subUnify info = unify (infoBoundCtx info)

block ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  Maybe MetaSet ->
  m (UnificationResult builtin)
block (problem, originalBlockingMetas) maybeRefinedBlockingMetas = do
  let blockingMetas = fromMaybe originalBlockingMetas maybeRefinedBlockingMetas
  if MetaSet.null blockingMetas
    then return $ HardFailure [problem]
    else return $ Blocked [(problem, blockingMetas)]

pattern (:~:) :: a -> b -> (a, b)
pattern x :~: y = (x, y)

unification ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  (Thunk builtin, Thunk builtin) ->
  (Value builtin, Value builtin) ->
  m (UnificationResult builtin)
unification info (o1, o2) = \case
  -----------------------
  -- Rigid-rigid cases --
  -----------------------
  VUniverse l1 :~: VUniverse l2
    | l1 == l2 -> solveTrivially
  VBoundVar v1 spine1 :~: VBoundVar v2 spine2
    | v1 == v2 -> solveSpine info spine1 spine2
  VFreeVar v1 spine1 :~: VFreeVar v2 spine2
    | v1 == v2 -> solveSpine info spine1 spine2
  VBuiltin b1 spine1 :~: VBuiltin b2 spine2
    | b1 == b2 -> solveSpine info spine1 spine2
    | isConstructor b1 && isConstructor b2 -> hardFail info
  VPi binder1 closure1 :~: VPi binder2 closure2
    | visibilityMatches binder1 binder2 -> solveClosure info (binder1, closure1) (binder2, closure2)
  VLam binder1 closure1 :~: VLam binder2 closure2 ->
    solveClosure info (binder1, closure1) (binder2, closure2)
  VRecord ident1 fields1 :~: VRecord ident2 fields2
    | ident1 == ident2 -> solveRecords info fields1 fields2
  VRecordAcc _recordType1 record1 field1 spine1 :~: VRecordAcc _recordType2 record2 field2 spine2
    | field1 == field2 -> do
        recordResult <- subUnify info record1 record2
        spineResult <- solveSpine info spine1 spine2
        return $ recordResult <> spineResult
  ---------------------
  -- Flex-flex cases --
  ---------------------
  VMeta meta1 spine1 :~: VMeta meta2 spine2
    | meta1 == meta2 -> solveSpine info spine1 spine2
    -- The longer spine normally means its in a deeper scope. This minor
    -- optimisation tries to solve the deeper meta first.
    | length spine1 < length spine2 -> solveFlexFlex info (meta2, spine2) (meta1, spine1)
    | otherwise -> solveFlexFlex info (meta1, spine1) (meta2, spine2)
  ----------------------
  -- Flex-rigid cases --
  ----------------------
  VMeta meta spine :~: _ -> solveFlexRigid info (meta, spine) o2
  _ :~: VMeta meta spine -> solveFlexRigid info (meta, spine) o1
  ------------------
  -- Blocked case --
  ------------------
  _ -> block info Nothing

solveTrivially :: (MonadUnify builtin m) => m (UnificationResult builtin)
solveTrivially = do
  logDebug MaxDetail "solved-trivially"
  return Success

solveArg ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  (VArg builtin, VArg builtin) ->
  m (UnificationResult builtin)
solveArg info (arg1, arg2)
  | not (visibilityMatches arg1 arg2) = hardFail info
  -- Don't unify instances, they should be uniquely determined by the type.
  | isInstance arg1 = return Success
  | otherwise = subUnify info (argExpr arg1) (argExpr arg2)

solveSpine ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  Spine builtin ->
  Spine builtin ->
  m (UnificationResult builtin)
solveSpine info args1 args2
  | length args1 /= length args2 = hardFail info
  | otherwise = mconcat <$> traverse (solveArg info) (zip args1 args2)

solveRecords ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  SearchableRecordFields (Thunk builtin) ->
  SearchableRecordFields (Thunk builtin) ->
  m (UnificationResult builtin)
solveRecords info fields1 fields2 = do
  -- Note we don't need to check that the fields align as scope checking should have
  -- already done this for us.
  let sharedFields = OMap.assocs $ OMap.intersectionWith (const (,)) fields1 fields2
  let solveField (_name, (v1, v2)) = subUnify info v1 v2
  mconcat <$> traverse solveField sharedFields

solveClosure ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  (VBinder builtin, Closure builtin) ->
  (VBinder builtin, Closure builtin) ->
  m (UnificationResult builtin)
solveClosure info (binder1, body1) (binder2, body2) = do
  -- Unify binder constraints
  binderConstraint <- subUnify info (typeOf binder1) (typeOf binder2)

  -- Unify the two bodies
  let ctx = toNamedBoundCtx $ infoBoundCtx info
  body1Value <- runNameBoundContextT ctx $ extendClosureWithBound binder1 body1
  body2Value <- runNameBoundContextT ctx $ extendClosureWithBound binder2 body2
  let updatedInfo = updateInfoUnderBinder info (binder1, binder2)
  bodyConstraint <- subUnify updatedInfo body1Value body2Value

  -- Return the result
  return $ binderConstraint <> bodyConstraint

solveFlexFlex ::
  forall builtin m.
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  (MetaID, Spine builtin) ->
  (MetaID, Spine builtin) ->
  m (UnificationResult builtin)
solveFlexFlex info (meta1, spine1) (meta2, spine2) = do
  let proxy = Proxy @builtin
  c1 <- length <$> getMetaCtx proxy meta1
  c2 <- length <$> getMetaCtx proxy meta2
  let (ctx1Args, extraArgs1) = splitAt c1 spine1
  let (ctx2Args, extraArgs2) = splitAt c2 spine2

  if not (null extraArgs1) && length extraArgs1 == length extraArgs2
    then do
      -- This is a massive hack assuming that the meta is always an injective function.
      -- This is to allow the instance unification to work in the `Decidable` typing
      -- subsystem when inferring if `(Tensor Bool) ds` -> `(\_ds -> Type)` or `Tensor Bool`)
      metaResult <- subUnify info (Forced $ VMeta meta1 ctx1Args) (Forced $ VMeta meta2 ctx2Args)
      spineResults <- solveSpine info extraArgs1 extraArgs2
      return $ metaResult <> spineResults
    else do
      -- It may be that only one of the two spines is invertible
      maybeRenaming <- invert (boundCtxLv (infoBoundCtx info)) (meta1, spine1)
      case maybeRenaming of
        Nothing -> solveFlexRigid info (meta2, spine2) (Forced $ VMeta meta1 spine1)
        Just renaming -> solveFlexRigidWithRenaming (infoBoundCtx info) (meta1, spine1) renaming (Forced $ VMeta meta2 spine2)

solveFlexRigid ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  (MetaID, Spine builtin) ->
  Thunk builtin ->
  m (UnificationResult builtin)
solveFlexRigid info (metaID, spine) solution = do
  let ctx = infoBoundCtx info
  -- Check that 'spine' is a pattern and try to calculate a substitution
  -- that renames the variables in `solution` to ones available to `meta`
  maybeRenaming <- invert (boundCtxLv ctx) (metaID, spine)
  case maybeRenaming of
    Just renaming -> solveFlexRigidWithRenaming ctx (metaID, spine) renaming solution
    -- This constraint is stuck because it is not pattern; shelve
    -- it for now and hope that another constraint allows us to
    -- progress.
    Nothing -> block info (Just (MetaSet.singleton metaID))

solveFlexRigidWithRenaming ::
  forall builtin m.
  (MonadUnify builtin m) =>
  BoundCtx (Type builtin) ->
  (MetaID, Spine builtin) ->
  Renaming ->
  Thunk builtin ->
  m (UnificationResult builtin)
solveFlexRigidWithRenaming ctx (metaID, metaSpine) renaming solution = do
  let unnormSolution = unnormalise (boundCtxLv ctx) solution
  prunedSolution <-
    if not (useDependentMetas (Proxy @builtin))
      then return unnormSolution
      else do
        -- Maybe need to use meta ctx level here?
        let metaArgs = fmap (unnormalise (boundCtxLv ctx)) metaSpine
        pruneMetaDependencies ctx (metaID, metaArgs) unnormSolution
  let substSolution = substDBAll 0 (`EnumMap.lookup` renaming) prunedSolution
  solveMeta metaID substSolution ctx
  return Success

pruneMetaDependencies ::
  forall builtin m.
  (MonadUnify builtin m) =>
  BoundCtx (Type builtin) ->
  (MetaID, Args builtin) ->
  Expr builtin ->
  m (Expr builtin)
pruneMetaDependencies ctx (solvingMetaID, solvingMetaSpine) attemptedSolution = do
  go attemptedSolution
  where
    go ::
      (MonadUnify builtin m) =>
      Expr builtin ->
      m (Expr builtin)
    go expr = case expr of
      App (Meta p metaID) args -> goMeta p metaID (NonEmpty.toList args)
      Meta p metaID -> goMeta p metaID []
      Universe {} -> return expr
      Builtin {} -> return expr
      BoundVar {} -> return expr
      FreeVar {} -> return expr
      Hole {} -> return expr
      Record p ident fields -> Record p ident <$> traverseRecordFields go fields
      RecordProj p recordType record field -> RecordProj p <$> go recordType <*> go record <*> pure field
      Pi p binder body -> Pi p <$> traverse go binder <*> go body
      Lam p binder body -> Lam p <$> traverse go binder <*> go body
      App fun args -> App <$> go fun <*> traverse (traverse go) args
      Let p bound binder body -> Let p <$> go bound <*> traverse go binder <*> go body

    goMeta :: Provenance -> MetaID -> Args builtin -> m (Expr builtin)
    goMeta p m spine
      | m == solvingMetaID =
          -- If `i` is inside the term we're trying to unify it with then error.
          -- Unsure if this should be a user or a developer error.
          compilerDeveloperError $
            "Meta variable"
              <+> pretty m
              <+> "found in own solution"
              <+> squotes (prettyVerbose attemptedSolution)
      | otherwise = do
          metaInfo <- getMetaInfo m
          case metaSolution metaInfo of
            Just solution -> go $ normAppList solution spine
            Nothing -> do
              (deps, _) <- getNormMetaDependencies solvingMetaID solvingMetaSpine
              (jDeps, remainingSpine) <- getNormMetaDependencies m spine
              let sharedDependencies = deps `intersect` jDeps
              if sharedDependencies /= jDeps
                then createMetaWithRestrictedDependencies ctx m sharedDependencies remainingSpine
                else return $ normAppList (Meta p m) spine

    getNormMetaDependencies :: MetaID -> Args builtin -> m ([Ix], Args builtin)
    getNormMetaDependencies meta spine = do
      metaCtx <- getMetaCtx (Proxy @builtin) meta
      let (deps, remainingArgs) = splitAt (length metaCtx) spine
      let getIx arg = case argExpr arg of
            BoundVar _ i -> i
            _ -> developerError $ "Meta variable" <+> pretty meta <+> "has none index arg"
      return (fmap getIx deps, remainingArgs)

createMetaWithRestrictedDependencies ::
  forall builtin m.
  (MonadUnify builtin m) =>
  BoundCtx (Type builtin) ->
  MetaID ->
  [Ix] ->
  Args builtin ->
  m (Expr builtin)
createMetaWithRestrictedDependencies ctx meta newDependencies spine = do
  p <- getMetaProvenance (Proxy @builtin) meta
  metaType <- getMetaType meta

  let newDeps = fmap (\v -> prettyFriendly (WithContext (BoundVar p v :: Expr builtin) (toNamedBoundCtx ctx))) newDependencies
  logCompilerSection MaxDetail ("restricting dependencies of" <+> pretty meta <+> "to" <+> sep newDeps) $ do
    let indexSet = EnumSet.fromList newDependencies
    let makeElem (i, v) = if i `EnumSet.member` indexSet then Just v else Nothing
    let ctxWithLevels = zip [0 .. Ix (length ctx - 1)] ctx
    let restrictedContext = mapMaybe makeElem ctxWithLevels
    newMetaExpr <- freshMetaExpr p metaType restrictedContext

    let substitution = EnumMap.fromAscList (zip [0 ..] (reverse newDependencies))
    let substMetaExpr = substDBAll 0 (`EnumMap.lookup` substitution) newMetaExpr
    solveMeta meta substMetaExpr ctx

    return $ normAppList newMetaExpr spine

updateInfoUnderBinder ::
  ConstraintInfo builtin ->
  (VBinder builtin, VBinder builtin) ->
  ConstraintInfo builtin
updateInfoUnderBinder ((ctx, e1, e2), blockingMetas) (binder1, _binder2) = do
  let unnormBinder = fmap (unnormalise (boundCtxLv ctx)) binder1
  ((unnormBinder : ctx, e1, e2), blockingMetas)

hardFail ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  m (UnificationResult builtin)
hardFail (problem, _) = do
  logDebug MaxDetail "failed"
  return $ HardFailure [problem]

--------------------------------------------------------------------------------
-- Argument patterns

type Renaming = EnumMap Ix Ix

-- | TODO: explain what this means:
-- [i2 i4 i1] --> [2 -> 2, 4 -> 1, 1 -> 0]
invert :: forall builtin m. (MonadUnify builtin m) => Lv -> (MetaID, Spine builtin) -> m (Maybe Renaming)
invert ctxSize (metaID, spine) = do
  metaCtxSize <- length <$> getMetaCtx (Proxy @builtin) metaID
  return $
    if metaCtxSize < length spine
      then Nothing
      else go (metaCtxSize - 1) mempty spine
  where
    go :: Int -> Renaming -> Spine builtin -> Maybe Renaming
    go i revMap = \case
      [] -> Just revMap
      (ExplicitArg _ (Forced (VBoundVar j [])) : restArgs) -> do
        -- TODO: we could eta-reduce arguments too, if possible
        let jIndex = dbLevelToIndex ctxSize j
        if EnumMap.member jIndex revMap
          then -- TODO: mark 'j' as ambiguous, and remove ambiguous entries before returning;
          -- but then we should make sure the solution is well-typed
            Nothing
          else go (i - 1) (EnumMap.insert jIndex (Ix i) revMap) restArgs
      -- Not a pattern so return nothing.
      _ -> Nothing
