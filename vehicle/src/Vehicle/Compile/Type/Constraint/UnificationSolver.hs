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
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.List (intersect)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty (toList)
import Data.Map.Ordered.Strict qualified as OMap
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Proxy (Proxy (..))
import Prettyprinter (sep)
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyExternal, prettyFriendly, prettyVerbose)
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Force (ForcedExpr (..), forceHead, unforce)
import Vehicle.Compile.Type.Meta
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet (null, singleton)
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.Monad.Class
import Vehicle.Data.Builtin.Interface.Type (TypableBuiltin (..))
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Generic
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
    Expr builtin,
    Expr builtin
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
  Expr builtin ->
  Expr builtin ->
  m (UnificationResult builtin)
unify ctx e1 e2 = do
  -- Force the heads of both expressions
  let namedCtx = toNamedBoundCtx ctx
  (fe1, e1BlockingMetas) <- forceHead namedCtx e1
  (fe2, e2BlockingMetas) <- forceHead namedCtx e2
  let fe1' = unforce fe1
  let fe2' = unforce fe2

  -- Construct the new constraint information
  let blockingMetas = e1BlockingMetas <> e2BlockingMetas
  let constraintInfo = ((ctx, fe1', fe2'), blockingMetas)

  -- Perform the unification
  let prettyExpr e = prettyExternal (WithContext e namedCtx)
  let passDoc = "unifying" <+> prettyExpr fe1' <+> "~" <+> prettyExpr fe2' -- <+> "in context" <+> prettyVerbose ctx
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
  Expr builtin ->
  Expr builtin ->
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
  (Expr builtin, Expr builtin) ->
  (ForcedExpr builtin, ForcedExpr builtin) ->
  m (UnificationResult builtin)
unification info (o1, o2) = \case
  -----------------------
  -- Rigid-rigid cases --
  -----------------------
  FUniverse _ l1 :~: FUniverse _ l2
    | l1 == l2 -> solveTrivially
  FBoundVar _ v1 spine1 :~: FBoundVar _ v2 spine2
    | v1 == v2 -> solveSpine info spine1 spine2
  FFreeVar _ v1 spine1 :~: FFreeVar _ v2 spine2
    | v1 == v2 -> solveSpine info spine1 spine2
  FBuiltin _ b1 spine1 :~: FBuiltin _ b2 spine2
    | b1 == b2 -> solveSpine info spine1 spine2
    | isConstructor b1 && isConstructor b2 -> hardFail info
  FPi _ binder1 closure1 :~: FPi _ binder2 closure2
    | visibilityMatches binder1 binder2 -> solveClosure info (binder1, closure1) (binder2, closure2)
  FLam _ binder1 closure1 :~: FLam _ binder2 closure2 ->
    solveClosure info (binder1, closure1) (binder2, closure2)
  FRecord _ ident1 fields1 :~: FRecord _ ident2 fields2
    | ident1 == ident2 -> solveRecords info fields1 fields2
  FRecordAcc _ _recordType1 record1 field1 spine1 :~: FRecordAcc _ _recordType2 record2 field2 spine2
    | field1 == field2 -> do
        recordResult <- subUnify info record1 record2
        spineResult <- solveSpine info spine1 spine2
        return $ recordResult <> spineResult
  ---------------------
  -- Flex-flex cases --
  ---------------------
  FMeta p1 meta1 spine1 :~: FMeta p2 meta2 spine2
    | meta1 == meta2 -> solveSpine info spine1 spine2
    -- The longer spine normally means its in a deeper scope. This minor
    -- optimisation tries to solve the deeper meta first.
    | length spine1 < length spine2 -> solveFlexFlex info (p1, meta2, spine2) (p2, meta1, spine1)
    | otherwise -> solveFlexFlex info (p1, meta1, spine1) (p2, meta2, spine2)
  ----------------------
  -- Flex-rigid cases --
  ----------------------
  FMeta _ meta spine :~: _ -> solveFlexRigid info (meta, spine) o2
  _ :~: FMeta _ meta spine -> solveFlexRigid info (meta, spine) o1
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
  (Arg builtin, Arg builtin) ->
  m (UnificationResult builtin)
solveArg info (arg1, arg2)
  | not (visibilityMatches arg1 arg2) = hardFail info
  -- Don't unify instances, they should be uniquely determined by the type.
  | isInstance arg1 = return Success
  | otherwise = subUnify info (argExpr arg1) (argExpr arg2)

solveSpine ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  Args builtin ->
  Args builtin ->
  m (UnificationResult builtin)
solveSpine info args1 args2
  | length args1 /= length args2 = hardFail info
  | otherwise = mconcat <$> traverse (solveArg info) (zip args1 args2)

solveRecords ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  SearchableRecordFields (Expr builtin) ->
  SearchableRecordFields (Expr builtin) ->
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
  (Binder builtin, Expr builtin) ->
  (Binder builtin, Expr builtin) ->
  m (UnificationResult builtin)
solveClosure info (binder1, body1) (binder2, body2) = do
  -- Unify binder constraints
  binderConstraint <- subUnify info (typeOf binder1) (typeOf binder2)

  -- Update the context.
  let updatedInfo = updateInfoUnderBinder info (binder1, binder2)

  -- Unify the two bodies
  bodyConstraint <- subUnify updatedInfo body1 body2

  -- Return the result
  return $ binderConstraint <> bodyConstraint

solveFlexFlex ::
  forall builtin m.
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  (Provenance, MetaID, Args builtin) ->
  (Provenance, MetaID, Args builtin) ->
  m (UnificationResult builtin)
solveFlexFlex info (p1, meta1, spine1) (p2, meta2, spine2) = do
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
      metaResult <- subUnify info (normAppList (Meta p1 meta1) ctx1Args) (normAppList (Meta p2 meta2) ctx2Args)
      spineResults <- solveSpine info extraArgs1 extraArgs2
      return $ metaResult <> spineResults
    else do
      -- It may be that only one of the two spines is invertible
      maybeRenaming <- invert (meta1, spine1)
      case maybeRenaming of
        Nothing -> solveFlexRigid info (meta2, spine2) (normAppList (Meta p1 meta1) spine1)
        Just renaming -> solveFlexRigidWithRenaming (infoBoundCtx info) (meta1, spine1) renaming (normAppList (Meta p2 meta2) spine2)

solveFlexRigid ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  (MetaID, Args builtin) ->
  Expr builtin ->
  m (UnificationResult builtin)
solveFlexRigid info (metaID, spine) solution = do
  let ctx = infoBoundCtx info
  -- Check that 'spine' is a pattern and try to calculate a substitution
  -- that renames the variables in `solution` to ones available to `meta`
  maybeRenaming <- invert (metaID, spine)
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
  (MetaID, Args builtin) ->
  Renaming ->
  Expr builtin ->
  m (UnificationResult builtin)
solveFlexRigidWithRenaming ctx meta@(metaID, _) renaming solution = do
  prunedSolution <-
    if useDependentMetas (Proxy @builtin)
      then pruneMetaDependencies ctx meta solution
      else return solution
  let substSolution = substDBAll 0 (\v -> unIx v `IntMap.lookup` renaming) prunedSolution
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
      Meta p m -> goMeta p m []
      App (Meta p m) args -> goMeta p m $ NonEmpty.toList args
      Universe {} -> return expr
      Builtin {} -> return expr
      BoundVar {} -> return expr
      FreeVar {} -> return expr
      Record p ident fields -> Record p ident <$> traverseRecordFields go fields
      RecordProj p recordType record field ->
        RecordProj p <$> go recordType <*> go record <*> pure field
      Pi p binder body -> Pi p <$> traverse go binder <*> go body
      Lam p binder body -> Lam p <$> traverse go binder <*> go body
      Hole {} -> return expr
      Let p bound binder body -> Let p <$> go bound <*> traverse go binder <*> go body
      App fun args -> App <$> go fun <*> traverse (traverse go) args

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
          case unnormalised <$> metaSolution metaInfo of
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
    let levelSet = IntSet.fromList $ fmap unIx newDependencies
    let makeElem (i, v) = if i `IntSet.member` levelSet then Just v else Nothing
    let ctxWithLevels = zip (reverse [0 .. length ctx - 1 :: Int]) ctx
    let restrictedContext = mapMaybe makeElem ctxWithLevels
    newMetaExpr <- freshMetaExpr p metaType restrictedContext

    let substitution = IntMap.fromAscList (zip [0 ..] (reverse newDependencies))
    let substMetaExpr = substDBAll 0 (\v -> unIx v `IntMap.lookup` substitution) newMetaExpr
    solveMeta meta substMetaExpr ctx

    return $ normAppList newMetaExpr spine

updateInfoUnderBinder ::
  ConstraintInfo builtin ->
  (Binder builtin, Binder builtin) ->
  ConstraintInfo builtin
updateInfoUnderBinder ((ctx, e1, e2), blockingMetas) (binder1, _binder2) = do
  ((binder1 : ctx, e1, e2), blockingMetas)

hardFail ::
  (MonadUnify builtin m) =>
  ConstraintInfo builtin ->
  m (UnificationResult builtin)
hardFail (problem, _) = do
  logDebug MaxDetail "failed"
  return $ HardFailure [problem]

--------------------------------------------------------------------------------
-- Argument patterns

type Renaming = IntMap Ix

-- | TODO: explain what this means:
-- [i2 i4 i1] --> [2 -> 2, 4 -> 1, 1 -> 0]
invert :: forall builtin m. (MonadUnify builtin m) => (MetaID, Args builtin) -> m (Maybe Renaming)
invert (metaID, spine) = do
  metaCtxSize <- length <$> getMetaCtx (Proxy @builtin) metaID
  return $
    if metaCtxSize < length spine
      then Nothing
      else go (metaCtxSize - 1) IntMap.empty spine
  where
    go :: Int -> IntMap Ix -> Args builtin -> Maybe Renaming
    go i revMap = \case
      [] -> Just revMap
      (ExplicitArg _ (BoundVar _ j) : restArgs) -> do
        -- TODO: we could eta-reduce arguments too, if possible
        if IntMap.member (unIx j) revMap
          then -- TODO: mark 'j' as ambiguous, and remove ambiguous entries before returning;
          -- but then we should make sure the solution is well-typed
            Nothing
          else go (i - 1) (IntMap.insert (unIx j) (Ix i) revMap) restArgs
      -- Not a pattern so return nothing.
      _ -> Nothing
