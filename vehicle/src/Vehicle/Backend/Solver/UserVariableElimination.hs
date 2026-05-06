module Vehicle.Backend.Solver.UserVariableElimination
  ( eliminateExists,
    eliminateExistless,
  )
where

-- Needed as Applicative is exported by Prelude in GHC 9.6 and above.
import Control.Applicative (Applicative (..))
import Control.Monad (forM)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.State (MonadState (..))
import Control.Monad.Writer (MonadWriter (..), WriterT (..))
import Vehicle.Backend.Solver.UserVariableElimination.Core
import Vehicle.Backend.Solver.UserVariableElimination.EliminateExists (eliminateQuantifiedVariable)
import Vehicle.Compile.Constants.Rational
import Vehicle.Compile.Error
import Vehicle.Compile.ExpandResources.Core (lookupNetworkInfo)
import Vehicle.Compile.Normalise.NBE (extendClosureWithBound)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Compile.Rational.LinearExpr (LinearityError (..), compileLinearAssertion)
import Vehicle.Compile.TypedView
import Vehicle.Compile.TypedView.Purification (purifyAssertion)
import Vehicle.Compile.TypedView.Unblock (CompilableBoolExpr (..), UnblockingActions (..), forceCompilableBoolExpr)
import Vehicle.Compile.Variable (createUserVar)
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Normalise (forceDims, forceDimsHead, unforcedBuiltinApp)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Builtin.Standard.Normalise (mkDims)
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.MaybeTrivial
import Vehicle.Data.Variable.Bound.Context.Name (getNameContext, prettyFriendlyInCtx)
import Vehicle.Data.Variable.Bound.Context.Tensor (replaceTensorVariableWithStackedChildren)
import Vehicle.Data.Variable.Bound.Level
import Vehicle.Verify.Core (inputShape)
import Vehicle.Verify.QueryFormat (QueryFormat (..), supportsStrictInequalities)
import Prelude hiding (Applicative (..))

eliminateExists ::
  (MonadQueryStructure m) =>
  QuantifyRatTensorArgs (Thunk Builtin) ->
  m (MaybeTrivial Partitions)
eliminateExists (QuantifyRatTensorArgs _ fn) = do
  let (binder, closure) = accessQuantifierLambda fn
  let varName = getBinderName binder
  let subpassDoc = "elimination of existential quantifier over" <+> quotePretty varName
  logCompilerSection2 MidDetail subpassDoc $ do
    -- Extract the shape of the user variable
    propertyProv <- asks propertyProvenance
    userVarShapeValue <- createUserVar propertyProv binder
    forcedDims <- forceDims userVarShapeValue
    userVarShape <- case forcedDims of
      Just shape -> return shape
      _ -> do
        namedCtx <- getNameContext
        throwError $ VariableSizeTensorQuantification propertyProv namedCtx binder userVarShapeValue

    -- Update the global context
    globalCtx <- get
    (userVar, newGlobalCtx) <- addUserVarToGlobalContext binder userVarShape globalCtx
    put newGlobalCtx

    -- Normalise the expression
    normExpr <- extendClosureWithBound binder closure

    -- Recursively compile the expression.
    (partitions, networkInputEqualities) <-
      logCompilerSection2 MidDetail "reduction of body to assertion tree" $ runWriterT (compileBoolExpr normExpr)

    -- Prepend network equalities to the tree (prepending is important for
    -- performance as the search for constraints will find them first.)
    networkEqPartitions <-
      logCompilerSection2 MidDetail "reduction of network equalities to assertion tree" $ networkEqualitiesToPartition networkInputEqualities

    let finalPartitions = andTrivial andPartitions partitions networkEqPartitions

    -- Solve for the user variable
    eliminateQuantifiedVariable finalPartitions userVar

eliminateExistless ::
  (MonadQueryStructure m) =>
  Thunk Builtin ->
  m (MaybeTrivial Partitions)
eliminateExistless value = do
  (maybePartitions, equalities) <- runWriterT $ compileBoolExpr value
  networkEqPartitions <- networkEqualitiesToPartition equalities
  return $ andTrivial andPartitions maybePartitions networkEqPartitions

-- | Attempts to compile an arbitrary expression of type `Bool` down to a tree
-- of assertions implicitly existentially quantified by a set of network
-- input/output variables.
compileBoolExpr ::
  (MonadQueryStructure m, MonadWriter [Thunk Builtin] m) =>
  Thunk Builtin ->
  m (MaybeTrivial Partitions)
compileBoolExpr value = do
  showEntry value
  showExit =<< do
    forcedValue <- forceCompilableBoolExpr unblockingActions value
    case forcedValue of
      ----------------
      -- Base cases --
      ----------------
      CBoolLiteral b -> return $ Trivial b
      CBoolCompareRatTensor (op, args) -> purifyAndCompileAssertion op args
      CBoolQuantifyRatTensor (Forall, _) -> throwError catchableUnsupportedAlternatingQuantifiersError
      ---------------------
      -- Recursive cases --
      ---------------------
      CBoolAnd (TensorOp2Args _dims x y) -> andTrivial andPartitions <$> compileBoolExpr x <*> compileBoolExpr y
      CBoolOr (TensorOp2Args _dims x y) -> orTrivial orPartitions <$> compileBoolExpr x <*> compileBoolExpr y
      CBoolQuantifyRatTensor (Exists, args) -> eliminateExists args

purifyAndCompileAssertion ::
  (MonadQuantifierBody m) =>
  ComparisonOp ->
  TensorOp2Args (Thunk Builtin) ->
  m (MaybeTrivial Partitions)
purifyAndCompileAssertion op args
  | op == Ne =
      -- We can't handle negative equalities so just eliminate it
      compileBoolExpr =<< eliminateNotEqualRatTensor args
  | otherwise = do
      recurseOrResult <- logCompilerSection2 MaxDetail "assertion compilation" $ do
        maybePurifiedValue <- purifyAssertion unblockingActions op args
        case maybePurifiedValue of
          Left purifiedValue -> return $ Left purifiedValue
          Right purifiedArgs -> compilePurifiedAssertion op purifiedArgs

      case recurseOrResult of
        Left value -> compileBoolExpr value
        Right assertion -> return $ mkTrivialPartition assertion

compilePurifiedAssertion ::
  (MonadQuantifierBody m) =>
  ComparisonOp ->
  TensorOp2Args (Thunk Builtin) ->
  m (Either (Thunk Builtin) LinearAssertion)
compilePurifiedAssertion op args@(TensorOp2Args dims xs ys) = do
  maybeShape <- forceDims dims
  let shape = case maybeShape of
        Nothing -> developerError $ "Non-concrete dimensions found" <+> prettyVerbose dims
        Just concreteShape -> concreteShape

  maybeLinearAssertion <- compileLinearAssertion findVariableFromLevel op shape xs ys
  case maybeLinearAssertion of
    Right assertion -> do
      return $ Right assertion
    Left NonLinearity ->
      throwError catchableUnsupportedNonLinearConstraint
    Left (TrivialExpr b) ->
      return $ Left $ Forced $ IBoolLiteral b
    Left (UnreducedExpr e) -> do
      logDebugM MaxDetail $ do
        exprDoc <- prettyFriendlyInCtx e
        return $ "non-variable-terms:" <+> exprDoc
      elementComparisonValue <- eliminateTensorAssertion op args
      logDebugM MaxDetail $ do
        newValueDoc <- prettyFriendlyInCtx elementComparisonValue
        return $ "converting-to-element-assertions:" <+> newValueDoc
      return $ Left elementComparisonValue

findVariableFromLevel :: (MonadQueryStructure m) => Lv -> m SliceVariable
findVariableFromLevel = return . SliceVariable

--------------------------------------------------------------------------------
-- Unblocking

type MonadQuantifierBody m =
  ( MonadQueryStructure m,
    MonadWriter [Thunk Builtin] m
  )

unblockingActions :: (MonadQuantifierBody m) => UnblockingActions m
unblockingActions =
  UnblockingActions
    { unblockRatTensorBoundVar = unblockQuantifiedBoundVar,
      unblockNetworkApp = unblockNetworkApplication
    }

unblockQuantifiedBoundVar ::
  (MonadQuantifierBody m) =>
  Lv ->
  m (Thunk Builtin)
unblockQuantifiedBoundVar lv =
  replaceTensorVariableWithStackedChildren (SliceVariable lv)

unblockNetworkApplication ::
  (MonadQuantifierBody m) =>
  (Thunk Builtin -> m (Thunk Builtin)) ->
  Identifier ->
  NetworkAppArgs (Thunk Builtin) ->
  m (Thunk Builtin)
unblockNetworkApplication unblockFn ident (NetworkAppArgs arg) = do
  let name = nameOf ident
  networkInfo <- asks (lookupNetworkInfo name . networkCtx)

  (inputVarExpr, outputVarExpr) <- addNetworkApplicationToGlobalCtx name networkInfo arg
  let inputEquality =
        fromBoolValue $
          VCompareRatTensor
            ( Eq,
              TensorOp2Args
                { tensorOp2Dims = mkDims (inputShape networkInfo),
                  tensorOp2Arg1 = inputVarExpr,
                  tensorOp2Arg2 = arg
                }
            )
  tell [inputEquality]

  logDebugM MaxDetail $ do
    inputEqualityDoc <- prettyFriendlyInCtx inputEquality
    replacementExprDoc <- prettyFriendlyInCtx outputVarExpr
    return $
      "note-input-equality" <+> inputEqualityDoc
        <> line
        <> "replace-expr" <+> replacementExprDoc

  unblockFn outputVarExpr

--------------------------------------------------------------------------------
-- Elimination operations

eliminateNotEqualRatTensor ::
  (MonadQueryStructure m) =>
  TensorOp2Args (Thunk Builtin) ->
  m (Thunk Builtin)
eliminateNotEqualRatTensor args@(TensorOp2Args dims _ _) = do
  PropertyMetaData {..} <- ask
  if supportsStrictInequalities queryFormat
    then throwError $ UnsupportedInequality (queryFormatID queryFormat) propertyProvenance
    else do
      let leq = fromBoolValue $ VCompareRatTensor (Le, args)
      let geq = fromBoolValue $ VCompareRatTensor (Ge, args)
      return $ fromBoolValue $ VOr (TensorOp2Args dims leq geq)

eliminateTensorAssertion ::
  forall m.
  (MonadQueryStructure m) =>
  ComparisonOp ->
  TensorOp2Args (Thunk Builtin) ->
  m (Thunk Builtin)
eliminateTensorAssertion op (TensorOp2Args dims xs ys) = do
  maybeDimHead <- forceDimsHead dims
  case maybeDimHead of
    Just (d, ds) ->
      return $
        unforcedBuiltinApp (applyAccessor accessCompareRatTensorReducedBuiltin op) $
          TensorComparisonArgs
            { tensorComparisonPointwiseDims = _,
              tensorComparisonReducedDims = _,
              tensorComparisonOpArg1 = etaReduceAndStack d ds xs,
              tensorComparisonOpArg2 = etaReduceAndStack d ds ys
            }
    _ -> compilerDeveloperError ("unexpected dimensions" <+> prettyVerbose dims)
  where
    etaReduceAndStack :: Int -> Thunk Builtin -> Thunk Builtin -> Thunk Builtin
    etaReduceAndStack d ds vs =
      Forced $
        mkExpr accessStackTensor $
          StackTensorArgs
            { stackType = Forced IRatType,
              stackFirstDim = Forced $ INatLiteral d,
              stackRemainingDims = ds,
              stackElements = etaReduceTensor (Forced IRatType) d ds vs
            }

networkEqualitiesToPartition ::
  (MonadQueryStructure m) =>
  [Thunk Builtin] ->
  m (MaybeTrivial Partitions)
networkEqualitiesToPartition networkEqualities = do
  logDebugM MaxDetail $ do
    networkEqDocs <- traverse prettyFriendlyInCtx networkEqualities
    return $ vsep networkEqDocs <> line

  results <- forM networkEqualities $ \equality -> do
    (partitions, newNetworkEqualities) <- runWriterT (compileBoolExpr equality)
    if null newNetworkEqualities
      then return partitions
      else andTrivial andPartitions partitions <$> networkEqualitiesToPartition newNetworkEqualities

  return $ foldr (andTrivial andPartitions) (Trivial True) results

--------------------------------------------------------------------------------
-- Vector operations preservation

-- | Constructs a temporary error with no real fields. This should be recaught
-- and populated higher up the query compilation process.
catchableUnsupportedAlternatingQuantifiersError :: CompileError
catchableUnsupportedAlternatingQuantifiersError =
  UnsupportedAlternatingQuantifiers x x x
  where
    x = developerError "Evaluating temporary quantifier error"

-- | Constructs a temporary error with no real fields. This should be recaught
-- and populated higher up the query compilation process.
catchableUnsupportedNonLinearConstraint :: CompileError
catchableUnsupportedNonLinearConstraint =
  UnsupportedNonLinearConstraint x x x
  where
    x = developerError "Evaluating temporary quantifier error"

showEntry :: (MonadQueryStructure m) => Thunk Builtin -> m ()
showEntry v = do
  logDebugM MaxDetail $ do
    vDoc <- prettyFriendlyInCtx v
    return $ "elim-enter" <+> vDoc
  incrCallDepth

showExit ::
  (MonadQueryStructure m) =>
  MaybeTrivial Partitions ->
  m (MaybeTrivial Partitions)
showExit v = do
  decrCallDepth
  logDebugM MaxDetail $ do
    -- vDoc <- prettyExternalInCtx v
    return $ "elim-exit" <+> pretty (partitionsSize v) -- vDoc
  return v
