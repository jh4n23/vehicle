module Vehicle.Compile.Unblock
  ( unblockBoolExpr,
    UnblockingActions (..),
    OperationUnblockingFunction,
    TypeUnblockingFunction,
    unblockRatTensorValue,
    unblockIndexValue,
    unblockRecordValue,
    unblockIf,
    unblockAtTensor,
    unblockAtVector,
    unblockForeachTensor,
    unblockReduceTensor,
    unblockMinRatTensor,
    unblockMaxRatTensor,
    unblockTensorOp2,
    unblockTensorOp1,
    unblockRecordAcc,
    toComparison,
    forceEval,
  )
where

import Vehicle.Compile.LiftIf (unfoldIf)
import Vehicle.Compile.Normalise.BuiltinForced
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Normalise.NBEForced
import Vehicle.Compile.Normalise.TypedValueForced
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.BooleanExpr (IfTree (..), elimIfTree, forIfTreeM)
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Code.Interface
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context.Class

--------------------------------------------------------------------------------
-- Unblocking
--------------------------------------------------------------------------------

type MonadUnblock m =
  ( MonadLogger m,
    MonadFreeContext Builtin m,
    MonadReadableNameContext m
  )

type MonadPurify m = MonadUnblock m

data UnblockingActions m = UnblockingActions
  { unblockRatTensorBoundVar ::
      Lv ->
      m (Thunk Builtin),
    unblockNetworkApp ::
      TypeUnblockingFunction (Thunk Builtin) m ->
      TypeUnblockingFunction (Thunk Builtin) m ->
      Identifier ->
      OperationUnblockingFunction NetworkAppArgs (Thunk Builtin) m,
    unblockDatasetOrParameter ::
      Identifier ->
      m (Thunk Builtin),
    unblockRecordBoundVar ::
      Lv ->
      m (Thunk Builtin)
  }

-- | Lifts all `if`s in the provided expression `e` to the top-level, while
-- preserving the guarantee that the expression is normalised as much as
-- possible.
unblockBoolExpr ::
  (MonadUnblock m) =>
  UnblockingActions m ->
  Thunk Builtin ->
  m (Thunk Builtin)
unblockBoolExpr actions expr = do
  exprDoc <- prettyFriendlyInCtx expr
  logCompilerSection MaxDetail ("unblocking" <+> exprDoc) $ do
    ifTree <- unblockBoolTensorValue actions expr
    let elimIf c x y = unfoldIf $ IfArgs (Forced IBoolType) c x y
    elimIfTree elimIf return ifTree

--------------------------------------------------------------------------------
-- Main unblocking functions

type TypeUnblockingFunction a m =
  (MonadUnblock m) =>
  Thunk Builtin ->
  m (IfTree (Thunk Builtin) a)

unblockBoolTensorValue :: UnblockingActions m -> TypeUnblockingFunction (Thunk Builtin) m
unblockBoolTensorValue actions value = showEntry value $ do
  forcedValue <- forceThunk value
  case toBoolTensorValue forcedValue of
    -- Already unblocked
    VBoolTensorLiteral {} -> return $ IfLeaf value
    VBoolStackTensor {} -> return $ IfLeaf value
    VBoolConstTensor {} -> return $ IfLeaf value
    VBoolTensorQuantifyRat {} -> return $ IfLeaf value
    VBoolTensorQuantifyRecord {} -> return $ IfLeaf value
    VBoolTensorAnd args -> unblockTensorOp2 unblock evalAnd args
    VBoolTensorOr args -> unblockTensorOp2 unblock evalOr args
    VBoolTensorNot args -> unblockTensorOp1 unblock evalNot args
    VBoolTensorImplies args -> unblock $ elimImplies args
    VBoolTensorCompareRatReduced {} -> return $ IfLeaf value
    VBoolTensorCompareRatPointwise (op, args) -> unblockTensorOp2 (unblockRatTensorValue actions) (evalCompareRatTensorPointwise op) args
    -- Recursively unblock
    VBoolTensorIf args -> unblockIf unblock args
    VBoolTensorReduceAnd args -> unblockReduceTensor unblock (forceEval evalReduceAndTensor) args
    VBoolTensorReduceOr args -> unblockReduceTensor unblock (forceEval evalReduceOrTensor) args
    VBoolTensorCompareIndex (op, args) -> unblockIndexOp2 (unblockIndexValue actions) (evalCompareIndex op) args
    VBoolTensorCompareNat (op, args) -> unblockOp2 unblockNatValue (evalCompareNat op) args
    VBoolTensorTensorAt args -> unblockAtTensor unblock (unblockIndexValue actions) args
    VBoolTensorVectorAt args -> unblockAtVector unblock (unblockIndexValue actions) args
    VBoolTensorForeach args -> unblockForeachTensor args
  where
    unblock = unblockBoolTensorValue actions

unblockRatTensorValue ::
  (MonadPurify m) =>
  UnblockingActions m ->
  TypeUnblockingFunction (Thunk Builtin) m
unblockRatTensorValue actions@UnblockingActions {..} expr =
  showEntry expr $ do
    forcedValue <- forceThunk expr
    case forcedValue of
      -- Rational operators
      VRatTensorLiteral {} -> return $ IfLeaf expr
      VRatConstTensor {} -> return $ IfLeaf expr
      VRatStackTensor {} -> return $ IfLeaf expr
      -- Recursively purify
      VIfRatTensor args -> unblockIf unblock args
      VNegRatTensor args -> unblockTensorOp1 unblock evalNegRatTensor args
      VLogRatTensor args -> unblockTensorOp1 unblock evalLogRatTensor args
      VExpRatTensor args -> unblockTensorOp1 unblock evalExpRatTensor args
      VAddRatTensor args -> unblockTensorOp2 unblock evalAddRatTensor args
      VSubRatTensor args -> unblockTensorOp2 unblock evalSubRatTensor args
      VMulRatTensor args -> unblockTensorOp2 unblock evalMulRatTensor args
      VDivRatTensor args -> unblockTensorOp2 unblock evalDivRatTensor args
      VPowRatTensor args -> unblockTensorOp2 unblock evalPowRatTensor args
      VReduceAddRatTensor args -> unblockReduceTensor unblock (forceEval evalReduceAddRatTensor) args
      VReduceMulRatTensor args -> unblockReduceTensor unblock (forceEval evalReduceMulRatTensor) args
      VReduceMinRatTensor args -> unblockReduceTensor unblock (forceEval evalReduceMinRatTensor) args
      VReduceMaxRatTensor args -> unblockReduceTensor unblock (forceEval evalReduceMaxRatTensor) args
      VMinRatTensor args -> unblockMinRatTensor unblock args
      VMaxRatTensor args -> unblockMaxRatTensor unblock args
      VRatTensorBoundVar v -> unblock =<< unblockRatTensorBoundVar v
      VNetworkApplication n args -> unblockNetworkApp unblock (unblockRecordValue actions) n args
      VParameterOrDataset ident -> unblock =<< unblockDatasetOrParameter ident
      VRatAtTensor args -> unblockAtTensor unblock (unblockIndexValue actions) args
      VRatAtVector args -> unblockAtVector (unblockVectorValue actions) (unblockIndexValue actions) args
      VRatForeach args -> unblockForeachTensor args
      VRatTensorRecordAcc typ value fieldName args -> unblockRecordAcc actions typ value fieldName args
  where
    unblock = unblockRatTensorValue actions

unblockRecordValue ::
  UnblockingActions m ->
  TypeUnblockingFunction (Thunk Builtin) m
unblockRecordValue actions@UnblockingActions {..} expr = showEntry expr $ do
  forcedValue <- forceThunk expr
  case forcedValue of
    VRecordRecord {} -> return $ IfLeaf expr
    -- VRecordNetworkApp n args -> unblockNetworkApp unblockTensor unblockRecord n args
    VRecordBoundVar v spine -> case spine of
      [] -> unblockRecord =<< unblockRecordBoundVar v
      _ -> unexpectedExprError currentPass "record boundVar with args"
    VRecordFreeVar {} -> unexpectedExprError currentPass "record freeVar"
    VRecordMeta {} -> unexpectedExprError currentPass "record meta"
    VRecordBuiltin b spine -> case VBuiltin b spine of
      (getExpr accessIf -> Just args) -> unblockIf unblockRecord args
      _ -> unexpectedExprError currentPass (pretty b <+> "record")
    VRecordRecordAcc typ record field spine -> unblockRecordAcc actions typ record field spine
  where
    unblockRecord = unblockRecordValue actions

unblockIndexValue ::
  UnblockingActions m ->
  TypeUnblockingFunction (Thunk Builtin) m
unblockIndexValue actions value = showEntry value $ do
  forcedValue <- forceThunk value
  case forcedValue of
    VIndexLiteral {} -> return $ IfLeaf value
    VIndexParameter {} -> return $ IfLeaf value
    VIndexIf args -> unblockIf (unblockIndexValue actions) args
    VIndexAtVector args -> unblockAtVector (unblockVectorValue actions) (unblockIndexValue actions) args
    VIndexRecordAcc typ record field spine -> unblockRecordAcc actions typ record field spine
    VIndexBoundVar {} -> do
      -- There can be no bound index variables as quantifiers over indices
      -- should be normalised out.
      unexpectedExprError currentPass (prettyVerbose value)

unblockNatValue :: TypeUnblockingFunction (Thunk Builtin) m
unblockNatValue value = showEntry value $ do
  forcedValue <- forceThunk value
  case forcedValue of
    VNatLiteral {} -> return $ IfLeaf value
    VNatIf ifArgs -> unblockIf unblockNatValue ifArgs
    VNatAdd args -> unblockOp2 unblockNatValue evalAddNat args
    VNatMul args -> unblockOp2 unblockNatValue evalMulNat args
    VNatBoundVar {} -> unexpectedExprError currentPass (prettyVerbose value)
    VNatParameter {} -> unexpectedExprError currentPass (prettyVerbose value)

unblockVectorValue ::
  UnblockingActions m ->
  TypeUnblockingFunction (Thunk Builtin) m
unblockVectorValue actions value = showEntry value $ do
  forcedValue <- forceThunk value
  case forcedValue of
    VVectorLiteral {} -> return $ IfLeaf value
    VVectorIf args -> unblockIf (unblockVectorValue actions) args
    VVectorForeach args -> unblockForeachVector args
    VVectorBoundVar {} -> unexpectedExprError currentPass (prettyVerbose value)
    VVectorDataset {} -> unexpectedExprError currentPass (prettyVerbose value)
    VVectorRecordAcc typ record field spine -> unblockRecordAcc actions typ record field spine

--------------------------------------------------------------------------------
-- Unblocking individual operations

type OperationUnblockingFunction args a m =
  (MonadUnblock m) => args (Thunk Builtin) -> m (IfTree (Thunk Builtin) a)

unblockIf ::
  TypeUnblockingFunction a m ->
  OperationUnblockingFunction IfArgs a m
unblockIf unblock (IfArgs _ c x y) = do
  IfTree c <$> unblock x <*> unblock y

unblockOp2 ::
  (MonadUnblock m) =>
  TypeUnblockingFunction (Thunk Builtin) m ->
  EvalSimple ForcedValue Thunk Op2Args Builtin m ->
  OperationUnblockingFunction Op2Args (Thunk Builtin) m
unblockOp2 unblock evalFn (Op2Args x y) = do
  x' <- unblock x
  y' <- unblock y
  forIfTreeM x' $ \x'' ->
    forIfTreeM y' $ \y'' ->
      IfLeaf <$> do
        forceEval evalFn $ Op2Args x'' y''

unblockIndexOp2 ::
  (MonadUnblock m) =>
  TypeUnblockingFunction (Thunk Builtin) m ->
  EvalSimple ForcedValue Thunk IndexComparisonArgs Builtin m ->
  OperationUnblockingFunction IndexComparisonArgs (Thunk Builtin) m
unblockIndexOp2 unblock evalFn (IndexComparisonArgs n1 n2 x y) = do
  x' <- unblock x
  y' <- unblock y
  forIfTreeM x' $ \x'' ->
    forIfTreeM y' $ \y'' ->
      IfLeaf <$> do
        forceEval evalFn $ IndexComparisonArgs n1 n2 x'' y''

unblockTensorOp1 ::
  (MonadUnblock m) =>
  TypeUnblockingFunction (Thunk Builtin) m ->
  EvalSimple ForcedValue Thunk TensorOp1Args Builtin m ->
  OperationUnblockingFunction TensorOp1Args (Thunk Builtin) m
unblockTensorOp1 unblock evalFn (TensorOp1Args ds xs) = do
  xs' <- unblock xs
  forIfTreeM xs' $ \xs'' ->
    IfLeaf
      <$> forceEval evalFn (TensorOp1Args ds xs'')

unblockTensorOp2 ::
  (MonadUnblock m) =>
  TypeUnblockingFunction (Thunk Builtin) m ->
  EvalSimple ForcedValue Thunk TensorOp2Args Builtin m ->
  OperationUnblockingFunction TensorOp2Args (Thunk Builtin) m
unblockTensorOp2 unblock evalFn (TensorOp2Args ds xs ys) = do
  xs' <- unblock xs
  ys' <- unblock ys
  forIfTreeM xs' $ \xs'' ->
    forIfTreeM ys' $ \ys'' -> do
      IfLeaf
        <$> forceEval evalFn (TensorOp2Args ds xs'' ys'')

unblockReduceTensor ::
  (MonadUnblock m) =>
  TypeUnblockingFunction (Thunk Builtin) m ->
  (TensorReductionArgs (Thunk Builtin) -> m (Thunk Builtin)) ->
  OperationUnblockingFunction TensorReductionArgs (Thunk Builtin) m
unblockReduceTensor unblock evalFn (TensorReductionArgs ds xs) = do
  xs' <- unblock xs
  forIfTreeM xs' $ \xs'' ->
    IfLeaf <$> do
      evalFn $ TensorReductionArgs ds xs''

unblockAtTensor ::
  (MonadUnblock m) =>
  TypeUnblockingFunction (Thunk Builtin) m ->
  TypeUnblockingFunction (Thunk Builtin) m ->
  OperationUnblockingFunction AtTensorArgs (Thunk Builtin) m
unblockAtTensor unblockTensor unblockIndex (AtTensorArgs tElem d ds xs i) = do
  xs' <- unblockTensor xs
  i' <- unblockIndex i
  forIfTreeM xs' $ \xs'' ->
    forIfTreeM i' $ \i'' ->
      IfLeaf <$> do
        forceEval evalAtTensor $ AtTensorArgs tElem d ds xs'' i''

unblockAtVector ::
  (MonadUnblock m) =>
  TypeUnblockingFunction (Thunk Builtin) m ->
  TypeUnblockingFunction (Thunk Builtin) m ->
  OperationUnblockingFunction AtVectorArgs (Thunk Builtin) m
unblockAtVector unblockVector unblockIndex (AtVectorArgs tElem d xs i) = do
  xs' <- unblockVector xs
  i' <- unblockIndex i
  forIfTreeM xs' $ \xs'' ->
    forIfTreeM i' $ \i'' ->
      IfLeaf <$> do
        forceEval evalAtVector $ AtVectorArgs tElem d xs'' i''

unblockRecordAcc ::
  (MonadUnblock m) =>
  UnblockingActions m ->
  UnforcedType Builtin ->
  Thunk Builtin ->
  FieldName ->
  UnforcedSpine Builtin ->
  m (IfTree (Thunk Builtin) (Thunk Builtin))
unblockRecordAcc actions typ value fieldName args = do
  value' <- unblockRecordValue actions value
  forIfTreeM value' $ \value'' ->
    IfLeaf <$> do
      result <- forceRecordAcc typ value'' fieldName
      Forced <$> forceApplication (Forced result) args

unblockForeachTensor ::
  (MonadUnblock m) =>
  OperationUnblockingFunction ForeachTensorArgs (Thunk Builtin) m
unblockForeachTensor (ForeachTensorArgs tElem d ds fn) = do
  d' <- unblockNatValue d
  forIfTreeM d' $ \d'' ->
    IfLeaf <$> do
      let result = forceEval evalForeachTensor
      result $ ForeachTensorArgs tElem d'' ds fn

unblockRatTensorExtrema ::
  ComparisonOp ->
  TypeUnblockingFunction (Thunk Builtin) m ->
  OperationUnblockingFunction TensorOp2Args (Thunk Builtin) m
unblockRatTensorExtrema op unblock (TensorOp2Args ds x y) = do
  x' <- unblock x
  y' <- unblock y
  forIfTreeM x' $ \x'' ->
    forIfTreeM y' $ \y'' -> do
      let cArgs = TensorOp2Args ds x'' y''
      c <- toComparison (op, cArgs)
      return $ IfTree c (IfLeaf x'') (IfLeaf y'')

unblockMinRatTensor ::
  TypeUnblockingFunction (Thunk Builtin) m ->
  OperationUnblockingFunction TensorOp2Args (Thunk Builtin) m
unblockMinRatTensor = unblockRatTensorExtrema Le

unblockMaxRatTensor ::
  TypeUnblockingFunction (Thunk Builtin) m ->
  OperationUnblockingFunction TensorOp2Args (Thunk Builtin) m
unblockMaxRatTensor = unblockRatTensorExtrema Ge

unblockForeachVector ::
  (MonadUnblock m) =>
  OperationUnblockingFunction ForeachVectorArgs (Thunk Builtin) m
unblockForeachVector (ForeachVectorArgs tElem d fn) = do
  d' <- unblockNatValue d
  forIfTreeM d' $ \d'' ->
    IfLeaf <$> do
      forceEval evalForeachVector $ ForeachVectorArgs tElem d'' fn

--------------------------------------------------------------------------------
-- Unblocking operations

forceEval ::
  (MonadUnblock m) =>
  EvalSimple ForcedValue Thunk args Builtin m ->
  args (Thunk Builtin) ->
  m (Thunk Builtin)
forceEval evalFn args = do
  evalResult <- evalFn args
  case evalResult of
    Evaluated result -> return result
    Unevaluable {} -> developerError "Unblocking evaluation results in unevaluable result"

toComparison :: (MonadNorm Builtin m) => (ComparisonOp, TensorOp2Args (Thunk Builtin)) -> m (Thunk Builtin)
toComparison (op, TensorOp2Args dims e1 e2) = do
  forcedDims <- forceThunk dims
  return $ Forced $ case forcedDims of
    VDimsNil -> mkExpr accessCompareRatTensorPointwise (op, TensorOp2Args dims e1 e2)
    VDimsCons d ds -> mkExpr accessCompareRatTensorReduced (op, TensorReduceComparisonArgs d ds e1 e2)
    _ -> developerError "Unexpected tensorOp2Args for comparison"

currentPass :: Doc a
currentPass = "unblocking"

showEntry :: forall m. (MonadUnblock m) => Thunk Builtin -> m (IfTree (Thunk Builtin) (Thunk Builtin)) -> m (IfTree (Thunk Builtin) (Thunk Builtin))
showEntry input resultFn = do
  logDebugM MaxDetail $ do
    ctx <- getNameContext
    let doc = prettyFriendly (WithContext input ctx)
    return $ "unblock-entry:" <+> doc
  incrCallDepth

  result <- resultFn
  decrCallDepth
  logDebugM MaxDetail $ do
    ctx <- getNameContext
    -- let doc = prettyVerbose result
    let doc = prettyFriendly (WithContext result ctx)
    return $ "unblock-exit:" <+> doc

  return result
