module Vehicle.Compile.TypedView.Unblock where

import Control.Monad.Except
import Vehicle.Compile.Normalise.Core (BuiltinEvaluationResult (..), RecordExpr (..))
import Vehicle.Compile.Normalise.NBE (forceThunk)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.TypedView.Core
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (Tensor)
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context (MonadFreeContext)

--------------------------------------------------------------------------------
-- Public interface
--------------------------------------------------------------------------------

type MonadUnblock m =
  ( MonadLogger m,
    MonadFreeContext Builtin m,
    MonadReadableNameContext m,
    MonadError (Expr Builtin) m
  )

data UnblockingActions m = UnblockingActions
  { unblockRatTensorBoundVar :: Lv -> m (Value Builtin),
    unblockNetworkApp :: Identifier -> NetworkAppArgs (Thunk Builtin) -> m (Value Builtin)
  }

-------------------------------------------------------------------------------
-- Unsupported

data IfTree a
  = IfTree (Thunk Builtin) (IfTree a) (IfTree a)
  | IfLeaf a

forIfTreeM :: (Monad m) => IfTree a -> (a -> m (IfTree b)) -> m (IfTree b)
forIfTreeM tree f = case tree of
  IfLeaf v -> f v
  IfTree c t1 t2 -> IfTree c <$> forIfTreeM t1 f <*> forIfTreeM t2 f

-- | A view on all possible expressions that can have type `Tensor Bool ds`
-- and that we know how to compile to constraints.
data CompilableBoolTensorExpr
  = CBoolTensorLiteral (Tensor Bool)
  | CBoolStackTensor (StackTensorArgs (Thunk Builtin))
  | CBoolConstTensor (ConstTensorArgs (Thunk Builtin))
  | CBoolTensorAnd (TensorOp2Args (Thunk Builtin))
  | CBoolTensorOr (TensorOp2Args (Thunk Builtin))
  | CBoolTensorCompareRat (ComparisonOp, TensorComparisonArgs (Thunk Builtin))
  | CBoolTensorQuantifyRat (Quantifier, QuantifyRatTensorArgs (Thunk Builtin))
  | CBoolTensorNot (TensorOp1Args (Thunk Builtin))

-- | A view on all possible compilable expressions that can have type `Tensor Rat`.
data CompilableRatTensorValue
  = CRatTensorLiteral (Tensor Rational)
  | CRatConstTensor (ConstTensorArgs (Thunk Builtin))
  | CRatStackTensor (StackTensorArgs (Thunk Builtin))

-- | Lifts all `if`s in the provided expression `e` to the top-level, while
-- preserving the guarantee that the expression is normalised as much as
-- possible.
forceCompilableBoolExpr ::
  (MonadUnblock m) =>
  UnblockingActions (ExceptT (Expr Builtin) m) ->
  Thunk Builtin ->
  m CompilableBoolTensorExpr
forceCompilableBoolExpr actions thunk = do
  exprDoc <- prettyFriendlyInCtx thunk
  logCompilerSection MaxDetail ("unblocking" <+> exprDoc) $ do
    result <- runExceptT $ unblockBoolTensorValue actions thunk
    case result of
      Left unblockableExpr -> do
        unblockableExprDoc <- prettyFriendlyInCtx unblockableExpr
        developerError $ "Failed to unblock expression:" <+> unblockableExprDoc
      Right value -> return value

--------------------------------------------------------------------------------
-- Type-based unblocking functions

type TypeUnblockingFunction compilableExpr m =
  (MonadUnblock m) => Thunk Builtin -> m compilableExpr

unblockBoolTensorValue :: UnblockingActions m -> TypeUnblockingFunction CompilableBoolTensorExpr m
unblockBoolTensorValue actions thunk = do
  showEntry thunk
  boolValue <- forceBoolTensorExpr thunk
  showExit =<< case boolValue of
    -- Already unblocked
    VBoolTensorLiteral args -> return $ CBoolTensorLiteral args
    VBoolStackTensor args -> return $ CBoolStackTensor args
    VBoolConstTensor args -> return $ CBoolConstTensor args
    VBoolTensorAnd args -> return $ CBoolTensorAnd args
    VBoolTensorOr args -> return $ CBoolTensorOr args
    VBoolTensorCompareRat args -> return $ CBoolTensorCompareRat args
    VBoolTensorQuantifyRat args -> return $ CBoolTensorQuantifyRat args
    VBoolTensorNot args -> return $ CBoolTensorNot args
    -- Recursively unblock
    VBoolTensorIf args -> elimIfTree <$> unblockIf unblock args
    VBoolTensorReduceAnd args -> elimIfTree <$> unblockReduceTensor unblock evalReduceAndTensor args
    VBoolTensorReduceOr args -> elimIfTree <$> unblockReduceTensor unblock evalReduceOrTensor args
    VBoolTensorCompareIndex (op, args) -> elimIfTree <$> unblockIndexOp2 unblock op args
    VBoolTensorCompareNat (op, args) -> elimIfTree <$> unblockOp2 unblockNatValue unblock (evalCompareNat op) args
    VBoolTensorAt args -> elimIfTree <$> unblockAtTensor unblock args
    VBoolTensorForeach args -> elimIfTree <$> unblockForeachTensor unblock args
  where
    unblock e = IfLeaf <$> unblockBoolTensorValue actions e

unblockRatTensorValue :: (MonadUnblock m) => UnblockingActions m -> TypeUnblockingFunction (IfTree CompilableRatTensorValue) m
unblockRatTensorValue actions@UnblockingActions {..} expr = do
  showEntry expr
  ratTensorExpr <- forceRatTensorExpr expr
  showExit =<< case ratTensorExpr of
    -- Rational operators
    VRatTensorLiteral args -> return $ IfLeaf $ CRatTensorLiteral args
    VRatConstTensor args -> return $ IfLeaf $ CRatConstTensor args
    VRatStackTensor args -> return $ IfLeaf $ CRatStackTensor args
    -- Recursively purify
    VIfRatTensor args -> unblockIf unblock args
    VMinRatTensor args -> unblockMinRatTensor unblock args
    VMaxRatTensor args -> unblockMaxRatTensor unblock args
    VNegRatTensor args -> unblockTensorOp1 unblock evalNegRatTensor args
    VAddRatTensor args -> unblockTensorOp2 unblock evalAddRatTensor args
    VSubRatTensor args -> unblockTensorOp2 unblock evalSubRatTensor args
    VMulRatTensor args -> unblockTensorOp2 unblock evalMulRatTensor args
    VDivRatTensor args -> unblockTensorOp2 unblock evalDivRatTensor args
    VReduceAddRatTensor args -> unblockReduceTensor unblock evalReduceAddRatTensor args
    VReduceMulRatTensor args -> unblockReduceTensor unblock evalReduceMulRatTensor args
    VReduceMinRatTensor args -> unblockReduceTensor unblock evalReduceMinRatTensor args
    VReduceMaxRatTensor args -> unblockReduceTensor unblock evalReduceMaxRatTensor args
    VRatTensorBoundVar v -> unblock . Forced =<< unblockRatTensorBoundVar v
    VNetworkApplication n args -> unblock . Forced =<< unblockNetworkApp n args
    VRatAt args -> unblockAtTensor unblock args
    VRatForeach args -> unblockForeachTensor unblock args
    VRatTensorRecordAcc typ record fields args -> _
    VParameterOrDataset _ -> unexpectedExprError _ _ _
  where
    unblock = unblockRatTensorValue actions

unblockIndexValue :: TypeUnblockingFunction (IfTree Int) m
unblockIndexValue expr = do
  indexExpr <- forceIndexExpr expr
  case indexExpr of
    VIndexLiteral result -> return $ IfLeaf result
    VIndexIf args -> unblockIf unblock args
    VIndexRecordAcc typ _ _ _ -> _
    VIndexBoundVar {} -> unexpectedExprError currentPass (prettyVerbose expr)
  where
    unblock = unblockIndexValue

unblockNatValue :: TypeUnblockingFunction (IfTree Int) m
unblockNatValue expr = do
  natExpr <- forceNatExpr expr
  case natExpr of
    VNatLiteral result -> return $ IfLeaf result
    VNatIf args -> unblockIf unblock args
    VNatAdd args -> unblockOp2 unblock unblock evalAddNat args
    VNatMul args -> unblockOp2 unblock unblock evalMulNat args
    VNatBoundVar {} -> unexpectedExprError currentPass (prettyVerbose expr)
    VNatParameter {} -> unexpectedExprError currentPass (prettyVerbose expr)
  where
    unblock = unblockNatValue

unblockRecordValue :: TypeUnblockingFunction (IfTree (RecordFields Builtin)) m
unblockRecordValue expr = do
  recordExpr <- forceThunk expr
  case recordExpr of
    VRecordRecord typ fields -> _
    VRecordFreeVar ident spine -> _
    VRecordMeta m spine -> _
    VRecordBuiltin b spine -> _
    VRecordBoundVar lv spine -> _
    VRecordRecordAcc typ record spine args -> _

--------------------------------------------------------------------------------
-- Operation-based unblocking functions

type OperationUnblockingFunction args a m =
  (MonadUnblock m) => args (Thunk Builtin) -> m (IfTree a)

unblockIf ::
  TypeUnblockingFunction (IfTree a) m ->
  OperationUnblockingFunction IfArgs a m
unblockIf unblock (IfArgs _ c x y) =
  IfTree c <$> unblock x <*> unblock y

unblockRatTensorExtrema ::
  ComparisonOp ->
  TypeUnblockingFunction (IfTree inputCompilableExpr) m ->
  OperationUnblockingFunction TensorOp2Args inputCompilableExpr m
unblockRatTensorExtrema op unblock (TensorOp2Args ds x y) = do
  x' <- unblock x
  y' <- unblock y
  let comparisonArgs = TensorComparisonArgs _ ds x' y'
  let comparison = mkExpr accessCompareRatTensor (op, comparisonArgs)
  return $ IfTree comparison x' y'

unblockMinRatTensor ::
  TypeUnblockingFunction (IfTree inputCompilableExpr) m ->
  OperationUnblockingFunction TensorOp2Args inputCompilableExpr m
unblockMinRatTensor = unblockRatTensorExtrema Le

unblockMaxRatTensor ::
  TypeUnblockingFunction (IfTree inputCompilableExpr) m ->
  OperationUnblockingFunction TensorOp2Args inputCompilableExpr m
unblockMaxRatTensor = unblockRatTensorExtrema Ge

unblockOp2 ::
  TypeUnblockingFunction (IfTree inputCompilableExpr) m ->
  TypeUnblockingFunction (IfTree outputCompilableExpr) m ->
  BuiltinEvaluation Op2Args Builtin m ->
  OperationUnblockingFunction Op2Args outputCompilableExpr m
unblockOp2 unblockArg unblockResult evalOp (Op2Args x y) = do
  x' <- unblockArg x
  y' <- unblockArg y
  forIfTreeM x' $ \x'' ->
    forIfTreeM y' $ \y'' ->
      unblockResult =<< do
        forceEvaluation evalOp $
          Op2Args (_ x'') (_ y'')

unblockIndexOp2 ::
  TypeUnblockingFunction (IfTree CompilableBoolTensorExpr) m ->
  ComparisonOp ->
  OperationUnblockingFunction IndexComparisonArgs CompilableBoolTensorExpr m
unblockIndexOp2 unblock op (IndexCompArgs n1 n2 x y) = do
  x' <- unblockIndexValue x
  y' <- unblockIndexValue y
  forIfTreeM x' $ \x'' ->
    forIfTreeM y' $ \y'' ->
      unblock =<< do
        forceEvaluation (evalCompareIndex op) $
          IndexCompArgs n1 n2 x'' y''

unblockTensorOp1 ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  BuiltinEvaluation TensorOp1Args Builtin m ->
  OperationUnblockingFunction TensorOp1Args compilableExpr m
unblockTensorOp1 unblock evalOp1 (TensorOp1Args ds xs) = do
  xs' <- unblock xs
  forIfTreeM xs' $ \xs'' ->
    unblock =<< do
      forceEvaluation evalOp1 $ TensorOp1Args ds (_ xs'')

unblockTensorOp2 ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  BuiltinEvaluation TensorOp2Args Builtin m ->
  OperationUnblockingFunction TensorOp2Args compilableExpr m
unblockTensorOp2 unblock evalOp2 (TensorOp2Args ds xs ys) = do
  xs' <- unblock xs
  ys' <- unblock ys
  forIfTreeM xs' $ \xs'' ->
    forIfTreeM ys' $ \ys'' ->
      unblock =<< do
        forceEvaluation evalOp2 $ TensorOp2Args ds (_ xs'') (_ ys'')

unblockReduceTensor ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  BuiltinEvaluation TensorReductionArgs Builtin m ->
  OperationUnblockingFunction TensorReductionArgs compilableExpr m
unblockReduceTensor unblock evalReductionOp (TensorReductionArgs ds e xs) = do
  xs' <- unblock xs
  forIfTreeM xs' $ \xs'' ->
    unblock =<< do
      forceEvaluation evalReductionOp $ TensorReductionArgs ds e (_ xs'')

unblockAtTensor ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  OperationUnblockingFunction AtTensorArgs compilableExpr m
unblockAtTensor unblock (AtTensorArgs tElem d ds xs i) = do
  xs' <- unblock xs
  i' <- unblockIndexValue i
  forIfTreeM xs' $ \xs'' ->
    forIfTreeM i' $ \i'' ->
      unblock =<< do
        forceEvaluation evalAtTensor $ AtTensorArgs tElem d ds (_ xs'') (_ i'')

unblockForeachTensor ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  OperationUnblockingFunction ForeachTensorArgs compilableExpr m
unblockForeachTensor unblock (ForeachTensorArgs tElem d ds fn) = do
  d' <- unblockNatValue d
  forIfTreeM d' $ \d'' ->
    unblock =<< do
      forceEvaluation evalForeachTensor $ ForeachTensorArgs tElem (_ d'') ds fn

--------------------------------------------------------------------------------
-- Other functions

forceEvaluation ::
  (MonadUnblock m) =>
  BuiltinEvaluation args Builtin m ->
  args (expr Builtin) ->
  m (Thunk Builtin)
forceEvaluation evalFn args = do
  evalResult <- evalFn _
  case evalResult of
    Evaluated result -> return $ Evaluated result
    Unevaluated {} -> _

elimIfTree :: IfTree CompilableBoolTensorExpr -> CompilableBoolTensorExpr
elimIfTree = _

--------------------------------------------------------------------------------
-- Utilities

currentPass :: Doc a
currentPass = "unblocking"

showEntry :: forall m. (MonadUnblock m) => Thunk Builtin -> m ()
showEntry e = do
  ctx <- getNameContext
  -- logDebug MaxDetail $ "unblock-entry" <+> prettyVerbose e
  logDebug MaxDetail $ "unblock-entry:" <+> prettyFriendly (WithContext e ctx)
  incrCallDepth

showExit :: (MonadUnblock m) => a -> m a
showExit e = do
  ctx <- getNameContext
  decrCallDepth
  -- logDebug MaxDetail $ "unblock-exit " <+> prettyVerbose e
  logDebug MaxDetail $ "unblock-exit:" <+> prettyFriendly (WithContext e ctx)
  return e
