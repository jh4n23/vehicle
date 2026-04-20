module Vehicle.Compile.TypedView.Unblock where

import Control.Monad.Except
import Vehicle.Compile.Normalise.Core (BuiltinEvaluationResult (..))
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.TypedView
import Vehicle.Compile.TypedView.Core
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
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
  { unblockRatTensorBoundVar :: Lv -> m (Expr Builtin),
    unblockNetworkApp :: Identifier -> NetworkAppArgs (Expr Builtin) -> m (Expr Builtin)
  }

-------------------------------------------------------------------------------
-- Unsupported

data IfTree a
  = IfTree (Expr Builtin) (IfTree a) (IfTree a)
  | IfLeaf a

forIfTreeM :: (Monad m) => IfTree a -> (a -> m (IfTree b)) -> m (IfTree b)
forIfTreeM tree f = case tree of
  IfLeaf v -> f v
  IfTree c t1 t2 -> IfTree c <$> forIfTreeM t1 f <*> forIfTreeM t2 f

-- | Lifts all `if`s in the provided expression `e` to the top-level, while
-- preserving the guarantee that the expression is normalised as much as
-- possible.
unblockBoolExpr ::
  (MonadUnblock m) =>
  UnblockingActions (ExceptT (Expr Builtin) m) ->
  BoundEnv Builtin ->
  Expr Builtin ->
  m (Value Builtin)
unblockBoolExpr actions env expr = do
  -- logDebug MaxDetail $ line <> "unblocking" <+> exprDoc
  -- incrCallDepth

  result <- runExceptT $ unblockBoolTensorValue actions env expr
  unblockedExpr <- case result of
    Left unblockableExpr -> do
      exprDoc <- prettyFriendlyInCtx unblockableExpr
      developerError $ "Failed to unblock expression:" <+> exprDoc
    Right value -> _

  decrCallDepth
  return unblockedExpr

--------------------------------------------------------------------------------
-- Type-based unblocking functions

type TypeUnblockingFunction compilableExpr m =
  (MonadUnblock m) => BoundEnv Builtin -> Expr Builtin -> m compilableExpr

unblockBoolTensorValue :: UnblockingActions m -> TypeUnblockingFunction CompilableBoolTensorValue m
unblockBoolTensorValue actions env expr = do
  showEntry expr
  boolValue <- toBoolTensorExpr env expr
  showExit =<< case boolValue of
    -- Already unblocked
    VCompilableBoolTensorValue result -> return result
    -- Recursively unblock
    VBoolTensorIf args -> elimIfTree <$> unblockIf unblock env args
    VBoolTensorReduceAnd args -> elimIfTree <$> unblockReduceTensor unblock evalReduceAndTensor env args
    VBoolTensorReduceOr args -> elimIfTree <$> unblockReduceTensor unblock evalReduceOrTensor env args
    VBoolTensorCompareIndex (op, args) -> elimIfTree <$> unblockIndexOp2 unblock op env args
    VBoolTensorCompareRatPointwise (op, args) -> _ unblockRatTensorValue
    VBoolTensorCompareNat (op, args) -> elimIfTree <$> unblockOp2 unblockNatValue unblock (evalCompareNat op) env args
    VBoolTensorAt args -> elimIfTree <$> unblockAtTensor unblock env args
    VBoolTensorForeach args -> elimIfTree <$> unblockForeachTensor unblock env args
  where
    unblock env' e = IfLeaf <$> unblockBoolTensorValue actions env' e

unblockRatTensorValue :: (MonadUnblock m) => UnblockingActions m -> TypeUnblockingFunction (IfTree CompilableRatTensorValue) m
unblockRatTensorValue actions@UnblockingActions {..} env expr = do
  showEntry expr
  ratTensorExpr <- toRatTensorValue env expr
  showExit =<< case ratTensorExpr of
    -- Rational operators
    VCompilableRatTensorValue result -> return $ IfLeaf result
    -- Recursively purify
    VIfRatTensor args -> unblockIf unblock env args
    VMinRatTensor args -> unblockMinRatTensor env args
    VMaxRatTensor args -> unblockMaxRatTensor env args
    VNegRatTensor args -> unblockTensorOp1 unblock evalNegRatTensor env args
    VAddRatTensor args -> unblockTensorOp2 unblock evalAddRatTensor env args
    VSubRatTensor args -> unblockTensorOp2 unblock evalSubRatTensor env args
    VMulRatTensor args -> unblockTensorOp2 unblock evalMulRatTensor env args
    VDivRatTensor args -> unblockTensorOp2 unblock evalDivRatTensor env args
    VReduceAddRatTensor args -> unblockReduceTensor unblock evalReduceAddRatTensor env args
    VReduceMulRatTensor args -> unblockReduceTensor unblock evalReduceMulRatTensor env args
    VReduceMinRatTensor args -> unblockReduceTensor unblock evalReduceMinRatTensor env args
    VReduceMaxRatTensor args -> unblockReduceTensor unblock evalReduceMaxRatTensor env args
    VRatTensorBoundVar v -> unblock env =<< unblockRatTensorBoundVar v
    VNetworkApplication n args -> unblock env =<< unblockNetworkApp n args
    VRatAt args -> unblockAtTensor unblock env args
    VRatForeach args -> unblockForeachTensor unblock env args
    VParameterOrDataset _ -> _
  where
    unblock = unblockRatTensorValue actions

unblockIndexValue :: TypeUnblockingFunction (IfTree CompilableIndexValue) m
unblockIndexValue env expr = do
  indexExpr <- toIndexValue env expr
  case indexExpr of
    VCompilableIndexValue result -> return $ IfLeaf result
    VIndexIf args -> unblockIf unblock env args
    VIndexBoundVar {} -> unexpectedExprError currentPass (prettyVerbose expr)
  where
    unblock = unblockIndexValue

unblockNatValue :: TypeUnblockingFunction (IfTree CompilableNatExpr) m
unblockNatValue env expr = do
  natExpr <- toNatValue env expr
  case natExpr of
    VCompilableNat result -> return $ IfLeaf result
    VNatIf args -> unblockIf unblock env args
    VNatAdd args -> unblockOp2 unblock unblock evalAddNat env args
    VNatMul args -> unblockOp2 unblock unblock evalMulNat env args
    VNatBoundVar {} -> unexpectedExprError currentPass (prettyVerbose expr)
    VNatParameter {} -> unexpectedExprError currentPass (prettyVerbose expr)
  where
    unblock = unblockNatValue

--------------------------------------------------------------------------------
-- Operation-based unblocking functions

type OperationUnblockingFunction args a m =
  (MonadUnblock m) => BoundEnv Builtin -> args (Expr Builtin) -> m (IfTree a)

unblockIf ::
  TypeUnblockingFunction (IfTree a) m ->
  OperationUnblockingFunction IfArgs a m
unblockIf unblock env (IfArgs _ c x y) =
  IfTree c <$> unblock env x <*> unblock env y

unblockMinRatTensor ::
  OperationUnblockingFunction TensorOp2Args CompilableRatTensorValue m
unblockMinRatTensor = _

unblockMaxRatTensor ::
  OperationUnblockingFunction TensorOp2Args CompilableRatTensorValue m
unblockMaxRatTensor = _

unblockOp2 ::
  TypeUnblockingFunction (IfTree inputCompilableExpr) m ->
  TypeUnblockingFunction (IfTree outputCompilableExpr) m ->
  BuiltinEvaluation Op2Args Builtin m ->
  OperationUnblockingFunction Op2Args outputCompilableExpr m
unblockOp2 unblockArg unblockResult evalOp env (Op2Args x y) = do
  x' <- unblockArg env x
  y' <- unblockArg env y
  forIfTreeM x' $ \x'' ->
    forIfTreeM y' $ \y'' ->
      unblockResult env =<< do
        forceEvaluation evalOp $
          Op2Args (_ x'') (_ y'')

unblockIndexOp2 ::
  TypeUnblockingFunction (IfTree CompilableBoolTensorValue) m ->
  ComparisonOp ->
  OperationUnblockingFunction IndexComparisonArgs CompilableBoolTensorValue m
unblockIndexOp2 unblock op env (IndexCompArgs n1 n2 x y) = do
  x' <- unblockIndexValue env x
  y' <- unblockIndexValue env y
  forIfTreeM x' $ \x'' ->
    forIfTreeM y' $ \y'' ->
      unblock env =<< do
        forceEvaluation (evalCompareIndex op) $
          IndexCompArgs n1 n2 (_ x'') (_ y'')

unblockTensorOp1 ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  BuiltinEvaluation TensorOp1Args Builtin m ->
  OperationUnblockingFunction TensorOp1Args compilableExpr m
unblockTensorOp1 unblock evalOp1 env (TensorOp1Args ds xs) = do
  xs' <- unblock env xs
  forIfTreeM xs' $ \xs'' ->
    unblock env =<< do
      forceEvaluation evalOp1 $ TensorOp1Args ds (_ xs'')

unblockTensorOp2 ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  BuiltinEvaluation TensorOp2Args Builtin m ->
  OperationUnblockingFunction TensorOp2Args compilableExpr m
unblockTensorOp2 unblock evalOp2 env (TensorOp2Args ds xs ys) = do
  xs' <- unblock env xs
  ys' <- unblock env ys
  forIfTreeM xs' $ \xs'' ->
    forIfTreeM ys' $ \ys'' ->
      unblock env =<< do
        forceEvaluation evalOp2 $ TensorOp2Args ds (_ xs'') (_ ys'')

unblockReduceTensor ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  BuiltinEvaluation TensorReductionArgs Builtin m ->
  OperationUnblockingFunction TensorReductionArgs compilableExpr m
unblockReduceTensor unblock evalReductionOp env (TensorReductionArgs ds e xs) = do
  xs' <- unblock env xs
  forIfTreeM xs' $ \xs'' ->
    unblock env =<< do
      forceEvaluation evalReductionOp $ TensorReductionArgs ds e (_ xs'')

unblockAtTensor ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  OperationUnblockingFunction AtTensorArgs compilableExpr m
unblockAtTensor unblock env (AtTensorArgs tElem d ds xs i) = do
  xs' <- unblock env xs
  i' <- unblockIndexValue env i
  forIfTreeM xs' $ \xs'' ->
    forIfTreeM i' $ \i'' ->
      unblock env =<< do
        forceEvaluation evalAtTensor $ AtTensorArgs tElem d ds (_ xs'') (_ i'')

unblockForeachTensor ::
  TypeUnblockingFunction (IfTree compilableExpr) m ->
  OperationUnblockingFunction ForeachTensorArgs compilableExpr m
unblockForeachTensor unblock env (ForeachTensorArgs tElem d ds fn) = do
  d' <- unblockNatValue env d
  forIfTreeM d' $ \d'' ->
    unblock env =<< do
      forceEvaluation evalForeachTensor $ ForeachTensorArgs tElem (_ d'') ds fn

--------------------------------------------------------------------------------
-- Other functions

forceEvaluation ::
  (MonadUnblock m) =>
  BuiltinEvaluation args Builtin m ->
  args (Expr Builtin) ->
  m (Expr Builtin)
forceEvaluation evalFn args = do
  evalResult <- evalFn args
  case evalResult of
    Evaluated result -> result
    Unevaluated {} -> _

elimIfTree :: IfTree CompilableBoolTensorValue -> CompilableBoolTensorValue
elimIfTree = _

--------------------------------------------------------------------------------
-- Utilities

currentPass :: Doc a
currentPass = "unblocking"

showEntry :: forall m. (MonadUnblock m) => Expr Builtin -> m ()
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
