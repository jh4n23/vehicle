module Vehicle.Compile.TypedView.Purification
  ( RatTensorExpr (..),
    purifyAssertion,
  )
where

import Control.Monad.Except
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.TypedView.Core
import Vehicle.Compile.TypedView.Unblock
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (RatTensor)
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context (MonadFreeContext)

--------------------------------------------------------------------------------
-- Purification

type MonadPurify m =
  ( MonadLogger m,
    MonadFreeContext Builtin m,
    MonadReadableNameContext m,
    MonadError (Expr Builtin) m
  )

data ConstraintExpr
  = ERatTensorLiteral RatTensor
  | ENegRatTensor ConstraintExpr
  | EAddRatTensor ConstraintExpr ConstraintExpr
  | ESubRatTensor ConstraintExpr ConstraintExpr
  | EMulRatTensor ConstraintExpr ConstraintExpr
  | EDivRatTensor ConstraintExpr ConstraintExpr
  | ERatTensorBoundVar Lv

purifyAssertion ::
  (MonadPurify m) =>
  UnblockingActions m ->
  BoundEnv Builtin ->
  ComparisonOp ->
  TensorOp2Args (Expr Builtin) ->
  m (IfTree (TensorOp2Args ConstraintExpr))
purifyAssertion actions env op args@(TensorOp2Args _ e1 e2) = do
  let purifyFn = purifyRatTensorExpr actions 0 _
  pe1 <- purifyFn e1
  pe2 <- purifyFn e2
  _ <- unblockTensorOp2 (purifyRatTensorExpr actions 0) _ env args

  return unblockedExpr

{-
data Impurity
  = LiftedIf (IfArgs (Value Builtin))
  | LiftedMinMax (Bool, TensorOp2Args (Value Builtin)) ComparisonOp (Value Builtin)
  | ReducedComparison (Value Builtin)

findImpurity :: Value Builtin -> Either Impurity (TensorOp2Args (Value Builtin))
findImpurity expr = do
  forcedValue <- forceValue expr
  case toBoolValue forcedValue of
    -- VBoolIf args -> Left $ LiftedIf args
    -- VCompareRatTensor (op, args) -> maybe (Right args) Left $ findMinMaxImpurity op args
    _ -> Left $ ReducedComparison expr
  where
    findMinMaxImpurity :: ComparisonOp -> TensorOp2Args (Value Builtin) -> Maybe Impurity
    findMinMaxImpurity op (TensorOp2Args _ e1 e2) = case (toRatTensorValue e1, toRatTensorValue e2) of
      (VMinRatTensor args, _) -> Just $ LiftedMinMax (True, args) op e2
      (_, VMinRatTensor args) -> Just $ LiftedMinMax (True, args) (flipOrder op) e1
      (VMaxRatTensor args, _) -> Just $ LiftedMinMax (False, args) op e2
      (_, VMaxRatTensor args) -> Just $ LiftedMinMax (False, args) (flipOrder op) e1
      _ -> Nothing

eliminateImpurities :: (MonadPurify m) => Impurity -> m (Value Builtin)
eliminateImpurities impurity = do
  case impurity of
    LiftedIf args -> unfoldIf args
    LiftedMinMax (isMin, TensorOp2Args dims e1 e2) op value -> do
      let comparison1 = fromBoolValue $ VCompareRatTensor (op, TensorOp2Args dims e1 value)
      let comparison2 = fromBoolValue $ VCompareRatTensor (op, TensorOp2Args dims e2 value)
      let logicalArgs = TensorOp2Args dims comparison1 comparison2

      let builtinOp
            | op == Le || op == Lt = (if isMin then accessOrTensorBuiltin else accessAndTensorBuiltin)
            | op == Ge || op == Gt = (if isMin then accessAndTensorBuiltin else accessOrTensorBuiltin)
            | otherwise = developerError $ "Support for min/max with" <+> pretty op <+> "not yet implemented"

      return $ unforcedBuiltinApp builtinOp logicalArgs
    ReducedComparison expr -> return expr
-}

-- | The number of dimensions above the dimensions of the expression that we're currently trying to compile.
type IncreasedDimensions = Int

purifyRatTensorExpr ::
  (MonadPurify m) =>
  UnblockingActions m ->
  IncreasedDimensions ->
  BoundEnv Builtin ->
  Expr Builtin ->
  m (IfTree ConstraintExpr)
purifyRatTensorExpr actions@UnblockingActions {..} incrDims env expr = do
  showPurifyEntry expr
  ratTensorExpr <- forceRatTensorExpr env expr
  showPurifyExit =<< case ratTensorExpr of
    -- Pure operations
    VCompilableRatTensorValue result -> case result of
      VRatTensorLiteral t -> return $ IfLeaf $ ERatTensorLiteral t
      VRatConstTensor {} -> _
      VRatStackTensor {} -> _
    VNegRatTensor args -> purifyTensorOp1 (recPurify incrDims) ENegRatTensor env args
    VAddRatTensor args -> purifyTensorOp2 (recPurify incrDims) EAddRatTensor env args
    VSubRatTensor args -> purifyTensorOp2 (recPurify incrDims) ESubRatTensor env args
    VMulRatTensor args -> purifyTensorOp2 (recPurify incrDims) EMulRatTensor env args
    VDivRatTensor args -> purifyTensorOp2 (recPurify incrDims) EDivRatTensor env args
    -- Recursively purify
    VIfRatTensor args -> unblockIf (recPurify incrDims) env args
    VMinRatTensor args -> unblockMinRatTensor env args
    VMaxRatTensor args -> unblockMaxRatTensor env args
    VReduceAddRatTensor args -> unblockReduceTensor (recPurify (incrDims + 1)) evalReduceAddRatTensor env args
    VReduceMulRatTensor args -> unblockReduceTensor (recPurify (incrDims + 1)) evalReduceMulRatTensor env args
    VReduceMinRatTensor args -> unblockReduceTensor (recPurify (incrDims + 1)) evalReduceMinRatTensor env args
    VReduceMaxRatTensor args -> unblockReduceTensor (recPurify (incrDims + 1)) evalReduceMaxRatTensor env args
    VRatAt args -> unblockAtTensor (recPurify (incrDims + 1)) env args
    VRatForeach args -> unblockForeachTensor (recPurify (incrDims - 1)) env args
    VRatTensorBoundVar v
      | incrDims == 0 -> return $ IfLeaf $ ERatTensorBoundVar v
      | otherwise -> recPurify incrDims env =<< unblockRatTensorBoundVar v
    VNetworkApplication n args -> recPurify incrDims env =<< unblockNetworkApp n args
    VParameterOrDataset _ -> _
    VRatTensorRecordAcc {} -> _
  where
    recPurify = purifyRatTensorExpr actions

purifyTensorOp1 ::
  TypeUnblockingFunction (IfTree ConstraintExpr) m ->
  (ConstraintExpr -> ConstraintExpr) ->
  OperationUnblockingFunction TensorOp1Args ConstraintExpr m
purifyTensorOp1 unblock evalOp1 env (TensorOp1Args _ds xs) = do
  xs' <- unblock env xs
  forIfTreeM xs' $ \xs'' -> do
    return $ IfLeaf $ evalOp1 xs''

purifyTensorOp2 ::
  TypeUnblockingFunction (IfTree ConstraintExpr) m ->
  (ConstraintExpr -> ConstraintExpr -> ConstraintExpr) ->
  OperationUnblockingFunction TensorOp2Args ConstraintExpr m
purifyTensorOp2 unblock evalOp2 env (TensorOp2Args _ds xs ys) = do
  xs' <- unblock env xs
  ys' <- unblock env ys
  forIfTreeM xs' $ \xs'' ->
    forIfTreeM ys' $ \ys'' ->
      return $ IfLeaf $ evalOp2 xs'' ys''

--------------------------------------------------------------------------------
-- Utilities

showPurifyEntry :: forall m. (MonadPurify m) => Expr Builtin -> m ()
showPurifyEntry e = do
  ctx <- getNameContext
  -- logDebug MaxDetail $ "purify-entry" <+> prettyVerbose e
  logDebug MaxDetail $ "purify-entry:" <+> prettyFriendly (WithContext e ctx)
  incrCallDepth

showPurifyExit :: (MonadPurify m) => a -> m a
showPurifyExit e = do
  ctx <- getNameContext
  decrCallDepth
  -- logDebug MaxDetail $ "purify-exit " <+> prettyVerbose e
  logDebug MaxDetail $ "purify-exit:" <+> prettyFriendly (WithContext e ctx)
  return e
