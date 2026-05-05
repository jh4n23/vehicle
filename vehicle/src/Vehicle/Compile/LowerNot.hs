module Vehicle.Compile.LowerNot
  ( lowerNot,
    negateQuantifierBody,
  )
where

import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Compile.TypedView
import Vehicle.Compile.TypedView.Core (BoolTensorExpr (..))
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Normalise (unforcedBuiltinApp)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (mapTensor)
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context (MonadFreeContext)

--------------------------------------------------------------------------------
-- Not elimination

type MonadDropNot m =
  ( MonadLogger m,
    MonadReadableNameContext m,
    MonadFreeContext Builtin m
  )

-- | Tries to push in a `Not` as far as possible into a boolean expression.
-- If it is not possible to push it all the way through, it calls the continuation.
lowerNot ::
  forall m.
  (MonadDropNot m) =>
  TensorOp1Args (Expr Builtin) ->
  m (Expr Builtin)
lowerNot (TensorOp1Args dims value) = do
  boolTensorExpr <- toBoolTensorValue _ value
  result <- case boolTensorExpr of
    ----------------
    -- Base cases --
    ----------------
    VBoolTensorLiteral b -> return $ fromBoolTensorValue $ VBoolTensorLiteral (mapTensor not b)
    VBoolTensorNot args -> return $ tensorOp1Arg args
    VBoolTensorCompareIndex (op, args) -> return $ fromBoolTensorValue $ VBoolTensorCompareIndex (neg op, args)
    VBoolTensorCompareNat (op, args) -> return $ fromBoolTensorValue $ VBoolTensorCompareNat (neg op, args)
    VBoolTensorCompareRat (op, args) -> return $ fromBoolTensorValue $ VBoolTensorCompareRat (neg op, args)
    -- We can't actually lower the `not` through the body of the quantifier as
    -- it is not yet unnormalised. However, it's fine to stop here as we'll
    -- simply continue to normalise it once we re-encounter it again after
    -- normalising the quantifier.
    VBoolTensorQuantifyRat (q, args) -> fromBoolValue . VQuantifyRatTensor . (neg q,) <$> negateQuantifierBody args
    ---------------------
    -- Inductive cases --
    ---------------------
    VBoolConstTensor args -> return $ fromBoolTensorValue $ VBoolConstTensor $ negateConstTensorArgs args
    VBoolStackTensor args -> return $ fromBoolTensorValue $ VBoolStackTensor $ negateStackTensorArgs args
    VBoolTensorOr args -> return $ fromBoolTensorValue $ VBoolTensorAnd $ negateOp2Args args
    VBoolTensorAnd args -> return $ fromBoolTensorValue $ VBoolTensorOr $ negateOp2Args args
    VBoolTensorIf args -> return $ fromBoolTensorValue $ VBoolTensorBoolIf $ negateIfArgs dims args
    VBoolTensorReduceOr args -> return $ fromBoolTensorValue $ VBoolTensorReduceAnd $ negateReductionArgs args
    VBoolTensorReduceAnd args -> return $ fromBoolTensorValue $ VBoolTensorReduceOr $ negateReductionArgs args
    VBoolTensorAt args -> return $ fromBoolTensorValue $ VBoolTensorAt $ negateAtTensorArgs args
    VBoolTensorForeach args -> fromBoolTensorValue . VBoolTensorForeach <$> negateForeachArgs args

  logDebugM MaxDetail $ do
    ctx <- getNameContext
    return $ "push-not:" <+> prettyFriendly (WithContext result ctx)

  return result

negateThunk :: Thunk Builtin -> Thunk Builtin -> Thunk Builtin
negateThunk dims v =
  unforcedBuiltinApp accessNotTensorBuiltin $
    TensorOp1Args
      { tensorOp1Dims = dims,
        tensorOp1Arg = v
      }

negateOp2Args :: TensorOp2Args (Thunk Builtin) -> TensorOp2Args (Thunk Builtin)
negateOp2Args TensorOp2Args {..} =
  TensorOp2Args
    { tensorOp2Dims = tensorOp2Dims,
      tensorOp2Arg1 = negateThunk tensorOp2Dims tensorOp2Arg1,
      tensorOp2Arg2 = negateThunk tensorOp2Dims tensorOp2Arg2
    }

negateReductionArgs :: TensorReductionArgs (Thunk Builtin) -> TensorReductionArgs (Thunk Builtin)
negateReductionArgs TensorReductionArgs {..} =
  TensorReductionArgs
    { tensorReductionDims = tensorReductionDims,
      tensorReductionUnit = negateThunk (Forced $ INil $ Forced INatType) tensorReductionUnit,
      tensorReductionTensor = negateThunk tensorReductionDims tensorReductionTensor
    }

negateIfArgs :: VDims Builtin -> IfArgs (Thunk Builtin) -> IfArgs (Thunk Builtin)
negateIfArgs dims IfArgs {..} =
  IfArgs
    { ifType = ifType,
      ifCond = ifCond,
      ifArg1 = negateThunk dims ifArg1,
      ifArg2 = negateThunk dims ifArg2
    }

negateConstTensorArgs :: ConstTensorArgs (Thunk Builtin) -> ConstTensorArgs (Thunk Builtin)
negateConstTensorArgs ConstTensorArgs {..} =
  ConstTensorArgs
    { constType = constType,
      constValue = negateThunk (Forced $ INil $ Forced INatType) constValue,
      constDims = constDims
    }

negateStackTensorArgs :: StackTensorArgs (Thunk Builtin) -> StackTensorArgs (Thunk Builtin)
negateStackTensorArgs StackTensorArgs {..} =
  StackTensorArgs
    { stackType = stackType,
      stackFirstDim = stackFirstDim,
      stackRemainingDims = stackRemainingDims,
      stackElements = fmap (negateThunk stackRemainingDims) stackElements
    }

negateAtTensorArgs :: AtTensorArgs (Thunk Builtin) -> AtTensorArgs (Thunk Builtin)
negateAtTensorArgs AtTensorArgs {..} =
  AtTensorArgs
    { atType = atType,
      atFirstDim = atFirstDim,
      atRemainingDims = atRemainingDims,
      atTensor = negateThunk (Forced $ ICons (Forced INatType) atFirstDim atRemainingDims) atTensor,
      atIndex = atIndex
    }

-- We can't actually lower the `not` through the body of the quantifier as
-- it is not yet unnormalised. However, it's fine to stop here as we'll
-- simply continue to normalise it once we re-encounter it again after
-- normalising the quantifier.
negateQuantifierBody ::
  (MonadDropNot m) =>
  QuantifyRatTensorArgs (Thunk Builtin) ->
  m (QuantifyRatTensorArgs (Thunk Builtin))
negateQuantifierBody (QuantifyRatTensorArgs dims fn) = do
  let (binder, Closure env body) = accessQuantifierLambda fn
  lv <- getBinderDepth
  let dims' = quote mempty lv dims
  let newBody = mkExpr accessNotTensor $ TensorOp1Args dims' body
  let quantifyFn = Forced $ VLam binder (Closure env newBody)
  return $
    QuantifyRatTensorArgs
      { quantifyDimensions = dims,
        quantifyFn = quantifyFn
      }

negateForeachArgs ::
  (MonadDropNot m) =>
  ForeachTensorArgs (Thunk Builtin) ->
  m (ForeachTensorArgs (Thunk Builtin))
negateForeachArgs (ForeachTensorArgs t dim dims fn) = do
  forcedFn <- forceValue fn
  (binder, Closure env body) <- case forcedFn of
    VLam binder closure -> return (binder, closure)
    _ -> developerError "Malformed foreachTensor"
  lv <- getBinderDepth
  let dims' = quote mempty lv dims
  let newBody = mkExpr accessNotTensor $ TensorOp1Args dims' body
  let newFn = Forced $ VLam binder (Closure env newBody)
  return $ ForeachTensorArgs t dim dims newFn
