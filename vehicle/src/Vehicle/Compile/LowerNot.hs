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
import Vehicle.Compile.TypedView.Core (CompilableBoolTensorValue (..))
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
    VBoolTensorCompareRatPointwise (op, args) -> return $ fromBoolTensorValue $ VBoolTensorCompareRatPointwise (neg op, args)
    VBoolTensorCompareRatReduced (op, args) -> return $ fromBoolTensorValue $ VBoolTensorCompareRatReduced (neg op, args)
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

negateValue :: Value Builtin -> Value Builtin -> Value Builtin
negateValue dims v =
  unforcedBuiltinApp accessNotTensorBuiltin $
    TensorOp1Args
      { tensorOp1Dims = dims,
        tensorOp1Arg = v
      }

negateOp2Args :: TensorOp2Args (Value Builtin) -> TensorOp2Args (Value Builtin)
negateOp2Args TensorOp2Args {..} =
  TensorOp2Args
    { tensorOp2Dims = tensorOp2Dims,
      tensorOp2Arg1 = negateValue tensorOp2Dims tensorOp2Arg1,
      tensorOp2Arg2 = negateValue tensorOp2Dims tensorOp2Arg2
    }

negateReductionArgs :: TensorReductionArgs (Value Builtin) -> TensorReductionArgs (Value Builtin)
negateReductionArgs TensorReductionArgs {..} =
  TensorReductionArgs
    { tensorReductionDims = tensorReductionDims,
      tensorReductionUnit = negateValue (Forced $ INil $ Forced INatType) tensorReductionUnit,
      tensorReductionTensor = negateValue tensorReductionDims tensorReductionTensor
    }

negateIfArgs :: VDims Builtin -> IfArgs (Value Builtin) -> IfArgs (Value Builtin)
negateIfArgs dims IfArgs {..} =
  IfArgs
    { ifType = ifType,
      ifCond = ifCond,
      ifArg1 = negateValue dims ifArg1,
      ifArg2 = negateValue dims ifArg2
    }

negateConstTensorArgs :: ConstTensorArgs (Value Builtin) -> ConstTensorArgs (Value Builtin)
negateConstTensorArgs ConstTensorArgs {..} =
  ConstTensorArgs
    { constType = constType,
      constValue = negateValue (Forced $ INil $ Forced INatType) constValue,
      constDims = constDims
    }

negateStackTensorArgs :: StackTensorArgs (Value Builtin) -> StackTensorArgs (Value Builtin)
negateStackTensorArgs StackTensorArgs {..} =
  StackTensorArgs
    { stackType = stackType,
      stackFirstDim = stackFirstDim,
      stackRemainingDims = stackRemainingDims,
      stackElements = fmap (negateValue stackRemainingDims) stackElements
    }

negateAtTensorArgs :: AtTensorArgs (Value Builtin) -> AtTensorArgs (Value Builtin)
negateAtTensorArgs AtTensorArgs {..} =
  AtTensorArgs
    { atType = atType,
      atFirstDim = atFirstDim,
      atRemainingDims = atRemainingDims,
      atTensor = negateValue (Forced $ ICons (Forced INatType) atFirstDim atRemainingDims) atTensor,
      atIndex = atIndex
    }

-- We can't actually lower the `not` through the body of the quantifier as
-- it is not yet unnormalised. However, it's fine to stop here as we'll
-- simply continue to normalise it once we re-encounter it again after
-- normalising the quantifier.
negateQuantifierBody ::
  (MonadDropNot m) =>
  QuantifyRatTensorArgs (Value Builtin) ->
  m (QuantifyRatTensorArgs (Value Builtin))
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
  ForeachTensorArgs (Value Builtin) ->
  m (ForeachTensorArgs (Value Builtin))
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
