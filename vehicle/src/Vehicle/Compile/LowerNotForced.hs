module Vehicle.Compile.LowerNotForced
  ( lowerNot,
    negateQuantifierBody,
  )
where

import Vehicle.Compile.Normalise.NBEForced (forceThunk)
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Normalise.TypedValueForced
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Code.Interface
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

-- | Pushes a `Not` into a boolean expression.
lowerNot ::
  forall m.
  (MonadDropNot m) =>
  TensorOp1Args (Thunk Builtin) ->
  m (Thunk Builtin)
lowerNot (TensorOp1Args dims value) = do
  boolTensorExpr <- forceThunk value
  result <- case boolTensorExpr of
    VBoolTensorLiteral b -> return $ Forced $ mkExpr accessBoolTensorLiteral (mapTensor not b)
    VBoolTensorNot args -> return $ tensorOp1Arg args
    VBoolTensorCompareIndex (op, args) -> return $ Forced $ mkExpr accessCompareIndex (neg op, args)
    VBoolTensorCompareNat (op, args) -> return $ Forced $ mkExpr accessCompareNat (neg op, args)
    VBoolTensorCompareRatPointwise (op, args) -> return $ Forced $ mkExpr accessCompareRatTensorPointwise (neg op, args)
    VBoolTensorCompareRatReduced (op, args) -> return $ negateCompareRatReduced (op, args)
    VBoolTensorQuantifyRat (q, args) -> return $ Forced $ mkExpr accessQuantifyRatTensor (neg q, negateQuantifierBody args)
    VBoolTensorQuantifyRecord (q, args) -> return $ Forced $ mkExpr accessQuantifyRecord (neg q, negateRecordQuantifierBody args)
    VBoolConstTensor args -> return $ Forced $ mkExpr accessConstTensor $ negateConstTensorArgs args
    VBoolStackTensor args -> return $ Forced $ mkExpr accessStackTensor $ negateStackTensorArgs args
    VBoolTensorOr args -> return $ Forced $ mkExpr accessAndTensor $ negateOp2Args args
    VBoolTensorAnd args -> return $ Forced $ mkExpr accessOrTensor $ negateOp2Args args
    VBoolTensorImplies args -> return $ Forced $ negateImplication args
    VBoolTensorIf args -> return $ Forced $ mkExpr accessIf $ negateIfArgs dims args
    VBoolTensorReduceOr args -> return $ Forced $ mkExpr accessReduceAnd $ negateReductionArgs args
    VBoolTensorReduceAnd args -> return $ Forced $ mkExpr accessReduceOr $ negateReductionArgs args
    VBoolTensorTensorAt args -> return $ Forced $ mkExpr accessAtTensor $ negateAtTensorArgs args
    VBoolTensorVectorAt args -> return $ Forced $ mkExpr accessAtVector $ negateAtVectorArgs args
    VBoolTensorForeach args -> Forced . mkExpr accessForeachTensor <$> negateForeachArgs args

  logDebugM MaxDetail $ do
    ctx <- getNameContext
    return $ "push-not:" <+> prettyFriendly (WithContext result ctx)

  return result

negateThunk :: Thunk Builtin -> Thunk Builtin -> Thunk Builtin
negateThunk dims v =
  Forced $
    mkExpr accessNotTensor $
      TensorOp1Args
        { tensorOp1Dims = dims,
          tensorOp1Arg = v
        }

negateImplication :: TensorOp2Args (Thunk Builtin) -> ForcedValue Builtin
negateImplication (TensorOp2Args dims x y) =
  mkExpr accessAndTensor $ TensorOp2Args dims x (negateThunk dims y)

negateOp2Args :: TensorOp2Args (Thunk Builtin) -> TensorOp2Args (Thunk Builtin)
negateOp2Args TensorOp2Args {..} =
  TensorOp2Args
    { tensorOp2Dims = tensorOp2Dims,
      tensorOp2Arg1 = negateThunk tensorOp2Dims tensorOp2Arg1,
      tensorOp2Arg2 = negateThunk tensorOp2Dims tensorOp2Arg2
    }

negateCompareRatReduced :: (ComparisonOp, TensorReduceComparisonArgs (Thunk Builtin)) -> Thunk Builtin
negateCompareRatReduced (op, TensorReduceComparisonArgs d ds xs ys) = do
  let dims = Forced $ IDimCons d ds
  let pointwiseComparison = Forced $ mkExpr accessCompareRatTensorPointwise (neg op, TensorOp2Args dims xs ys)
  Forced $ mkExpr accessReduceOr $ TensorReductionArgs dims pointwiseComparison

negateReductionArgs :: TensorReductionArgs (Thunk Builtin) -> TensorReductionArgs (Thunk Builtin)
negateReductionArgs TensorReductionArgs {..} =
  TensorReductionArgs
    { tensorReductionDims = tensorReductionDims,
      tensorReductionTensor = negateThunk tensorReductionDims tensorReductionTensor
    }

negateIfArgs :: Thunk Builtin -> IfArgs (Thunk Builtin) -> IfArgs (Thunk Builtin)
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

negateAtVectorArgs :: AtVectorArgs (Thunk Builtin) -> AtVectorArgs (Thunk Builtin)
negateAtVectorArgs _args =
  developerError "Looking up of Boolean vectors not currently supported"

{-AtVectorArgs
  { atType = atType,
    atDim = atDim,
    atVector = negateThunk (Forced $ ICons (Forced INatType) atDim atRemainingDims) atTensor,
    atIndex = atIndex
  }-}

negateQuantifierBody ::
  QuantifyRatTensorArgs (Thunk Builtin) (Closure Builtin) ->
  QuantifyRatTensorArgs (Thunk Builtin) (Closure Builtin)
negateQuantifierBody (QuantifyRatTensorArgs dims binder (Closure env body)) = do
  let newBody = mkExpr accessNotTensor $ TensorOp1Args IDimNil body
  QuantifyRatTensorArgs
    { quantifyDimensions = dims,
      quantifyBinder = binder,
      quantifyBody = Closure env newBody
    }

negateRecordQuantifierBody ::
  QuantifyRecordArgs (Thunk Builtin) (Closure Builtin) ->
  QuantifyRecordArgs (Thunk Builtin) (Closure Builtin)
negateRecordQuantifierBody (QuantifyRecordArgs typ binder (Closure env body)) = do
  let newBody = mkExpr accessNotTensor $ TensorOp1Args IDimNil body
  QuantifyRecordArgs
    { quantifyRecordType = typ,
      quantifyRecordBinder = binder,
      quantifyRecordBody = Closure env newBody
    }

negateForeachArgs ::
  (MonadDropNot m) =>
  ForeachTensorArgs (Thunk Builtin) ->
  m (ForeachTensorArgs (Thunk Builtin))
negateForeachArgs (ForeachTensorArgs t dim dims fn) = do
  forcedFn <- forceThunk fn
  (binder, Closure env body) <- case forcedFn of
    VLam binder closure -> return (binder, closure)
    _ -> developerError "Malformed foreachTensor"
  lv <- getBinderDepth
  let dims' = quote mempty lv dims
  let newBody = mkExpr accessNotTensor $ TensorOp1Args dims' body
  let newFn = Forced $ VLam binder (Closure env newBody)
  return $ ForeachTensorArgs t dim dims newFn
