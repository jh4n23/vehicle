module Vehicle.Backend.Loss.LossCompilation
  ( convertType,
    convertFunction,
    convertRatTensor,
    convertDims,
    convertBoundVar,
    convertVecLiteralArgs,
    convertVecForeachArgs,
    convertBoolTensorLiteral,
    convertNatComparison,
    convertIndexComparison,
    convertRatTensorPointwiseComparison,
    convertRatTensorReducedComparison,
    convertTensorReduction,
    convertStackTensor,
    convertConstTensor,
    convertAtTensor,
    convertForeachTensor,
    convertTensorOp1,
    convertTensorOp2,
    convertBoolTensor,
    convertNot,
    convertOr,
    convertAnd,
    convertReduceAnd,
    convertReduceOr,
    convertIf,
  )
where

import Vehicle.Backend.Loss.Core hiding (currentPass)
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Compile.TypedView
import Vehicle.Compile.TypedView.Core
import Vehicle.Data.Builtin.Interface (Accessor (..), BuiltinHasTensors (accessConstTensorBuiltin))
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Loss
import Vehicle.Data.Builtin.Standard (Builtin (..))
import Vehicle.Data.Builtin.Standard.Normalise (mkDims)
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.DifferentiableLogic
import Vehicle.Data.Tensor (Tensor, foldMapTensor, shapeOf)
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Bound.Context.Tensor
import Vehicle.Data.Variable.Bound.Level (findSliceIndices)

--------------------------------------------------------------------------------
-- Types

convertType ::
  (MonadLogic m) =>
  VType Builtin ->
  m (VType LossBuiltin)
convertType typ = logConversion typ $ do
  forcedType <- forceValue typ
  case toTypeValue forcedType of
    VPiType binder closure -> convertPiType binder closure
    VUnitType {} -> unexpectedOperation "unit type"
    VTypeFreeVar {} -> unexpectedOperation "free var type"
    VBoolType -> convertBoolType
    VTypeBoundVar lv spine -> convertBoundVar lv spine
    VRatType -> return $ Forced IRatType
    VIndexType n -> Forced . IIndexType <$> convertDim n
    VNatType -> return $ Forced INatType
    VListType tElem -> Forced . IListType <$> convertType tElem
    VVectorType {} -> unsupportedOperation "VectorType"
    VTensorType tElem ds -> do
      tElem' <- convertType tElem
      ds' <- convertDims ds
      return $ Forced $ ITensorType tElem' ds'

convertBoolType :: (MonadLogic m) => m (VType LossBuiltin)
convertBoolType = return $ Forced IRatType

convertPiType :: (MonadLogic m) => VBinder Builtin -> Closure Builtin -> m (VType LossBuiltin)
convertPiType binder closure = do
  binder' <- traverse convertType binder
  closure' <- convertClosure convertType binder closure
  return $ Forced $ VPi binder' closure'

--------------------------------------------------------------------------------
-- Dims

convertDim ::
  (MonadLogic m) =>
  Thunk Builtin ->
  m (Thunk LossBuiltin)
convertDim value = logConversion value $ do
  forcedValue <- forceValue value
  case toNatValue forcedValue of
    VNatBoundVar v spine -> convertBoundVar v spine
    VNatParameter ident -> return $ Forced $ VFreeVar ident []
    VNatLiteral i -> return $ Forced $ mkExpr accessNatLiteral i
    VNatAdd args -> Forced . mkExpr accessAddNat <$> traverseOp2Args convertDim args
    VNatMul args -> Forced . mkExpr accessMulNat <$> traverseOp2Args convertDim args
    VNatIf {} -> unsupportedOperation "if"

convertDims ::
  (MonadLogic m) =>
  VDims Builtin ->
  m (VDims LossBuiltin)
convertDims value = logConversion value $ do
  forcedValue <- forceValue value
  case toDimensionsValue forcedValue of
    VDimsBoundVar lv spine -> convertBoundVar lv spine
    VDimsIf args -> convertIf args
    VDimsNil -> return $ Forced $ INil $ Forced INatType
    VDimsCons d ds -> do
      d' <- convertDim d
      ds' <- convertDims ds
      return $ Forced $ ICons (Forced INatType) d' ds'

--------------------------------------------------------------------------------
-- Variables

convertFunction ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  Thunk Builtin ->
  m (Thunk LossBuiltin)
convertFunction convertValue value = do
  forcedValue <- forceValue value
  case forcedValue of
    VLam binder closure -> do
      binder' <- traverse convertType binder
      closure' <- convertClosure convertValue binder closure
      return $ Forced $ VLam binder' closure'
    _ -> convertValue value

convertClosure ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  VBinder Builtin ->
  Closure Builtin ->
  m (Closure LossBuiltin)
convertClosure convertValue binder closure = do
  normBody <- extendClosureWithBound binder closure
  finalCtx <- getShrunkenContext
  lossBody <- addNonTensorBinderToContext binder $ do
    normLossBody <- convertFunction convertValue normBody
    return $ quote mempty (1 + boundCtxLv finalCtx) normLossBody
  return $ Closure (boundContextToEnv finalCtx) lossBody

-- | This function converts a DeBruijn level back into a loss value.
-- Crucially if the variable represents a slice of a quantified user variable
-- (e.g. X[0,1]) then it is replaced in terms of the original tensor variable
-- (e.g. X ! 0 ! 1)
convertBoundVar ::
  (MonadLogic m) =>
  Lv ->
  Spine Builtin ->
  m (Thunk LossBuiltin)
convertBoundVar lv = \case
  _ : _ -> unexpectedExprError currentPass "bound function variables"
  [] -> do
    (originalLv, maybeVars) <- lookupVariableInNestedCtx lv
    let var = Forced $ VBoundVar originalLv []
    case maybeVars of
      Nothing -> return var
      Just (parentVar, sliceVar) -> do
        let indices = findSliceIndices parentVar sliceVar
        return $ mkIndexInto (Forced IRatType) var (shapeOf parentVar) indices

convertFreeVar ::
  (MonadLogic m) =>
  Identifier ->
  Spine Builtin ->
  m (Thunk LossBuiltin)
convertFreeVar name = \case
  [] -> return $ Forced $ VFreeVar name []
  spine -> case getExpr accessSpine spine of
    Nothing -> unexpectedExprError currentPass "non-network args"
    Just (NetworkAppArgs arg) -> do
      args' <- NetworkAppArgs <$> convertRatTensor arg
      return $ Forced $ VFreeVar name $ mkExpr accessSpine args'

--------------------------------------------------------------------------------
-- Bool

convertBoolTensor :: (MonadLogic m) => Thunk Builtin -> m (Thunk LossBuiltin)
convertBoolTensor value = logConversion value $ do
  forcedValue <- forceValue value
  case toBoolTensorValue forcedValue of
    VBoolTensorLiteral bs -> convertBoolTensorLiteral bs
    VBoolConstTensor args -> convertConstTensor convertBoolTensor args
    VBoolStackTensor args -> convertStackTensor convertBoolTensor args
    VBoolTensorNot args -> convertNot =<< convertTensorOp1 convertBoolTensor args
    VBoolTensorAnd args -> convertAnd =<< convertTensorOp2 convertBoolTensor args
    VBoolTensorOr args -> convertOr =<< convertTensorOp2 convertBoolTensor args
    VBoolTensorCompareIndex args -> convertIndexComparison args
    VBoolTensorCompareNat args -> convertNatComparison args
    VBoolTensorCompareRatPointwise args -> convertRatTensorPointwiseComparison args
    VBoolTensorCompareRatReduced args -> convertRatTensorReducedComparison args
    VBoolTensorReduceAnd args -> convertReduceAnd =<< convertTensorReduction convertBoolTensor args
    VBoolTensorReduceOr args -> convertReduceOr =<< convertTensorReduction convertBoolTensor args
    VBoolTensorQuantifyRat {} -> unexpectedOperation "quantifier"
    VBoolTensorBoolIf args -> convertIf args
    VBoolTensorAt args -> convertAtTensor convertBoolTensor args
    VBoolTensorForeach args -> convertForeachTensor convertBoolTensor args

convertBoolTensorLiteral :: (MonadLogic m) => Tensor Bool -> m (Thunk LossBuiltin)
convertBoolTensorLiteral tensor = do
  trueExpr <- getLogicField TruthityElement
  falseExpr <- getLogicField FalsityElement

  let convertBool b = if b then trueExpr else falseExpr
  let foldLayer shape elems =
        Forced $
          mkExpr accessStackTensor $
            StackTensorArgs
              { stackType = Forced INatType,
                stackFirstDim = Forced $ INatLiteral $ length elems,
                stackRemainingDims = mkDims shape,
                stackElements = elems
              }
  return $ foldMapTensor convertBool foldLayer tensor

convertNot :: (MonadLogic m) => TensorOp1Args (Thunk LossBuiltin) -> m (Thunk LossBuiltin)
convertNot = convertLogicField PointwiseNegation

convertAnd :: (MonadLogic m) => TensorOp2Args (Thunk LossBuiltin) -> m (Thunk LossBuiltin)
convertAnd = convertLogicField PointwiseConjunction

convertOr :: (MonadLogic m) => TensorOp2Args (Thunk LossBuiltin) -> m (Thunk LossBuiltin)
convertOr = convertLogicField PointwiseDisjunction

convertReduceAnd :: (MonadLogic m) => TensorReductionArgs (Thunk LossBuiltin) -> m (Thunk LossBuiltin)
convertReduceAnd = convertLogicField ReduceConjunction

convertReduceOr :: (MonadLogic m) => TensorReductionArgs (Thunk LossBuiltin) -> m (Thunk LossBuiltin)
convertReduceOr = convertLogicField ReduceDisjunction

convertNatComparison :: (MonadLogic m) => (ComparisonOp, Op2Args (Thunk Builtin)) -> m (Thunk LossBuiltin)
convertNatComparison _args = unsupportedOperation "NatComparison"

convertIndexComparison :: (MonadLogic m) => (ComparisonOp, IndexComparisonArgs (Thunk Builtin)) -> m (Thunk LossBuiltin)
convertIndexComparison _args = unsupportedOperation "IndexComparison"

convertRatTensorPointwiseComparison :: (MonadLogic m) => (ComparisonOp, TensorOp2Args (Thunk Builtin)) -> m (Thunk LossBuiltin)
convertRatTensorPointwiseComparison (op, args) = do
  args' <- convertTensorOp2 convertRatTensor args
  convertLogicField (comparisonOpToField op) args'

convertRatTensorReducedComparison :: (MonadLogic m) => (ComparisonOp, TensorReduceComparisonArgs (Thunk Builtin)) -> m (Thunk LossBuiltin)
convertRatTensorReducedComparison (op, args) =
  unsupportedOperation $ "RatTensorCompareReduced" <+> pretty op <+> prettyVerbose (mkExpr accessSpine args)

convertIf ::
  (MonadLogic m) =>
  IfArgs (Thunk Builtin) ->
  m (Thunk LossBuiltin)
convertIf _args = unsupportedOperation "if"

convertLogicField ::
  (MonadLogic m, IsArgs args) =>
  TensorDifferentiableLogicField ->
  args (Thunk LossBuiltin) ->
  m (Thunk LossBuiltin)
convertLogicField field args = do
  fn <- getLogicField field
  logDebugM MaxDetail $ do
    fnDoc <- prettyFriendlyInCtx fn
    return $ "subst-field" <+> pretty field <> ":" <+> fnDoc
  return $ UnforcedApp fn (mkExpr accessSpine args)

--------------------------------------------------------------------------------
-- Index

convertIndex ::
  (MonadLogic m) =>
  Thunk Builtin ->
  m (Thunk LossBuiltin)
convertIndex value = logConversion value $ do
  forcedValue <- forceValue value
  case toIndexValue forcedValue of
    VIndexLiteral i -> Forced . IIndexLiteral i <$> convertDim dim
    VIndexBoundVar v spine -> convertBoundVar v spine
    VIndexIf args -> convertIf args

--------------------------------------------------------------------------------
-- Rat

convertRatTensor ::
  (MonadLogic m) =>
  Thunk Builtin ->
  m (Thunk LossBuiltin)
convertRatTensor value = logConversion value $ do
  forcedValue <- forceValue value
  case toRatTensorValue forcedValue of
    VRatTensorBoundVar lv -> convertBoundVar lv mempty
    VRatTensorFreeVar name [] -> return $ Forced $ VFreeVar name []
    VRatTensorFreeVar name spine -> convertFreeVar name spine
    VRatTensorLiteral t -> return $ Forced $ mkExpr accessRatTensorLiteral t
    VNegRatTensor args -> Forced . mkExpr accessNegRatTensor <$> convertTensorOp1 convertRatTensor args
    VAddRatTensor args -> Forced . mkExpr accessAddRatTensor <$> convertTensorOp2 convertRatTensor args
    VSubRatTensor args -> Forced . mkExpr accessSubRatTensor <$> convertTensorOp2 convertRatTensor args
    VMulRatTensor args -> Forced . mkExpr accessMulRatTensor <$> convertTensorOp2 convertRatTensor args
    VDivRatTensor args -> Forced . mkExpr accessDivRatTensor <$> convertTensorOp2 convertRatTensor args
    VMinRatTensor args -> Forced . mkExpr accessMinRatTensor <$> convertTensorOp2 convertRatTensor args
    VMaxRatTensor args -> Forced . mkExpr accessMaxRatTensor <$> convertTensorOp2 convertRatTensor args
    VReduceAddRatTensor args -> Forced . mkExpr accessReduceAddRat <$> convertTensorReduction convertRatTensor args
    VReduceMulRatTensor args -> Forced . mkExpr accessReduceMulRat <$> convertTensorReduction convertRatTensor args
    VReduceMinRatTensor args -> Forced . mkExpr accessReduceMinRat <$> convertTensorReduction convertRatTensor args
    VReduceMaxRatTensor args -> Forced . mkExpr accessReduceMaxRat <$> convertTensorReduction convertRatTensor args
    VIfRatTensor args -> convertIf args
    VRatConstTensor args -> convertConstTensor convertRatTensor args
    VRatStackTensor args -> convertStackTensor convertRatTensor args
    VRatAt args -> convertAtTensor convertRatTensor args
    VRatForeach args -> convertForeachTensor convertRatTensor args

--------------------------------------------------------------------------------
-- Vector

-- Vector operations are converted to tensor operations.

convertVecLiteralArgs ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  (VType Builtin, VDims Builtin) ->
  VecLitArgs (Thunk Builtin) ->
  m (Thunk LossBuiltin)
convertVecLiteralArgs convertValue (elemType, dims) (VecLitArgs _typ dim xs) = do
  convertStackTensor convertValue $
    StackTensorArgs
      { stackType = elemType,
        stackFirstDim = dim,
        stackRemainingDims = dims,
        stackElements = xs
      }

convertVecForeachArgs ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  (VType Builtin, VDims Builtin) ->
  ForeachVectorArgs (Thunk Builtin) ->
  m (Thunk LossBuiltin)
convertVecForeachArgs convertValue (elemType, dims) (ForeachVectorArgs _typ dim xs) =
  convertForeachTensor convertValue $
    ForeachTensorArgs
      { foreachTensorType = elemType,
        foreachTensorFirstDim = dim,
        foreachTensorRemainingDims = dims,
        foreachTensorFn = xs
      }

--------------------------------------------------------------------------------
-- Tensor

convertTensorOp1 ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  TensorOp1Args (Thunk Builtin) ->
  m (TensorOp1Args (Thunk LossBuiltin))
convertTensorOp1 go (TensorOp1Args dims xs) =
  TensorOp1Args <$> convertDims dims <*> go xs

convertTensorOp2 ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  TensorOp2Args (Thunk Builtin) ->
  m (TensorOp2Args (Thunk LossBuiltin))
convertTensorOp2 go (TensorOp2Args dims xs ys) =
  TensorOp2Args <$> convertDims dims <*> go xs <*> go ys

convertTensorReduction ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  TensorReductionArgs (Thunk Builtin) ->
  m (TensorReductionArgs (Thunk LossBuiltin))
convertTensorReduction go (TensorReductionArgs dims e xs) =
  TensorReductionArgs <$> convertDims dims <*> go e <*> go xs

convertAtTensor ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  AtTensorArgs (Thunk Builtin) ->
  m (Thunk LossBuiltin)
convertAtTensor convertValue (AtTensorArgs typ dim dims xs i) = do
  type' <- convertType typ
  dim' <- convertDim dim
  dims' <- convertDims dims
  xs' <- convertValue xs
  i' <- convertIndex i
  return $ Forced $ mkExpr accessAtTensor $ AtTensorArgs type' dim' dims' xs' i'

convertStackTensor ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  StackTensorArgs (Thunk Builtin) ->
  m (Thunk LossBuiltin)
convertStackTensor convertValue (StackTensorArgs typ dim dims xs) = do
  type' <- convertType typ
  dim' <- convertDim dim
  dims' <- convertDims dims
  xs' <- traverse convertValue xs
  return $ Forced $ mkExpr accessStackTensor $ StackTensorArgs type' dim' dims' xs'

convertConstTensor ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  ConstTensorArgs (Thunk Builtin) ->
  m (Thunk LossBuiltin)
convertConstTensor convertValue (ConstTensorArgs typ value dims) = do
  type' <- convertType typ
  value' <- convertValue value
  dims' <- convertDims dims
  return $ unforcedBuiltinApp accessConstTensorBuiltin $ ConstTensorArgs type' value' dims'

convertForeachTensor ::
  (MonadLogic m) =>
  (Thunk Builtin -> m (Thunk LossBuiltin)) ->
  ForeachTensorArgs (Thunk Builtin) ->
  m (Thunk LossBuiltin)
convertForeachTensor convertValue (ForeachTensorArgs t dim dims fn) = do
  t' <- convertType t
  dim' <- convertDim dim
  dims' <- convertDims dims
  fn' <- convertFunction convertValue fn
  return $ Forced $ mkExpr accessForeachTensor $ ForeachTensorArgs t' dim' dims' fn'

--------------------------------------------------------------------------------
-- Utils

currentPass :: Doc a
currentPass = "logic translation"

logConversion ::
  (MonadLogger m, MonadReadableNameContext m) =>
  Thunk Builtin ->
  m (Thunk LossBuiltin) ->
  m (Thunk LossBuiltin)
logConversion e action = do
  logDebugM MaxDetail $ do
    inputDoc <- prettyFriendlyInCtx e
    return $ "enter-loss" <+> ":" <+> inputDoc
  incrCallDepth

  result <- action

  decrCallDepth
  logDebugM MaxDetail $ do
    outputDoc <- prettyFriendlyInCtx result
    return $ "exit-loss" <+> ": " <+> outputDoc

  return result
