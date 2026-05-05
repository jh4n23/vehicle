module Vehicle.Compile.TypedView.Core where

import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Prelude (Lv)
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Data.AST.Expr.Scoped
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Builtin.Standard.Normalise ()
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor
import Vehicle.Prelude

-------------------------------------------------------------------------------
-- Types

-- | A view on all possible expressions that can have type `Type`.
data TypeExpr
  = VUnitType
  | VBoolType
  | VIndexType (Thunk Builtin)
  | VNatType
  | VRatType
  | VTensorType (Thunk Builtin) (Thunk Builtin)
  | VListType (Thunk Builtin)
  | VVectorType (Thunk Builtin) (Thunk Builtin)
  | VPiType (VBinder Builtin) (Closure Builtin)
  | VTypeBoundVar Lv (Spine Builtin)
  | VTypeFreeVar Identifier (Spine Builtin)

instance (MonadNorm Builtin m) => TypedEvalScheme TypeExpr Builtin m where
  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Just $ \binder closure -> return $ VPiType binder closure
  handleBoundVar lv args = return $ VTypeBoundVar lv args
  handleFreeVar ident args = return $ VTypeFreeVar ident args
  handleRecordAcc = caseTypeError "RecordAcc" "BoolExpr"

  forceMeta = caseTypeError "MetaVar" "BoolExpr"
  forceBuiltin b spine = return $ case (b, spine) of
    (BuiltinType UnitType, []) -> VUnitType
    (BuiltinType BoolType, []) -> VBoolType
    (BuiltinType RatType, []) -> VRatType
    (BuiltinType IndexType, [n]) -> VIndexType (argExpr n)
    (BuiltinType NatType, []) -> VNatType
    (BuiltinType ListType, [tElem]) -> VListType (argExpr tElem)
    (BuiltinType TensorType, [tElem, ds]) -> VTensorType (argExpr tElem) (argExpr ds)
    (BuiltinType VectorType, [tElem, dim]) -> VVectorType (argExpr tElem) (argExpr dim)
    _ -> developerError $ "ill-typed type" <+> pretty b

forceTypeExpr :: (MonadNorm Builtin m) => Thunk Builtin -> m TypeExpr
forceTypeExpr = forceThunk

-------------------------------------------------------------------------------
-- Booleans

-- | A view on all possible expressions that can have type `Tensor Bool ds`.
data BoolTensorExpr
  = VBoolTensorLiteral (Tensor Bool)
  | VBoolStackTensor (StackTensorArgs (Thunk Builtin))
  | VBoolConstTensor (ConstTensorArgs (Thunk Builtin))
  | VBoolTensorAnd (TensorOp2Args (Thunk Builtin))
  | VBoolTensorOr (TensorOp2Args (Thunk Builtin))
  | VBoolTensorCompareRat (ComparisonOp, TensorComparisonArgs (Thunk Builtin))
  | VBoolTensorQuantifyRat (Quantifier, QuantifyRatTensorArgs (Thunk Builtin))
  | VBoolTensorNot (TensorOp1Args (Thunk Builtin))
  | VBoolTensorReduceAnd (TensorReductionArgs (Thunk Builtin))
  | VBoolTensorReduceOr (TensorReductionArgs (Thunk Builtin))
  | VBoolTensorCompareIndex (ComparisonOp, IndexComparisonArgs (Thunk Builtin))
  | VBoolTensorCompareNat (ComparisonOp, Op2Args (Thunk Builtin))
  | VBoolTensorAt (AtTensorArgs (Thunk Builtin))
  | VBoolTensorForeach (ForeachTensorArgs (Thunk Builtin))
  | VBoolTensorIf (IfArgs (Thunk Builtin))

instance (MonadNorm Builtin m) => TypedEvalScheme BoolTensorExpr Builtin m where
  forceBuiltin b spine = return $ case VBuiltin b spine of
    (getExpr accessBoolTensorLiteral -> Just t) -> VBoolTensorLiteral t
    (getExpr accessConstTensor -> Just args) -> VBoolConstTensor args
    (getExpr accessStackTensor -> Just args) -> VBoolStackTensor args
    (getExpr accessAndTensor -> Just args) -> VBoolTensorAnd args
    (getExpr accessOrTensor -> Just args) -> VBoolTensorOr args
    (getExpr accessNotTensor -> Just args) -> VBoolTensorNot args
    (getExpr accessQuantifyRatTensor -> Just args) -> VBoolTensorQuantifyRat args
    (getExpr accessCompareRatTensor -> Just args) -> VBoolTensorCompareRat args
    (getExpr accessCompareNat -> Just args) -> VBoolTensorCompareNat args
    (getExpr accessCompareIndex -> Just args) -> VBoolTensorCompareIndex args
    (getExpr accessReduceAnd -> Just args) -> VBoolTensorReduceAnd args
    (getExpr accessReduceOr -> Just args) -> VBoolTensorReduceOr args
    (getExpr accessAtTensor -> Just args) -> VBoolTensorAt args
    (getExpr accessForeachTensor -> Just args) -> VBoolTensorForeach args
    (getExpr accessIf -> Just args) -> VBoolTensorIf args
    _ -> developerError $ "ill-typed BoolTensor expression:" <+> pretty b <+> prettyVerbose spine
  forceMeta = caseTypeError "MetaVar" "BoolExpr"

  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar = caseTypeError "BoundVar" "BoolExpr"
  handleFreeVar = caseTypeError "FreeVar" "BoolExpr"
  handleRecordAcc = caseTypeError "RecordAcc" "BoolExpr"

forceBoolTensorExpr :: (MonadNorm Builtin m) => Thunk Builtin -> m BoolTensorExpr
forceBoolTensorExpr = forceThunk

-------------------------------------------------------------------------------
-- Naturals

-- | A view on all possible expressions that can have type `Nat`.
data NatExpr
  = VNatLiteral Int
  | VNatBoundVar Lv (Spine Builtin)
  | VNatIf (IfArgs (Thunk Builtin))
  | VNatAdd (Op2Args (Thunk Builtin))
  | VNatMul (Op2Args (Thunk Builtin))
  | VNatParameter Identifier

instance (MonadNorm Builtin m) => TypedEvalScheme NatExpr Builtin m where
  forceBuiltin b spine = return $ case VBuiltin b spine of
    (getExpr accessNatLiteral -> Just i) -> VNatLiteral i
    (getExpr accessIf -> Just args) -> VNatIf args
    (getExpr accessAddNat -> Just args) -> VNatAdd args
    (getExpr accessMulNat -> Just args) -> VNatMul args
    _ -> developerError $ "ill-typed BoolTensor expression:" <+> pretty b <+> prettyVerbose spine
  forceMeta = caseTypeError "MetaVar" "NatExpr"

  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar lv args = return $ VNatBoundVar lv args
  handleFreeVar ident spine = return $ case spine of
    [] -> VNatParameter ident
    _ -> caseTypeError "FreeVar" "NatExpr"
  handleRecordAcc = caseTypeError "RecordAcc" "NatExpr"

forceNatExpr :: (MonadNorm Builtin m) => Thunk Builtin -> m NatExpr
forceNatExpr = forceThunk

-------------------------------------------------------------------------------
-- Index

-- | A view on all possible expressions that can have type `Index n`.
data IndexExpr
  = VIndexLiteral Int
  | VIndexBoundVar Lv (Spine Builtin)
  | VIndexIf (IfArgs (Thunk Builtin))
  | VIndexRecordAcc (Type Builtin) (RecordExpr Builtin) FieldName (Spine Builtin)

instance (MonadNorm Builtin m) => TypedEvalScheme IndexExpr Builtin m where
  forceBuiltin b spine = return $ case VBuiltin b spine of
    (getExpr accessIndexLiteral -> Just (i, _)) -> VIndexLiteral i
    (getExpr accessIf -> Just args) -> VIndexIf args
    _ -> developerError $ "ill-typed BoolTensor expression:" <+> pretty b <+> prettyVerbose spine
  forceMeta = caseTypeError "MetaVar" "IndexExpr"

  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar lv spine = return $ VIndexBoundVar lv spine
  handleFreeVar = caseTypeError "FreeVar" "IndexExpr"
  handleRecordAcc typ record field spine = return $ VIndexRecordAcc typ record field spine

forceIndexExpr :: (MonadNorm Builtin m) => Thunk Builtin -> m IndexExpr
forceIndexExpr = forceThunk

-------------------------------------------------------------------------------
-- Dimensions

-- | A view on all possible expressions that can have type `List Int`.
data DimensionsExpr
  = VDimsNil
  | VDimsCons (Thunk Builtin) (Thunk Builtin)
  | VDimsIf (IfArgs (Thunk Builtin))
  | VDimsBoundVar Lv (Spine Builtin)
  | VDimsRecordAcc (Type Builtin) (RecordExpr Builtin) FieldName (Spine Builtin)

instance (MonadNorm Builtin m) => TypedEvalScheme DimensionsExpr Builtin m where
  handleUniverse _ = Nothing
  handlePi = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handleBoundVar = caseTypeError "BoundVar" "RatTensorExpr"
  handleFreeVar = caseTypeError "FreeVar" "RatTensorExpr"
  handleRecordAcc typ record field spine = return $ VDimsRecordAcc typ record field spine

  forceBuiltin b spine = return $ case VBuiltin b spine of
    (getExpr accessNil -> Just (NilArgs {})) -> VDimsNil
    (getExpr accessCons -> Just (ConsArgs _ x xs)) -> VDimsCons x xs
    (getExpr accessIf -> Just args) -> VDimsIf args
    _ -> developerError $ "ill-typed RatTensor builtin:" <+> pretty b
  forceMeta = caseTypeError "Meta" "RatTensorExpr"

forceDimensionsExpr :: (MonadNorm Builtin m) => Thunk Builtin -> m DimensionsExpr
forceDimensionsExpr = forceThunk

-------------------------------------------------------------------------------
-- Rational Tensors

-- | A view on all possible expressions that can have type `Tensor Rat`.
data RatTensorExpr
  = VRatTensorLiteral (Tensor Rational)
  | VRatConstTensor (ConstTensorArgs (Thunk Builtin))
  | VRatStackTensor (StackTensorArgs (Thunk Builtin))
  | VReduceAddRatTensor (TensorReductionArgs (Thunk Builtin))
  | VReduceMulRatTensor (TensorReductionArgs (Thunk Builtin))
  | VReduceMinRatTensor (TensorReductionArgs (Thunk Builtin))
  | VReduceMaxRatTensor (TensorReductionArgs (Thunk Builtin))
  | VNegRatTensor (TensorOp1Args (Thunk Builtin))
  | VAddRatTensor (TensorOp2Args (Thunk Builtin))
  | VSubRatTensor (TensorOp2Args (Thunk Builtin))
  | VMulRatTensor (TensorOp2Args (Thunk Builtin))
  | VDivRatTensor (TensorOp2Args (Thunk Builtin))
  | VMinRatTensor (TensorOp2Args (Thunk Builtin))
  | VMaxRatTensor (TensorOp2Args (Thunk Builtin))
  | VRatAt (AtTensorArgs (Thunk Builtin))
  | VRatForeach (ForeachTensorArgs (Thunk Builtin))
  | VIfRatTensor (IfArgs (Thunk Builtin))
  | VNetworkApplication Identifier (NetworkAppArgs (Thunk Builtin))
  | VParameterOrDataset Identifier
  | VRatTensorBoundVar Lv
  | VRatTensorRecordAcc (Type Builtin) (RecordExpr Builtin) FieldName (Spine Builtin)

instance (MonadNorm Builtin m) => TypedEvalScheme RatTensorExpr Builtin m where
  handleUniverse _ = Nothing
  handlePi = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handleBoundVar lv spine = return $ case spine of
    [] -> VRatTensorBoundVar lv
    _ -> caseTypeError "BoundVar" "RatTensorExpr"
  handleFreeVar ident spine = return $ case spine of
    (getExpr accessSpine -> Just args) -> VNetworkApplication ident args
    [] -> VParameterOrDataset ident
    _ -> caseTypeError "FreeVar" "RatTensorExpr"
  handleRecordAcc typ record field spine = return $ VRatTensorRecordAcc typ record field spine

  forceMeta = caseTypeError "Meta" "RatTensorExpr"
  forceBuiltin b spine = return $ case VBuiltin b spine of
    -- Compilable builtins
    (getExpr accessRatTensorLiteral -> Just t) -> VRatTensorLiteral t
    (getExpr accessConstTensor -> Just args) -> VRatConstTensor args
    (getExpr accessStackTensor -> Just args) -> VRatStackTensor args
    -- Non-compilable builtins
    (getExpr accessReduceAddRat -> Just args) -> VReduceAddRatTensor args
    (getExpr accessReduceMulRat -> Just args) -> VReduceMulRatTensor args
    (getExpr accessReduceMinRat -> Just args) -> VReduceMinRatTensor args
    (getExpr accessReduceMaxRat -> Just args) -> VReduceMaxRatTensor args
    (getExpr accessNegRatTensor -> Just args) -> VNegRatTensor args
    (getExpr accessAddRatTensor -> Just args) -> VAddRatTensor args
    (getExpr accessSubRatTensor -> Just args) -> VSubRatTensor args
    (getExpr accessMulRatTensor -> Just args) -> VMulRatTensor args
    (getExpr accessDivRatTensor -> Just args) -> VDivRatTensor args
    (getExpr accessMinRatTensor -> Just args) -> VMinRatTensor args
    (getExpr accessMaxRatTensor -> Just args) -> VMaxRatTensor args
    (getExpr accessIf -> Just args) -> VIfRatTensor args
    (getExpr accessAtTensor -> Just args) -> VRatAt args
    (getExpr accessForeachTensor -> Just args) -> VRatForeach args
    _ -> developerError $ "ill-typed RatTensor builtin:" <+> pretty b

forceRatTensorExpr :: (MonadNorm Builtin m) => Thunk Builtin -> m RatTensorExpr
forceRatTensorExpr = forceThunk

caseTypeError :: Doc a -> Doc a -> v
caseTypeError op exprType = developerError $ "not expecting" <+> squotes op <+> "in expression of type" <+> exprType
