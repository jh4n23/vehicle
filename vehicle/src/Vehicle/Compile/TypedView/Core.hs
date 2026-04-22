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
  | VIndexType (Expr Builtin)
  | VNatType
  | VRatType
  | VTensorType (Expr Builtin) (Expr Builtin)
  | VListType (Expr Builtin)
  | VVectorType (Expr Builtin) (Expr Builtin)
  | VPiType (Binder Builtin) (Expr Builtin)
  | VTypeBoundVar Lv (Args Builtin)
  | VTypeFreeVar Identifier (Args Builtin)

instance TypedEvalScheme TypeExpr Builtin where
  handleUniverse = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Just VPiType
  handleBoundVar = VTypeBoundVar
  handleFreeVar = VTypeFreeVar
  handleMeta = caseTypeError "MetaVar" "BoolExpr"
  handleRecordAcc = caseTypeError "RecordAcc" "BoolExpr"

  handleBuiltin b spine = case (b, spine) of
    (BuiltinType UnitType, []) -> VUnitType
    (BuiltinType BoolType, []) -> VBoolType
    (BuiltinType RatType, []) -> VRatType
    (BuiltinType IndexType, [n]) -> VIndexType (argExpr n)
    (BuiltinType NatType, []) -> VNatType
    (BuiltinType ListType, [tElem]) -> VListType (argExpr tElem)
    (BuiltinType TensorType, [tElem, ds]) -> VTensorType (argExpr tElem) (argExpr ds)
    (BuiltinType VectorType, [tElem, dim]) -> VVectorType (argExpr tElem) (argExpr dim)
    _ -> developerError $ "ill-typed type" <+> pretty b

forceTypeExpr :: (MonadNorm Builtin m) => BoundEnv Builtin -> Expr Builtin -> m TypeExpr
forceTypeExpr env expr = forceThunk (Thunk env expr)

-------------------------------------------------------------------------------
-- Booleans

-- | A view on all possible expressions that can have type `Tensor Bool ds`
-- and that we know how to compile to constraints.
data CompilableBoolTensorExpr
  = VBoolTensorLiteral (Tensor Bool)
  | VBoolStackTensor (StackTensorArgs (Expr Builtin))
  | VBoolConstTensor (ConstTensorArgs (Expr Builtin))
  | VBoolTensorAnd (TensorOp2Args (Expr Builtin))
  | VBoolTensorOr (TensorOp2Args (Expr Builtin))
  | VBoolTensorCompareRatReduced (ComparisonOp, TensorOp2Args (Expr Builtin))
  | VBoolTensorQuantifyRat (Quantifier, QuantifyRatTensorArgs (Expr Builtin))
  | VBoolTensorNot (TensorOp1Args (Expr Builtin))

-- | A view on all possible expressions that can have type `Tensor Bool ds`.
data BoolTensorExpr
  = VCompilableBoolTensorExpr CompilableBoolTensorExpr
  | VBoolTensorReduceAnd (TensorReductionArgs (Expr Builtin))
  | VBoolTensorReduceOr (TensorReductionArgs (Expr Builtin))
  | VBoolTensorCompareIndex (ComparisonOp, IndexComparisonArgs (Expr Builtin))
  | VBoolTensorCompareNat (ComparisonOp, Op2Args (Expr Builtin))
  | VBoolTensorAt (AtTensorArgs (Expr Builtin))
  | VBoolTensorForeach (ForeachTensorArgs (Expr Builtin))
  | VBoolTensorCompareRatPointwise (ComparisonOp, TensorOp2Args (Expr Builtin))
  | VBoolTensorIf (IfArgs (Expr Builtin))

instance TypedEvalScheme BoolTensorExpr Builtin where
  handleBuiltin b spine = case normAppList (Builtin mempty b) spine of
    (getExpr accessBoolTensorLiteral -> Just t) -> VCompilableBoolTensorExpr $ VBoolTensorLiteral t
    (getExpr accessConstTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolConstTensor args
    (getExpr accessStackTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolStackTensor args
    (getExpr accessAndTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorAnd args
    (getExpr accessOrTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorOr args
    (getExpr accessNotTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorNot args
    (getExpr accessQuantifyRatTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorQuantifyRat args
    (getExpr accessCompareRatTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorCompareRatReduced _
    (getExpr accessCompareNat -> Just args) -> VBoolTensorCompareNat args
    (getExpr accessCompareIndex -> Just args) -> VBoolTensorCompareIndex args
    (getExpr accessReduceAnd -> Just args) -> VBoolTensorReduceAnd args
    (getExpr accessReduceOr -> Just args) -> VBoolTensorReduceOr args
    (getExpr accessAtTensor -> Just args) -> VBoolTensorAt args
    (getExpr accessForeachTensor -> Just args) -> VBoolTensorForeach args
    (getExpr accessIf -> Just args) -> VBoolTensorIf args
    _ -> developerError $ "ill-typed BoolTensor expression:" <+> pretty b <+> prettyVerbose spine

  handleUniverse = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar = caseTypeError "BoundVar" "BoolExpr"
  handleFreeVar = caseTypeError "FreeVar" "BoolExpr"
  handleMeta = caseTypeError "MetaVar" "BoolExpr"
  handleRecordAcc = caseTypeError "RecordAcc" "BoolExpr"

forceBoolTensorExpr :: (MonadNorm Builtin m) => BoundEnv Builtin -> Expr Builtin -> m BoolTensorExpr
forceBoolTensorExpr env expr = forceThunk (Thunk env expr)

-------------------------------------------------------------------------------
-- Naturals

newtype CompilableNatExpr
  = VNatLiteral Int

-- | A view on all possible expressions that can have type `Nat`.
data NatExpr
  = VCompilableNat CompilableNatExpr
  | VNatBoundVar Lv (Args Builtin)
  | VNatIf (IfArgs (Expr Builtin))
  | VNatAdd (Op2Args (Expr Builtin))
  | VNatMul (Op2Args (Expr Builtin))
  | VNatParameter Identifier

instance TypedEvalScheme NatExpr Builtin where
  handleBuiltin b spine = case normAppList (Builtin mempty b) spine of
    (getExpr accessNatLiteral -> Just i) -> VCompilableNat $ VNatLiteral i
    (getExpr accessIf -> Just args) -> VNatIf args
    (getExpr accessAddNat -> Just args) -> VNatAdd args
    (getExpr accessMulNat -> Just args) -> VNatMul args
    _ -> developerError $ "ill-typed BoolTensor expression:" <+> pretty b <+> prettyVerbose spine

  handleUniverse = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar = VNatBoundVar
  handleFreeVar ident spine = case spine of
    [] -> VNatParameter ident
    _ -> caseTypeError "FreeVar" "NatExpr"
  handleMeta = caseTypeError "MetaVar" "NatExpr"
  handleRecordAcc = caseTypeError "RecordAcc" "NatExpr"

forceNatExpr :: (MonadNorm Builtin m) => BoundEnv Builtin -> Expr Builtin -> m NatExpr
forceNatExpr env expr = forceThunk (Thunk env expr)

-------------------------------------------------------------------------------
-- Index

-- | A view on all possible expressions that can have type `Index n`.
newtype CompilableIndexValue
  = VIndexLiteral Int

data IndexExpr
  = VCompilableIndexValue CompilableIndexValue
  | VIndexBoundVar Lv (Args Builtin)
  | VIndexIf (IfArgs (Expr Builtin))
  | VIndexRecordAcc (Type Builtin) (RecordExpr Builtin) FieldName (Args Builtin)

instance TypedEvalScheme IndexExpr Builtin where
  handleBuiltin b spine = case normAppList (Builtin mempty b) spine of
    (getExpr accessIndexLiteral -> Just (i, _)) -> VCompilableIndexValue $ VIndexLiteral i
    (getExpr accessIf -> Just args) -> VIndexIf args
    _ -> developerError $ "ill-typed BoolTensor expression:" <+> pretty b <+> prettyVerbose spine

  handleUniverse = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar = VIndexBoundVar
  handleFreeVar = caseTypeError "FreeVar" "IndexExpr"
  handleMeta = caseTypeError "MetaVar" "IndexExpr"
  handleRecordAcc = VIndexRecordAcc

forceIndexExpr :: (MonadNorm Builtin m) => BoundEnv Builtin -> Expr Builtin -> m IndexExpr
forceIndexExpr env expr = forceThunk (Thunk env expr)

-------------------------------------------------------------------------------
-- Dimensions

-- | A view on all possible expressions that can have type `List Int`.
data CompilableDimensionsExpr
  = VDimsNil
  | VDimsCons (Expr Builtin) (Expr Builtin)

data DimensionsExpr
  = VCompilableDimensionsExpr CompilableDimensionsExpr
  | VDimsIf (IfArgs (Expr Builtin))
  | VDimsBoundVar Lv (Args Builtin)
  | VDimsRecordAcc (Type Builtin) (RecordExpr Builtin) FieldName (Args Builtin)

instance TypedEvalScheme DimensionsExpr Builtin where
  handleUniverse = Nothing
  handlePi = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handleBoundVar = caseTypeError "BoundVar" "RatTensorExpr"
  handleFreeVar = caseTypeError "FreeVar" "RatTensorExpr"
  handleMeta = caseTypeError "Meta" "RatTensorExpr"
  handleRecordAcc = VDimsRecordAcc

  handleBuiltin b spine = case normAppList (Builtin mempty b) spine of
    (getExpr accessNil -> Just (NilArgs {})) -> VCompilableDimensionsExpr VDimsNil
    (getExpr accessCons -> Just (ConsArgs _ x xs)) -> VCompilableDimensionsExpr $ VDimsCons x xs
    (getExpr accessIf -> Just args) -> VDimsIf args
    _ -> developerError $ "ill-typed RatTensor builtin:" <+> pretty b

forceDimensionsExpr :: (MonadNorm Builtin m) => BoundEnv Builtin -> Expr Builtin -> m DimensionsExpr
forceDimensionsExpr env expr = forceThunk (Thunk env expr)

-------------------------------------------------------------------------------
-- Rational Tensors

-- | A view on all possible compilable expressions that can have type `Tensor Rat`.
data CompilableRatTensorValue
  = VRatTensorLiteral (Tensor Rational)
  | VRatConstTensor (ConstTensorArgs (Expr Builtin))
  | VRatStackTensor (StackTensorArgs (Expr Builtin))

-- | A view on all possible expressions that can have type `Tensor Rat`.
data RatTensorExpr
  = VCompilableRatTensorValue CompilableRatTensorValue
  | VReduceAddRatTensor (TensorReductionArgs (Expr Builtin))
  | VReduceMulRatTensor (TensorReductionArgs (Expr Builtin))
  | VReduceMinRatTensor (TensorReductionArgs (Expr Builtin))
  | VReduceMaxRatTensor (TensorReductionArgs (Expr Builtin))
  | VNegRatTensor (TensorOp1Args (Expr Builtin))
  | VAddRatTensor (TensorOp2Args (Expr Builtin))
  | VSubRatTensor (TensorOp2Args (Expr Builtin))
  | VMulRatTensor (TensorOp2Args (Expr Builtin))
  | VDivRatTensor (TensorOp2Args (Expr Builtin))
  | VMinRatTensor (TensorOp2Args (Expr Builtin))
  | VMaxRatTensor (TensorOp2Args (Expr Builtin))
  | VRatAt (AtTensorArgs (Expr Builtin))
  | VRatForeach (ForeachTensorArgs (Expr Builtin))
  | VIfRatTensor (IfArgs (Expr Builtin))
  | VNetworkApplication Identifier (NetworkAppArgs (Expr Builtin))
  | VParameterOrDataset Identifier
  | VRatTensorBoundVar Lv
  | VRatTensorRecordAcc (Type Builtin) (RecordExpr Builtin) FieldName (Args Builtin)

instance TypedEvalScheme RatTensorExpr Builtin where
  handleUniverse = Nothing
  handlePi = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handleBoundVar lv spine = case spine of
    [] -> VRatTensorBoundVar lv
    _ -> caseTypeError "BoundVar" "RatTensorExpr"
  handleFreeVar ident spine = case spine of
    (getExpr accessSpine -> Just args) -> VNetworkApplication ident args
    [] -> VParameterOrDataset ident
    _ -> caseTypeError "FreeVar" "RatTensorExpr"
  handleMeta = caseTypeError "Meta" "RatTensorExpr"
  handleRecordAcc = VRatTensorRecordAcc

  handleBuiltin b spine = case normAppList (Builtin mempty b) spine of
    -- Compilable builtins
    (getExpr accessRatTensorLiteral -> Just t) -> VCompilableRatTensorValue $ VRatTensorLiteral t
    (getExpr accessConstTensor -> Just args) -> VCompilableRatTensorValue $ VRatConstTensor args
    (getExpr accessStackTensor -> Just args) -> VCompilableRatTensorValue $ VRatStackTensor args
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

forceRatTensorExpr :: (MonadNorm Builtin m) => BoundEnv Builtin -> Expr Builtin -> m RatTensorExpr
forceRatTensorExpr env expr = forceThunk (Thunk env expr)

caseTypeError :: Doc a -> Doc a -> v
caseTypeError op exprType = developerError $ "not expecting" <+> squotes op <+> "in expression of type" <+> exprType
