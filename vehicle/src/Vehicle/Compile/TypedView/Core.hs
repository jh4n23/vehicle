module Vehicle.Compile.TypedView.Core where

import GHC.Stack (HasCallStack)
import Vehicle.Compile.Prelude (Lv)
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Data.AST.Expr.Scoped
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor
import Vehicle.Prelude
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Normalise.NBE

-------------------------------------------------------------------------------
-- Booleans

-- | A view on all possible expressions that can have type `Bool` that we know how to compile
-- to constraints.

data CompilableBoolTensorExpr
  = VBoolTensorLiteral (Tensor Bool)
  | VBoolStackTensor (StackTensorArgs (Expr Builtin))
  | VBoolConstTensor (ConstTensorArgs (Expr Builtin))
  | VBoolTensorAnd (TensorOp2Args (Expr Builtin))
  | VBoolTensorOr (TensorOp2Args (Expr Builtin))
  | VBoolTensorCompareRatReduced (ComparisonOp, TensorOp2Args (Expr Builtin))
  | VBoolTensorQuantifyRat (Quantifier, QuantifyRatTensorArgs (Expr Builtin))
  | VBoolTensorNot (TensorOp1Args (Expr Builtin))

-- | A view on all possible expressions that can have type `Bool`.
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
    (getExpr accessCompareRatTensorPointwise -> Just args) -> VBoolTensorCompareRatPointwise args
    (getExpr accessQuantifyRatTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorQuantifyRat args
    (getExpr accessCompareRatTensorReduced -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorCompareRatReduced args
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

forceBoolTensorExpr :: (HasCallStack) => BoundEnv Builtin -> Expr Builtin -> m BoolTensorExpr
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
  handleFreeVar = VNatParameter
  handleMeta = caseTypeError "MetaVar" "NatExpr"
  handleRecordAcc = caseTypeError "RecordAcc" "NatExpr"

-------------------------------------------------------------------------------
-- Index

-- | A view on all possible expressions that can have type `Index n`.
newtype CompilableIndexValue
  = VIndexLiteral Int

data IndexExpr
  = VCompilableIndexValue CompilableIndexValue
  | VIndexBoundVar Lv (Args Builtin)
  | VIndexIf (IfArgs (Expr Builtin))

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
  handleRecordAcc = caseTypeError "RecordAcc" "IndexExpr"

-------------------------------------------------------------------------------
-- Dimensions

-- | A view on all possible expressions that can have type `List Int`.
data CompilableDimensionsExpr
  = VDimsNil
  | VDimsCons (Value Builtin) (Value Builtin)

data DimensionsExpr
  = VCompilableDimensionsExpr CompilableDimensionsExpr
  | VDimsIf (IfArgs (Expr Builtin))
  | VDimsBoundVar Lv (Spine Builtin)

toDimensionsExpr :: (HasCallStack) => BoundEnv Builtin -> Expr Builtin -> m DimensionsExpr
toDimensionsExpr e = case e of
  VBoundVar lv spine -> VDimsBoundVar lv spine
  (getExpr accessNil -> Just (NilArgs {})) -> VDimsNil
  (getExpr accessCons -> Just (ConsArgs _ x xs)) -> VDimsCons x xs
  (getExpr accessIf -> Just args) -> VDimsIf args
  _ -> developerError $ "ill-typed Dimensions expression" <+> prettyVerbose e

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

instance TypedEvalScheme RatTensorExpr Builtin where
  handleUniverse = Nothing
  handlePi = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handleBoundVar lv args = VCompilableRatTensorValue _
  handleFreeVar ident spine = case spine of
    getExpr accessSpine -> Just networkArgs -> _
    {-
  case getExpr accessSpine spine of
      Just args -> unblock status =<< unblockNetworkApp n args
      -- Parameters and other scalar free vars may appear in constraints used
      -- for quantifier-domain extraction, e.g. `-epsilon < x ! 0 < epsilon`.
      _ -> return expr
      -}

  handleMeta = caseTypeError "Meta" "RatTensorExpr"
  handleRecordAcc = _

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

currentPass :: Doc a
currentPass = "typed evaluation"

caseTypeError :: Doc a -> Doc a -> v
caseTypeError op exprType = developerError $ "not expecting" <+> squotes op <+> "in expression of type" <+> exprType
