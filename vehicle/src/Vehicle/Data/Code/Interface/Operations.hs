module Vehicle.Data.Code.Interface.Operations where

import Vehicle.Data.Builtin.Core.BasicOperations
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Code.Interface.Args
import Vehicle.Data.Tensor
import Vehicle.Prelude

--------------------------------------------------------------------------------
-- Interface to standard builtins
--------------------------------------------------------------------------------

class HasBuiltinConstructor expr arg | expr -> arg where
  accessBuiltinC :: Accessor (expr builtin) (builtin, [GenericArg (arg builtin)])

mkBuiltin ::
  (HasBuiltinConstructor expr arg) =>
  Accessor builtin a ->
  a ->
  [GenericArg (arg builtin)] ->
  expr builtin
mkBuiltin accessBuiltin v args = mkExpr accessBuiltinC (mkExpr accessBuiltin v, args)

getBuiltin ::
  (HasBuiltinConstructor expr arg) =>
  Accessor builtin a ->
  expr builtin ->
  Maybe (a, [GenericArg (arg builtin)])
getBuiltin accessBuiltin e = case getExpr accessBuiltinC e of
  Just (b, args) -> case getExpr accessBuiltin b of
    Just v -> Just (v, args)
    _ -> Nothing
  _ -> Nothing

--------------------------------------------------------------------------------
-- Accessors for args
--------------------------------------------------------------------------------

accessNoArgs ::
  (HasBuiltinConstructor expr arg) =>
  Accessor builtin a ->
  Accessor (expr builtin) a
accessNoArgs access =
  Access
    { getExpr = \case
        (getBuiltin access -> Just (b, [])) -> Just b
        _ -> Nothing,
      mkExpr = \b -> mkBuiltin access b []
    }

accessArgs ::
  (HasBuiltinConstructor expr arg, IsArgs args) =>
  Accessor builtin () ->
  Accessor (expr builtin) (args (arg builtin))
accessArgs accessOp =
  Access
    { getExpr = \case
        (getBuiltin accessOp -> Just ((), getExpr accessSpine -> Just args)) -> Just args
        _ -> Nothing,
      mkExpr = \args -> mkBuiltin accessOp () (mkExpr accessSpine args)
    }

accessOpAndArgs ::
  (HasBuiltinConstructor expr arg, IsArgs args) =>
  Accessor builtin op ->
  Accessor (expr builtin) (op, args (arg builtin))
accessOpAndArgs accessOp =
  Access
    { getExpr = \case
        (getBuiltin accessOp -> Just (op, getExpr accessSpine -> Just args)) -> Just (op, args)
        _ -> Nothing,
      mkExpr = \(op, args) -> mkBuiltin accessOp op (mkExpr accessSpine args)
    }

accessArgsForOp ::
  (HasBuiltinConstructor expr arg, IsArgs args, Eq op) =>
  Accessor (expr builtin) (op, args (arg builtin)) ->
  op ->
  Accessor (expr builtin) (args (arg builtin))
accessArgsForOp accessor op =
  Access
    { getExpr = \case
        (getExpr accessor -> Just (op2, args)) | op == op2 -> Just args
        _ -> Nothing,
      mkExpr = \args -> mkExpr accessor (op, args)
    }

--------------------------------------------------------------------------------
-- Types of accessors
--------------------------------------------------------------------------------

type NatComparisonAccessor expr arg op = Accessor expr (op, Op2Args arg)

type IndexComparisonAccessor expr arg op = Accessor expr (op, IndexComparisonArgs arg)

type Op1Accessor expr arg = Accessor expr (Op1Args arg)

type Op2Accessor expr arg = Accessor expr (Op2Args arg)

type TensorOp1Accessor expr arg = Accessor expr (TensorOp1Args arg)

type TensorOp2Accessor expr arg = Accessor expr (TensorOp2Args arg)

type TensorReductionAccessor expr arg = Accessor expr (TensorReductionArgs arg)

--------------------------------------------------------------------------------
-- Accessors for operations
--------------------------------------------------------------------------------
-- Booleans

type HasBoolType expr arg builtin =
  ( HasTensorExpr expr arg builtin,
    BuiltinHasBoolType builtin
  )

type HasBoolExpr expr arg builtin =
  ( HasTensorExpr expr arg builtin,
    BuiltinHasBoolLiterals builtin
  )

accessBoolType :: (HasBoolType expr arg builtin) => Accessor (expr builtin) ()
accessBoolType = accessNoArgs accessBoolTypeBuiltin

accessBoolTensorLiteral :: (BuiltinHasBoolLiterals builtin, HasBuiltinConstructor expr arg) => Accessor (expr builtin) BoolTensor
accessBoolTensorLiteral = accessNoArgs accessBoolTensorLitBuiltin

accessNotTensor :: (HasBoolExpr expr arg builtin) => TensorOp1Accessor (expr builtin) (arg builtin)
accessNotTensor = accessArgs accessNotTensorBuiltin

accessAndTensor :: (HasBoolExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessAndTensor = accessArgs accessAndTensorBuiltin

accessOrTensor :: (HasBoolExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessOrTensor = accessArgs accessOrTensorBuiltin

accessImpliesTensor :: (HasBoolExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessImpliesTensor = accessArgs accessImpliesTensorBuiltin

accessReduceAnd :: (HasBoolExpr expr arg builtin) => TensorReductionAccessor (expr builtin) (arg builtin)
accessReduceAnd = accessArgs accessReduceAndBuiltin

accessReduceOr :: (HasBoolExpr expr arg builtin) => TensorReductionAccessor (expr builtin) (arg builtin)
accessReduceOr = accessArgs accessReduceOrBuiltin

accessIf :: (HasBoolExpr expr arg builtin) => Accessor (expr builtin) (IfArgs (arg builtin))
accessIf = accessArgs accessIfBuiltin

accessCompareIndex :: (HasBoolExpr expr arg builtin) => IndexComparisonAccessor (expr builtin) (arg builtin) ComparisonOp
accessCompareIndex = accessOpAndArgs accessCompareIndexBuiltin

accessCompareNat :: (HasBoolExpr expr arg builtin) => NatComparisonAccessor (expr builtin) (arg builtin) ComparisonOp
accessCompareNat = accessOpAndArgs accessCompareNatBuiltin

accessCompareRatTensor :: (HasBoolExpr expr arg builtin) => Accessor (expr builtin) (ComparisonOp, TensorComparisonArgs (arg builtin))
accessCompareRatTensor = accessOpAndArgs accessCompareRatTensorBuiltin

accessQuantifyRatTensor :: (HasBoolExpr expr arg builtin) => Accessor (expr builtin) (Quantifier, QuantifyRatTensorArgs (arg builtin))
accessQuantifyRatTensor = accessOpAndArgs accessQuantifyRatTensorBuiltin

--------------------------------------------------------------------------------
-- Indices

type HasIndexType expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasIndexType builtin
  )

type HasIndexExpr expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasIndexLiterals builtin
  )

accessIndexType :: (HasIndexType expr arg builtin) => Accessor (expr builtin) (IndexTypeArgs (arg builtin))
accessIndexType = accessArgs accessIndexTypeBuiltin

accessIndexLiteral :: (HasIndexExpr expr arg builtin) => Accessor (expr builtin) (Int, IndexLiteralArgs (arg builtin))
accessIndexLiteral = accessOpAndArgs accessIndexLitBuiltin

--------------------------------------------------------------------------------
-- Naturals

type HasNatType expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasNatType builtin
  )

type HasNatExpr expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasNatLiterals builtin
  )

accessNatType :: (HasNatType expr arg builtin) => Accessor (expr builtin) ()
accessNatType = accessNoArgs accessNatTypeBuiltin

accessNatLiteral :: (HasNatExpr expr arg builtin) => Accessor (expr builtin) Int
accessNatLiteral = accessNoArgs accessNatLitBuiltin

accessNatTensorLiteral :: (HasNatExpr expr arg builtin) => Accessor (expr builtin) NatTensor
accessNatTensorLiteral = accessNoArgs accessNatTensorLitBuiltin

accessAddNat :: (HasNatExpr expr arg builtin) => Op2Accessor (expr builtin) (arg builtin)
accessAddNat = accessArgs accessAddNatBuiltin

accessMulNat :: (HasNatExpr expr arg builtin) => Op2Accessor (expr builtin) (arg builtin)
accessMulNat = accessArgs accessMulNatBuiltin

--------------------------------------------------------------------------------
-- Rationals

type HasRatType expr arg builtin =
  ( HasTensorExpr expr arg builtin,
    BuiltinHasRatType builtin
  )

type HasRatExpr expr arg builtin =
  ( HasTensorExpr expr arg builtin,
    BuiltinHasRatLiterals builtin
  )

accessRatType :: (HasRatType expr arg builtin) => Accessor (expr builtin) ()
accessRatType = accessNoArgs accessRatTypeBuiltin

accessRatTensorLiteral :: (HasRatExpr expr arg builtin) => Accessor (expr builtin) RatTensor
accessRatTensorLiteral = accessNoArgs accessRatTensorLitBuiltin

accessNegRatTensor :: (HasRatExpr expr arg builtin) => TensorOp1Accessor (expr builtin) (arg builtin)
accessNegRatTensor = accessArgs accessNegRatTensorBuiltin

accessAddRatTensor :: (HasRatExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessAddRatTensor = accessArgs accessAddRatTensorBuiltin

accessMulRatTensor :: (HasRatExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessMulRatTensor = accessArgs accessMulRatTensorBuiltin

accessSubRatTensor :: (HasRatExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessSubRatTensor = accessArgs accessSubRatTensorBuiltin

accessDivRatTensor :: (HasRatExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessDivRatTensor = accessArgs accessDivRatTensorBuiltin

accessMinRatTensor :: (HasRatExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessMinRatTensor = accessArgs accessMinRatTensorBuiltin

accessMaxRatTensor :: (HasRatExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessMaxRatTensor = accessArgs accessMaxRatTensorBuiltin

accessPowRatTensor :: (HasRatExpr expr arg builtin) => TensorOp2Accessor (expr builtin) (arg builtin)
accessPowRatTensor = accessArgs accessPowRatTensorBuiltin

accessReduceAddRat :: (HasRatExpr expr arg builtin) => TensorReductionAccessor (expr builtin) (arg builtin)
accessReduceAddRat = accessArgs accessReduceAddRatBuiltin

accessReduceMulRat :: (HasRatExpr expr arg builtin) => TensorReductionAccessor (expr builtin) (arg builtin)
accessReduceMulRat = accessArgs accessReduceMulRatBuiltin

accessReduceMinRat :: (HasRatExpr expr arg builtin) => TensorReductionAccessor (expr builtin) (arg builtin)
accessReduceMinRat = accessArgs accessReduceMinRatBuiltin

accessReduceMaxRat :: (HasRatExpr expr arg builtin) => TensorReductionAccessor (expr builtin) (arg builtin)
accessReduceMaxRat = accessArgs accessReduceMaxRatBuiltin

--------------------------------------------------------------------------------
-- Lists

type HasListType expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasListType builtin
  )

type HasListExpr expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasListLiterals builtin
  )

accessListType :: (HasListType expr arg builtin) => Op1Accessor (expr builtin) (arg builtin)
accessListType = accessArgs accessListTypeBuiltin

accessNil :: (HasListExpr expr arg builtin) => Accessor (expr builtin) (NilArgs (arg builtin))
accessNil = accessArgs accessNilBuiltin

accessCons :: (HasListExpr expr arg builtin) => Accessor (expr builtin) (ConsArgs (arg builtin))
accessCons = accessArgs accessConsBuiltin

accessMapList :: (HasListExpr expr arg builtin) => Accessor (expr builtin) (MapListArgs (arg builtin))
accessMapList = accessArgs accessMapListBuiltin

accessFoldList :: (HasListExpr expr arg builtin) => Accessor (expr builtin) (FoldListArgs (arg builtin))
accessFoldList = accessArgs accessFoldListBuiltin

--------------------------------------------------------------------------------
-- Vector

type HasVectorType expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasVectorType builtin
  )

type HasVectorExpr expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasVectors builtin,
    BuiltinHasNatLiterals builtin
  )

accessVectorType :: (HasVectorType expr arg builtin) => Accessor (expr builtin) (VectorTypeArgs (arg builtin))
accessVectorType = accessArgs accessVectorTypeBuiltin

accessVecLit :: (HasVectorExpr expr arg builtin) => Accessor (expr builtin) (VecLitArgs (arg builtin))
accessVecLit = accessArgs accessVecLitBuiltin

accessAtVector :: (HasVectorExpr expr arg builtin) => Accessor (expr builtin) (AtVectorArgs (arg builtin))
accessAtVector = accessArgs accessAtVectorBuiltin

accessForeachVector ::
  (HasBuiltinConstructor expr arg, BuiltinHasForeach builtin) =>
  Accessor (expr builtin) (ForeachVectorArgs (arg builtin))
accessForeachVector = accessArgs accessForeachVectorBuiltin

--------------------------------------------------------------------------------
-- Tensors

type HasTensorType expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasTensorType builtin
  )

type HasTensorExpr expr arg builtin =
  ( HasBuiltinConstructor expr arg,
    BuiltinHasTensors builtin,
    BuiltinHasListLiterals builtin,
    BuiltinHasNatLiterals builtin,
    BuiltinHasIndexLiterals builtin,
    BuiltinHasNatType builtin
  )

accessTensorType :: (HasTensorType expr arg builtin) => Accessor (expr builtin) (TensorTypeArgs (arg builtin))
accessTensorType = accessArgs accessTensorTypeBuiltin

accessStackTensor :: (HasTensorExpr expr arg builtin) => Accessor (expr builtin) (StackTensorArgs (arg builtin))
accessStackTensor = accessArgs accessStackTensorBuiltin

accessConstTensor :: (HasTensorExpr expr arg builtin) => Accessor (expr builtin) (ConstTensorArgs (arg builtin))
accessConstTensor = accessArgs accessConstTensorBuiltin

accessAtTensor :: (HasTensorExpr expr arg builtin) => Accessor (expr builtin) (AtTensorArgs (arg builtin))
accessAtTensor = accessArgs accessAtTensorBuiltin

accessForeachTensor ::
  (HasBuiltinConstructor expr arg, BuiltinHasForeach builtin) =>
  Accessor (expr builtin) (ForeachTensorArgs (arg builtin))
accessForeachTensor = accessArgs accessForeachTensorBuiltin

accessIterate ::
  (HasBuiltinConstructor expr arg, BuiltinHasIterate builtin) =>
  Accessor (expr builtin) (IterateArgs (arg builtin))
accessIterate = accessArgs accessIterateBuiltin
