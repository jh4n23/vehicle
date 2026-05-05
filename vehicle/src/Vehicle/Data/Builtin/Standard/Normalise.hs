{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Data.Builtin.Standard.Normalise
  ( mkListExpr,
    mkDims,
  )
where

import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Normalise.NBE
import Vehicle.Data.Builtin.Core as Syntax
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Prelude (HasIdentifier (identifierOf))

---------------------------------------------------------------------------------
--- Normalisation

instance HasTensorLiterals Builtin where
  tensorLiterals =
    [ Wrapper accessBoolTensorLiteral,
      Wrapper accessNatTensorLiteral,
      Wrapper accessRatTensorLiteral
    ]

instance HasLiftableTensorOperations Builtin where
  liftableTensorOp1s =
    [ (accessNegRatTensor, accessNegRatTensorBuiltin, Forced IRatType),
      (accessNotTensor, accessNotTensorBuiltin, Forced IBoolType)
    ]

  liftableTensorOp2s =
    [ (accessAddRatTensor, accessAddRatTensorBuiltin, Forced IRatType),
      (accessMulRatTensor, accessMulRatTensorBuiltin, Forced IRatType),
      (accessSubRatTensor, accessSubRatTensorBuiltin, Forced IRatType),
      (accessDivRatTensor, accessDivRatTensorBuiltin, Forced IRatType),
      (accessMinRatTensor, accessMinRatTensorBuiltin, Forced IRatType),
      (accessMaxRatTensor, accessMaxRatTensorBuiltin, Forced IRatType),
      (accessAndTensor, accessAndTensorBuiltin, Forced IBoolType),
      (accessOrTensor, accessOrTensorBuiltin, Forced IBoolType),
      compPointwise Eq,
      compPointwise Ne,
      compPointwise Le,
      compPointwise Lt,
      compPointwise Ge,
      compPointwise Gt
    ]
    where
      compPointwise op = (accessArgsForOp accessCompareRatTensorPointwise op, applyAccessor accessCompareRatTensorPointwiseBuiltin op, Forced IBoolType)

instance NormalisableBuiltin Builtin where
  evaluationScheme = \case
    BuiltinFunction f -> case f of
      CompareIndex op -> StandardEvaluation (evalCompareIndex op)
      CompareNat op -> StandardEvaluation (evalCompareNat op)
      CompareRatTensor op -> StandardEvaluation (evalCompareRatTensor op)
      Not -> StandardEvaluation evalNot
      And -> StandardEvaluation evalAnd
      Or -> StandardEvaluation evalOr
      Add AddNat -> StandardEvaluation evalAddNat
      Mul MulNat -> StandardEvaluation evalMulNat
      Neg NegRatTensor -> StandardEvaluation evalNegRatTensor
      Add AddRatTensor -> StandardEvaluation evalAddRatTensor
      Sub SubRatTensor -> StandardEvaluation evalSubRatTensor
      Mul MulRatTensor -> StandardEvaluation evalMulRatTensor
      Div DivRatTensor -> StandardEvaluation evalDivRatTensor
      Min MinRatTensor -> StandardEvaluation evalMinRatTensor
      Max MaxRatTensor -> StandardEvaluation evalMaxRatTensor
      PowRat -> StandardEvaluation evalPowRat
      ReduceAddRatTensor -> StandardEvaluation evalReduceAddRatTensor
      ReduceMulRatTensor -> StandardEvaluation evalReduceMulRatTensor
      ReduceMinRatTensor -> StandardEvaluation evalReduceMinRatTensor
      ReduceMaxRatTensor -> StandardEvaluation evalReduceMaxRatTensor
      ReduceAndTensor -> StandardEvaluation evalReduceAndTensor
      ReduceOrTensor -> StandardEvaluation evalReduceOrTensor
      If -> StandardEvaluation evalIf
      Implies -> StandardEvaluation evalImplies
      AtVector -> StandardEvaluation evalAtVector
      AtTensor -> StandardEvaluation evalAtTensor
      StackTensor -> StandardEvaluation evalStackTensor
      ConstTensor -> StandardEvaluation evalConstTensor
      FoldList -> StandardEvaluation evalFoldList
      MapList -> StandardEvaluation evalMapList
      ForeachTensor -> StandardEvaluation evalForeachTensor
      ForeachVector -> StandardEvaluation evalForeachVector
      Iterate -> StandardEvaluation evalIterate
      QuantifyRatTensor {} -> Unevaluable
      QuantifyTensorLike {} -> Unevaluable
    BuiltinCast c -> case c of
      FromNat FromNatToNat -> StandardEvaluation evalFromNatToNat
      FromNat FromNatToIndex -> StandardEvaluation evalFromNatToIndex
      FromNat FromNatToRat -> StandardEvaluation evalFromNatToRat
      FromRat FromRatToRat -> StandardEvaluation evalFromRatToRat
      FromVectorToList -> StandardEvaluation evalVectorToList
    DerivedFunction f -> DerivedEvaluation (identifierOf f)
    TypeClassOp {} -> TypeClassEvaluation
    _ -> Unevaluable

  isCast b = case b of
    BuiltinCast {} -> True
    -- Also force stacks to resolve as they are kind of cast.
    BuiltinFunction StackTensor -> True
    _ -> False

  isDerivedBuiltin b = case b of
    DerivedFunction f -> Just $ identifierOf f
    _ -> Nothing

evalFromNatToNat :: (MonadNorm Builtin m) => StandardBuiltinEvaluationScheme FromNatToSimpleArgs Builtin m
evalFromNatToNat (FromNatToSimpleArgs v _) = return $ Evaluated v

evalFromNatToIndex :: (MonadNorm Builtin m) => StandardBuiltinEvaluationScheme FromNatToIndexArgs Builtin m
evalFromNatToIndex (FromNatToIndexArgs d value _) = do
  forcedValue <- forceValue value
  case forcedValue of
    INatLiteral v -> return $ Evaluated $ Forced $ IIndexLiteral v d
    _ -> return $ Unevaluated [forcedValue]

evalFromNatToRat :: (MonadNorm Builtin m) => StandardBuiltinEvaluationScheme FromNatToSimpleArgs Builtin m
evalFromNatToRat (FromNatToSimpleArgs value _) = do
  forcedValue <- forceValue value
  case forcedValue of
    INatLiteral n -> return $ Evaluated $ Forced $ IRatLiteral $ fromIntegral n
    _ -> return $ Unevaluated [forcedValue]

evalFromRatToRat :: (MonadNorm Builtin m) => StandardBuiltinEvaluationScheme Op1Args Builtin m
evalFromRatToRat (Op1Args x) = return $ Evaluated x

evalVectorToList :: (MonadNorm Builtin m) => StandardBuiltinEvaluationScheme VectorToListArgs Builtin m
evalVectorToList (VectorToListArgs t size xs) = do
  forcedSize <- forceValue size
  case forcedSize of
    INatLiteral n | n == length xs -> return $ Evaluated $ mkListExpr t xs
    _ -> return $ Unevaluated [forcedSize]

mkListExpr ::
  (HasListExpr Value Thunk builtin) =>
  Thunk builtin ->
  [Thunk builtin] ->
  Thunk builtin
mkListExpr tElem = foldr (\x xs -> Forced $ ICons tElem x xs) (Forced $ INil tElem)

mkDims ::
  (HasNatExpr Value Thunk builtin, HasListExpr Value Thunk builtin, BuiltinHasNatType builtin) =>
  [Int] ->
  Thunk builtin
mkDims ds = mkListExpr (Forced INatType) (fmap (Forced . INatLiteral) ds)
