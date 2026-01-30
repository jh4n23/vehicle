{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Data.Builtin.Standard.Normalise
  ( foldReduceAndComparison,
  )
where

import Vehicle.Data.Builtin.Core as Syntax
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Prelude (GenericArg (..), HasIdentifier (identifierOf))

---------------------------------------------------------------------------------
--- Normalisation

instance (HasBuiltinConstructor expr) => HasTensorLiterals expr Builtin where
  tensorLiterals =
    [ Wrapper accessBoolTensorLiteral,
      Wrapper accessNatTensorLiteral,
      Wrapper accessRatTensorLiteral
    ]

instance (HasBuiltinConstructor expr) => HasLiftableTensorOperations expr Builtin where
  liftableTensorOp1s =
    [ (accessNegRatTensor, evalNegRatTensor, IRatType),
      (accessNotTensor, evalNot, IBoolType)
    ]

  liftableTensorOp2s =
    [ (accessAddRatTensor, evalAddRatTensor, IRatType),
      (accessMulRatTensor, evalMulRatTensor, IRatType),
      (accessSubRatTensor, evalSubRatTensor, IRatType),
      (accessDivRatTensor, evalDivRatTensor, IRatType),
      (accessMinRatTensor, evalMinRatTensor, IRatType),
      (accessMaxRatTensor, evalMaxRatTensor, IRatType),
      (accessAndTensor, evalAnd, IBoolType),
      (accessOrTensor, evalOr, IBoolType),
      compPointwise Eq,
      compPointwise Ne,
      compPointwise Le,
      compPointwise Lt,
      compPointwise Ge,
      compPointwise Gt
    ]
    where
      compPointwise op = (accessArgsForOp accessCompareRatTensorPointwise op, evalCompareRatTensorPointwise op, IBoolType)

instance NormalisableBuiltin expr Builtin where
  evaluationScheme = \case
    BuiltinFunction f -> case f of
      CompareIndex op -> simpleEvaluation (evalCompareIndex op)
      CompareNat op -> simpleEvaluation (evalCompareNat op)
      CompareRatTensorPointwise op -> simpleEvaluation (evalCompareRatTensorPointwise op)
      Not -> simpleEvaluation evalNot
      And -> simpleEvaluation evalAnd
      Or -> simpleEvaluation evalOr
      Add AddNat -> simpleEvaluation evalAddNat
      Mul MulNat -> simpleEvaluation evalMulNat
      Neg NegRatTensor -> simpleEvaluation evalNegRatTensor
      Add AddRatTensor -> simpleEvaluation evalAddRatTensor
      Sub SubRatTensor -> simpleEvaluation evalSubRatTensor
      Mul MulRatTensor -> simpleEvaluation evalMulRatTensor
      Div DivRatTensor -> simpleEvaluation evalDivRatTensor
      Min MinRatTensor -> simpleEvaluation evalMinRatTensor
      Max MaxRatTensor -> simpleEvaluation evalMaxRatTensor
      PowRat -> simpleEvaluation evalPowRat
      ReduceAddRatTensor -> simpleEvaluation evalReduceAddRatTensor
      ReduceMulRatTensor -> simpleEvaluation evalReduceMulRatTensor
      ReduceMinRatTensor -> simpleEvaluation evalReduceMinRatTensor
      ReduceMaxRatTensor -> simpleEvaluation evalReduceMaxRatTensor
      ReduceAndTensor -> StandardEvaluation evalReduceAndTensor
      ReduceOrTensor -> simpleEvaluation evalReduceOrTensor
      If -> simpleEvaluation evalIf
      Implies -> simpleEvaluation evalImplies
      AtVector -> simpleEvaluation evalAtVector
      AtTensor -> StandardEvaluation evalAtTensor
      StackTensor -> simpleEvaluation evalStackTensor
      ConstTensor -> simpleEvaluation evalConstTensor
      FoldList -> StandardEvaluation evalFoldList
      MapList -> StandardEvaluation evalMapList
      ForeachTensor -> StandardEvaluation evalForeachTensor
      ForeachVector -> StandardEvaluation evalForeachVector
      Iterate -> StandardEvaluation evalIterate
      QuantifyRatTensor {} -> Unevaluable
      QuantifyTensorLike {} -> Unevaluable
    BuiltinCast c -> case c of
      FromNat FromNatToNat -> simpleEvaluation evalFromNatToNat
      FromNat FromNatToIndex -> simpleEvaluation evalFromNatToIndex
      FromNat FromNatToRat -> simpleEvaluation evalFromNatToRat
      FromRat FromRatToRat -> simpleEvaluation evalFromRatToRat
      FromVectorToList -> simpleEvaluation evalVectorToList
    DerivedFunction f -> DerivedEvaluation (identifierOf f)
    TypeClassOp {} -> TypeClassEvaluation
    _ -> Unevaluable

  isCast p b = case b of
    BuiltinCast c -> Just $ case c of
      FromNat FromNatToNat -> forceEvalSimpleBuiltin p b evalFromNatToNat
      FromNat FromNatToIndex -> forceEvalSimpleBuiltin p b evalFromNatToIndex
      FromNat FromNatToRat -> forceEvalSimpleBuiltin p b evalFromNatToRat
      FromRat FromRatToRat -> forceEvalSimpleBuiltin p b evalFromRatToRat
      FromVectorToList -> forceEvalSimpleBuiltin p b evalVectorToList
    BuiltinFunction StackTensor ->
      Just $
        -- Also force stacks to resolve as they are kind of cast.
        forceEvalSimpleBuiltin p b evalStackTensor
    _ -> Nothing

evalFromNatToNat :: (MonadNormBuiltin m) => SimpleStandardBuiltinEvaluation FromNatToSimpleArgs expr Builtin m
evalFromNatToNat (FromNatToSimpleArgs v _) = return $ Right v

evalFromNatToIndex :: (MonadNormBuiltin m, HasBuiltinConstructor expr) => SimpleStandardBuiltinEvaluation FromNatToIndexArgs expr Builtin m
evalFromNatToIndex args = case args of
  FromNatToIndexArgs d (INatLiteral v) _ -> return $ Right $ IIndexLiteral v d
  _ -> return $ Left $ blocked [1] args

evalFromNatToRat :: (MonadNormBuiltin m, HasBuiltinConstructor expr) => SimpleStandardBuiltinEvaluation FromNatToSimpleArgs expr Builtin m
evalFromNatToRat args = case args of
  FromNatToSimpleArgs (INatLiteral n) _ -> return $ Right $ IRatLiteral $ fromIntegral n
  _ -> return $ Left $ blocked [0] args

evalFromRatToRat :: (MonadNormBuiltin m) => SimpleStandardBuiltinEvaluation Op1Args expr Builtin m
evalFromRatToRat (Op1Args x) = return $ Right x

evalVectorToList :: (MonadNormBuiltin m, HasBuiltinConstructor expr) => SimpleStandardBuiltinEvaluation VectorToListArgs expr Builtin m
evalVectorToList args@(VectorToListArgs t d xs) =
  case argExpr d of
    INatLiteral n | n == length xs -> return $ Right $ mkListExpr (argExpr t) xs
    _ -> return $ Left $ blocked [1] args

foldReduceAndComparison ::
  TensorReductionArgs (Value Builtin) ->
  Maybe (Value Builtin)
foldReduceAndComparison (TensorReductionArgs _ unit tensor) =
  case (unit, getExpr accessCompareRatTensorPointwise tensor) of
    (IBoolLiteral True, Just (op, TensorOp2Args (IDimCons d ds) xs ys)) | op /= Ne -> do
      let compareArgs = TensorReduceComparisonArgs d ds xs ys
      Just $ mkExpr accessCompareRatTensorReduced (op, compareArgs)
    _ -> Nothing
