{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Data.Builtin.Standard.Normalise where

import Vehicle.Compile.Normalise.BuiltinForced qualified as Forced
import Vehicle.Compile.Normalise.Core qualified as Forced
import Vehicle.Data.Builtin.Core as Syntax
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Blocked
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Real (ExtendedRational (..))
import Vehicle.Prelude (HasIdentifier (identifierOf), developerError)

---------------------------------------------------------------------------------
--- Normalisation

instance (HasBuiltinConstructor expr thunk) => HasTensorLiterals expr Builtin where
  tensorLiterals =
    [ Wrapper accessBoolTensorLiteral,
      Wrapper accessNatTensorLiteral,
      Wrapper accessRatTensorLiteral
    ]

instance (HasBuiltinConstructor expr thunk, NormalisableExpr expr thunk) => HasLiftableTensorOperations expr thunk Builtin where
  liftableTensorOp1s =
    [ (getExpr accessNegRatTensor, evalNegRatTensor, IRatType),
      (getExpr accessNotTensor, evalNot, IBoolType)
    ]

  liftableTensorOp2s =
    [ (getExpr accessAddRatTensor, evalAddRatTensor, IRatType),
      (getExpr accessMulRatTensor, evalMulRatTensor, IRatType),
      (getExpr accessSubRatTensor, evalSubRatTensor, IRatType),
      (getExpr accessDivRatTensor, evalDivRatTensor, IRatType),
      (getExpr accessMinRatTensor, evalMinRatTensor, IRatType),
      (getExpr accessMaxRatTensor, evalMaxRatTensor, IRatType),
      (getExpr accessAndTensor, evalAnd, IBoolType),
      (getExpr accessOrTensor, evalOr, IBoolType),
      compPointwise Eq,
      compPointwise Ne,
      compPointwise Le,
      compPointwise Lt,
      compPointwise Ge,
      compPointwise Gt
    ]
    where
      compPointwise op = (getExpr (accessArgsForOp accessCompareRatTensorPointwise op), evalCompareRatTensorPointwise op, IBoolType)

instance NormalisableBuiltin Builtin where
  evalScheme = \case
    BuiltinFunction f -> case f of
      CompareIndex op -> Simple (evalCompareIndex op)
      CompareNat op -> Simple (evalCompareNat op)
      CompareRatTensorPointwise op -> Simple (evalCompareRatTensorPointwise op)
      Not -> Simple evalNot
      And -> Simple evalAnd
      Or -> Simple evalOr
      Add AddNat -> Simple evalAddNat
      Mul MulNat -> Simple evalMulNat
      Neg NegRatTensor -> Simple evalNegRatTensor
      Add AddRatTensor -> Simple evalAddRatTensor
      Sub SubRatTensor -> Simple evalSubRatTensor
      Mul MulRatTensor -> Simple evalMulRatTensor
      Div DivRatTensor -> Simple evalDivRatTensor
      Min MinRatTensor -> Simple evalMinRatTensor
      Max MaxRatTensor -> Simple evalMaxRatTensor
      Pow PowRatTensor -> Simple evalPowRatTensor
      Log LogRatTensor -> None
      Exp ExpRatTensor -> None
      ReduceAddRatTensor -> Simple evalReduceAddRatTensor
      ReduceMulRatTensor -> Simple evalReduceMulRatTensor
      ReduceMinRatTensor -> Simple evalReduceMinRatTensor
      ReduceMaxRatTensor -> Simple evalReduceMaxRatTensor
      ReduceAndTensor -> NonSimple evalReduceAndTensor
      ReduceOrTensor -> Simple evalReduceOrTensor
      If -> Simple evalIf
      Implies -> Simple evalImplies
      AtVector -> Simple evalAtVector
      AtTensor -> NonSimple evalAtTensor
      StackTensor -> Simple evalStackTensor
      ConstTensor -> Simple evalConstTensor
      FoldList -> NonSimple evalFoldList
      MapList -> NonSimple evalMapList
      ForeachTensor -> NonSimple evalForeachTensor
      ForeachVector -> NonSimple evalForeachVector
      Iterate -> NonSimple evalIterate
      QuantifyRatTensor {} -> None
      QuantifyRecord {} -> None
    BuiltinCast c -> case c of
      FromNat FromNatToNat -> Simple evalFromNatToNat
      FromNat FromNatToIndex -> Simple evalFromNatToIndex
      FromNat FromNatToRat -> Simple evalFromNatToRat
      FromRat FromRatToRat -> Simple evalFromRatToRat
      FromVectorToList -> Simple evalVectorToList
    DerivedFunction f -> Derived (identifierOf f)
    _ -> None

  blockingStatus = \case
    BuiltinFunction f -> functionBlockingStatus f
    BuiltinCast c -> castBlockingStatus c
    DerivedFunction f -> derivedFunctionBlockingStatus f
    _ -> return DoesNotReduce

  isTypeClassOp = \case
    TypeClassOp {} -> True
    _ -> False

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

evalFromNatToNat ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk) =>
  EvalSimple expr thunk FromNatToSimpleArgs Builtin m
evalFromNatToNat (FromNatToSimpleArgs v _) = return $ force v

evalFromNatToIndex ::
  forall m expr thunk.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBuiltinConstructor expr thunk) =>
  EvalSimple expr thunk FromNatToIndexArgs Builtin m
evalFromNatToIndex args@(FromNatToIndexArgs d value _) = do
  let forcedValue = force @expr value
  return $ case forcedValue of
    INatLiteral v -> IIndexLiteral v d
    _ -> mkExpr accessFromNatToIndex args

evalFromNatToRat ::
  forall m expr thunk.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBuiltinConstructor expr thunk) =>
  EvalSimple expr thunk FromNatToSimpleArgs Builtin m
evalFromNatToRat args@(FromNatToSimpleArgs value _) = do
  let forcedValue = force @expr value
  return $ case forcedValue of
    INatLiteral n -> IRatLiteral $ Finite $ fromIntegral n
    _ -> mkExpr accessFromNatToRat args

evalFromRatToRat ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk) =>
  EvalSimple expr thunk Op1Args Builtin m
evalFromRatToRat (Op1Args x) = return $ force x

evalVectorToList ::
  forall expr thunk m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBuiltinConstructor expr thunk) =>
  EvalSimple expr thunk VectorToListArgs Builtin m
evalVectorToList args@(VectorToListArgs t d xs) = do
  let d' = force @expr d
  return $ case d' of
    INatLiteral n | n == length xs -> mkListExpr t xs
    _ -> mkExpr accessFromVectorToList args

---------------------------------------------------------------------------------
--- Forced normalisation

instance Forced.NormalisableBuiltin Builtin where
  evalScheme = \case
    BuiltinFunction f -> case f of
      CompareIndex op -> Forced.Eval (Forced.evalCompareIndex op)
      CompareNat op -> Forced.Eval (Forced.evalCompareNat op)
      CompareRatTensorPointwise op -> Forced.Eval (Forced.evalCompareRatTensorPointwise op)
      Not -> Forced.Eval Forced.evalNot
      And -> Forced.Eval Forced.evalAnd
      Or -> Forced.Eval Forced.evalOr
      Add AddNat -> Forced.Eval Forced.evalAddNat
      Mul MulNat -> Forced.Eval Forced.evalMulNat
      Neg NegRatTensor -> Forced.Eval Forced.evalNegRatTensor
      Add AddRatTensor -> Forced.Eval Forced.evalAddRatTensor
      Sub SubRatTensor -> Forced.Eval Forced.evalSubRatTensor
      Mul MulRatTensor -> Forced.Eval Forced.evalMulRatTensor
      Div DivRatTensor -> Forced.Eval Forced.evalDivRatTensor
      Min MinRatTensor -> Forced.Eval Forced.evalMinRatTensor
      Max MaxRatTensor -> Forced.Eval Forced.evalMaxRatTensor
      Pow PowRatTensor -> Forced.Eval Forced.evalPowRatTensor
      Log LogRatTensor -> Forced.None
      Exp ExpRatTensor -> Forced.None
      ReduceAddRatTensor -> Forced.Eval Forced.evalReduceAddRatTensor
      ReduceMulRatTensor -> Forced.Eval Forced.evalReduceMulRatTensor
      ReduceMinRatTensor -> Forced.Eval Forced.evalReduceMinRatTensor
      ReduceMaxRatTensor -> Forced.Eval Forced.evalReduceMaxRatTensor
      ReduceAndTensor -> Forced.Eval Forced.evalReduceAndTensor
      ReduceOrTensor -> Forced.Eval Forced.evalReduceOrTensor
      If -> Forced.Eval Forced.evalIf
      Implies -> Forced.Eval Forced.evalImplies
      AtVector -> Forced.Eval Forced.evalAtVector
      AtTensor -> Forced.Eval Forced.evalAtTensor
      StackTensor -> Forced.Eval Forced.evalStackTensor
      ConstTensor -> Forced.Eval Forced.evalConstTensor
      FoldList -> Forced.Eval Forced.evalFoldList
      MapList -> Forced.Eval Forced.evalMapList
      ForeachTensor -> Forced.Eval Forced.liftAndEvalForeachTensor
      ForeachVector -> Forced.Eval Forced.evalForeachVector
      Iterate -> Forced.Eval Forced.evalIterate
      QuantifyRatTensor {} -> Forced.None
      QuantifyRecord {} -> Forced.None
    BuiltinCast c -> case c of
      FromNat FromNatToNat -> Forced.Eval forcedEvalFromNatToNat
      FromNat FromNatToIndex -> Forced.Eval forcedEvalFromNatToIndex
      FromNat FromNatToRat -> Forced.Eval forcedEvalFromNatToRat
      FromRat FromRatToRat -> Forced.Eval forcedEvalFromRatToRat
      FromVectorToList -> Forced.Eval forcedEvalVectorToList
    DerivedFunction f -> case f of
      CompareRatTensorReduced {} -> Forced.Eval $ developerError "reduced comparisons should not be evaluated"
      _ -> Forced.Derived (identifierOf f)
    _ -> Forced.None

forcedEvalFromNatToNat ::
  (Forced.MonadNormBuiltin m) =>
  Forced.EvalSimple expr thunk FromNatToSimpleArgs Builtin m
forcedEvalFromNatToNat (FromNatToSimpleArgs v _) = return $ Forced.Evaluated v

forcedEvalFromNatToIndex ::
  forall m expr thunk.
  (Forced.MonadNormBuiltin m, HasBuiltinConstructor expr thunk) =>
  Forced.EvalSimple expr thunk FromNatToIndexArgs Builtin m
forcedEvalFromNatToIndex (FromNatToIndexArgs d value _) = do
  forcedValue <- Forced.force @expr value
  return $ case forcedValue of
    INatLiteral v -> Forced.Evaluated $ exprToThunk $ IIndexLiteral v d
    _ -> Forced.Unevaluable [forcedValue]

forcedEvalFromNatToRat ::
  forall m expr thunk.
  (Forced.MonadNormBuiltin m, HasBuiltinConstructor expr thunk) =>
  Forced.EvalSimple expr thunk FromNatToSimpleArgs Builtin m
forcedEvalFromNatToRat (FromNatToSimpleArgs value _) = do
  forcedValue <- Forced.force @expr value
  return $ case forcedValue of
    INatLiteral n -> Forced.Evaluated $ exprToThunk $ IRatLiteral $ Finite $ fromIntegral n
    _ -> Forced.Unevaluable [forcedValue]

forcedEvalFromRatToRat ::
  (Forced.MonadNormBuiltin m) =>
  Forced.EvalSimple expr thunk Op1Args Builtin m
forcedEvalFromRatToRat (Op1Args x) = return $ Forced.Evaluated x

forcedEvalVectorToList ::
  forall expr thunk m.
  (Forced.MonadNormBuiltin m, HasBuiltinConstructor expr thunk) =>
  Forced.EvalSimple expr thunk VectorToListArgs Builtin m
forcedEvalVectorToList (VectorToListArgs t d xs) = do
  d' <- Forced.force @expr d
  return $ case d' of
    INatLiteral n | n == length xs -> Forced.Evaluated $ exprToThunk $ mkListExpr t xs
    _ -> Forced.Unevaluable [d']

instance (HasBuiltinConstructor expr thunk) => Forced.HasTensorLiterals expr Builtin where
  tensorLiterals =
    [ Forced.Wrapper accessBoolTensorLiteral,
      Forced.Wrapper accessNatTensorLiteral,
      Forced.Wrapper accessRatTensorLiteral
    ]

instance (HasBuiltinConstructor expr thunk) => Forced.HasLiftableTensorOperations expr thunk Builtin where
  liftableTensorOp1s =
    [ (accessNegRatTensor, IRatType),
      (accessNotTensor, IBoolType)
    ]

  liftableTensorOp2s =
    [ (accessAddRatTensor, IRatType),
      (accessMulRatTensor, IRatType),
      (accessSubRatTensor, IRatType),
      (accessDivRatTensor, IRatType),
      (accessMinRatTensor, IRatType),
      (accessMaxRatTensor, IRatType),
      (accessAndTensor, IBoolType),
      (accessOrTensor, IBoolType),
      compPointwise Eq,
      compPointwise Ne,
      compPointwise Le,
      compPointwise Lt,
      compPointwise Ge,
      compPointwise Gt
    ]
    where
      compPointwise op = (accessArgsForOp accessCompareRatTensorPointwise op, IBoolType)
