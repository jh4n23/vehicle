{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
module Vehicle.Data.Builtin.Interface.Normalise where

import Control.Applicative ((<|>))
import Control.Monad (foldM, zipWithM)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromMaybe, isJust)
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Compile.Type.Force
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Print (PrintableBuiltin)
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (Tensor, TensorShape, at, extendTensor, foldTensor, mapTensor, stack, unstack, zipWithTensor, pattern ConstantTensor, pattern ZeroDimTensor)
import Vehicle.Data.Variable.Bound.Context.Name

-- Okay so the important thing to remember about this module is that we have
-- a variety of different typing schemes for builtins (standard, polarity,
-- linearity etc.). Normalisation needs to work for all of these, and
-- therefore we can't guarantee what the implicit and instance arguments are
-- going to be for a given builtin. However, explicit arguments are always
-- the same in every type system.

-- Therefore this can be viewed as a type of runtime irrelevance, where only
-- the explicit arguments are runtime relevant. This notion isn't made
-- explicit in the code below. Maybe there's a nice way of doing so?

-----------------------------------------------------------------------------
-- Main method

type MonadNormBuiltin m = MonadLogger m

type Eval builtin m = NamedBoundCtx -> BoundEnv builtin -> Expr builtin -> m (ForcedExpr builtin)

-- | A method for evaluating an application.
-- Although there is only one implementation of this type, it needs to be
-- passed around as an argument to avoid dependency cycles between
-- this module and the module in which the general NBE algorithm lives in.
type EvalApp builtin m = NamedBoundCtx -> Expr builtin -> ForcibleSpine builtin -> m (ForcedExpr builtin)

type StandardBuiltinEvaluationScheme builtin m =
  NamedBoundCtx ->
  EvalApp builtin m ->
  Eval builtin m ->
  GenericArgs builtin ->
  m (BuiltinEvaluationResult builtin)

data BuiltinEvaluationResult builtin
  = Evaluated (ForcedExpr builtin)
  | Unevaluated (BlockingStatus (ForcedExpr builtin))

data BuiltinEvaluationScheme builtin m
  = StandardEvaluation (StandardBuiltinEvaluationScheme builtin m)
  | DerivedEvaluation Identifier
  | -- The builtin is a type-class operation (should eventually be eliminated)
    TypeClassEvaluation
  | Unevaluable

-- | A type-class for builtins that can be normalised compositionally.
class (PrintableBuiltin builtin) => NormalisableBuiltin builtin where
  evaluationScheme :: (MonadLogger m) => builtin -> BuiltinEvaluationScheme builtin m
  isCast :: (MonadLogger m) => Provenance -> builtin -> Maybe ([Arg builtin] -> m (expr builtin))

type SimpleStandardBuiltinEvaluation args builtin m =
  args (ForcibleExpr builtin) ->
  m (BuiltinEvaluationResult builtin)

simpleEvaluation ::
  (IsArgs args) =>
  SimpleStandardBuiltinEvaluation args builtin m ->
  BuiltinEvaluationScheme builtin m
simpleEvaluation simpleEval = StandardEvaluation $
  \ctx evalApp eval args -> do
    result <- simpleEval _
    case result of
      Left blockingStatus -> return $ Unevaluated blockingStatus
      Right newValue -> return $ Evaluated newValue

-- | A method for evaluating builtins that takes in an argument allowing the
-- recursive evaluation of applications. that takes in an argument allowing
-- the subsequent further evaluation of applications.
-- Such recursive evaluation is necessary when evaluating higher order
-- functions such as fold, map etc.
type EvalComplexBuiltin args expr builtin m =
  (MonadNormBuiltin m) =>
  NamedBoundCtx ->
  EvalApp builtin m ->
  Eval builtin m ->
  args (ForcibleExpr builtin) ->
  m (Maybe (ForcedExpr builtin))

forceEvalSimpleBuiltin ::
  (IsArgs args, MonadLogger m, Pretty builtin, PrintableBuiltin builtin) =>
  Provenance ->
  builtin ->
  SimpleStandardBuiltinEvaluation args builtin m ->
  [GenericArg (Expr builtin)] ->
  m (Expr builtin)
forceEvalSimpleBuiltin p b simpleEval spine =
  case simpleEvaluation simpleEval _ of
    Evaluated args -> eval args
    Unevaluated _ -> return $ normAppList (Builtin p b) spine

evalSimpleOrReturn ::
  (MonadNormBuiltin m, IsArgs args) =>
  Accessor (expr builtin) (args (expr builtin)) ->
  SimpleStandardBuiltinEvaluation args builtin m ->
  args (expr builtin) ->
  m (expr builtin)
evalSimpleOrReturn accessBuiltin evalBuiltin args = do
  maybeResult <- evalBuiltin args
  case maybeResult of
    Unevaluated {} -> return $ mkExpr accessBuiltin args
    Evaluated result -> return result

{-
evalNonSimple ::
  (MonadNormBuiltin m, IsArgs args) =>
  EvalApp Value builtin m ->
  Accessor builtin () ->
  EvalComplexBuiltin args Value builtin m ->
  args (Value builtin) ->
  m (Value builtin)
evalNonSimple evalApp accessBuiltin eval args = do
  maybeResult <- eval evalApp args
  return $ case maybeResult of
    Just result -> result
    Nothing -> VBuiltin (mkExpr accessBuiltin ()) (mkExpr accessSpine args)
-}
--------------------------------------------------------------------------------
-- Blocking

data BlockingStatus expr
  = InsufficientArgs
  | DoesNotReduce
  | Blocked (BlockingArgsTraversal expr)
  | AlwaysReduces

type BlockingArgsTraversal expr = forall m. (Monad m) => (expr -> m expr) -> m [GenericArg expr]

blocked :: (IsArgs args) => NonEmpty Int -> args expr -> BlockingStatus expr
blocked indices spine
  | maximum indices < length spine = Blocked $ traverseArgsAtIndices (NonEmpty.toList indices) 0 spine
  | otherwise = InsufficientArgs

traverseArgsAtIndices ::
  (Monad m) =>
  [Int] ->
  Int ->
  GenericArgs expr ->
  (expr -> m expr) ->
  m (GenericArgs expr)
traverseArgsAtIndices _blockingArgs _currentIndex [] _f = return []
traverseArgsAtIndices [] _currentIndex args _f = return args
traverseArgsAtIndices (blockingIndex : blockingIndices) currentIndex (arg : args) f
  | currentIndex == blockingIndex = do
      arg' <- traverse f arg
      args' <- traverseArgsAtIndices blockingIndices (currentIndex + 1) args f
      return $ arg' : args'
  | otherwise = do
      args' <- traverseArgsAtIndices (blockingIndex : blockingIndices) (currentIndex + 1) args f
      return $ arg : args'

--------------------------------------------------------------------------------
-- Evaluation

evalOp2Args ::
  Accessor (expr builtin) a ->
  Accessor (expr builtin) b ->
  Accessor (expr builtin) c ->
  (a -> b -> c) ->
  SimpleStandardBuiltinEvaluation Op2Args builtin m
evalOp2Args accessArg1 accessArg2 accessRes f args@(Op2Args e1 e2) =
  case (getExpr accessArg1 e1, getExpr accessArg2 e2) of
    (Just a, Just b) -> return $ Evaluated $ mkExpr accessRes (f a b)
    _ -> return $ Unevaluated $ blocked [0, 1] args

evalTensorOp1 ::
  forall expr builtin a m.
  (MonadNormBuiltin m, HasTensorExpr expr builtin, Eq a) =>
  Accessor (expr builtin) (TensorOp1Args (expr builtin)) ->
  Accessor (expr builtin) (Tensor a) ->
  (a -> a) ->
  SimpleStandardBuiltinEvaluation TensorOp1Args builtin m
evalTensorOp1 accessBuiltinOp accessLit op = eval
  where
    eval :: SimpleStandardBuiltinEvaluation TensorOp1Args builtin m
    eval = \case
      TensorOp1Args _ds (getExpr accessLit -> Just t) ->
        return $ Evaluated $ mkExpr accessLit $ mapTensor op t
      TensorOp1Args (IDimCons d _) (getExpr accessConstTensor -> Just xs) ->
        Evaluated . mkExpr accessConstTensor <$> traverseConstTensorValue (evalFull d) xs
      TensorOp1Args (IDimCons d _) (getExpr accessStackTensor -> Just xs) ->
        Evaluated . mkExpr accessStackTensor <$> traverseStackTensorElements (evalFull d) xs
      args -> return $ Unevaluated $ blocked [1] args

    evalFull :: expr builtin -> expr builtin -> m (expr builtin)
    evalFull d x = evalSimpleOrReturn accessBuiltinOp eval (TensorOp1Args d x)

evalTensorOp2 ::
  forall expr builtin a m.
  (MonadNormBuiltin m, HasTensorExpr expr builtin, Eq a) =>
  Accessor (expr builtin) (TensorOp2Args (expr builtin)) ->
  Accessor (expr builtin) (Tensor a) ->
  (a -> a -> a) ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalTensorOp2 accessOp2 accessLit = evalHeteroTensorOp2 accessOp2 accessLit accessLit

evalHeteroTensorOp2 ::
  forall expr builtin a b m.
  (MonadNormBuiltin m, HasTensorExpr expr builtin, Eq a, Eq b) =>
  Accessor (expr builtin) (TensorOp2Args (expr builtin)) ->
  Accessor (expr builtin) (Tensor a) ->
  Accessor (expr builtin) (Tensor b) ->
  (a -> a -> b) ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalHeteroTensorOp2 accessOp2 inputLit outputLit op leftUnit rightUnit leftZero rightZero = eval
  where
    eval :: SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
    eval = \case
      TensorOp2Args _ds (getExpr inputLit -> Just xs) (getExpr inputLit -> Just ys) ->
        return $ Evaluated $ mkExpr outputLit $ zipWithTensor op xs ys
      TensorOp2Args (IDimCons _ ds) (getExpr accessConstTensor -> Just xs) (getExpr accessConstTensor -> Just ys) -> do
        newConstValue <- evalFull ds (constValue xs) (constValue ys)
        return $ Evaluated $ mkExpr accessConstTensor $ xs {constValue = newConstValue}
      -- Unlike const tensors, we need to eval stack tensors as after being combined with constants, short-circuiting of
      -- operations may allow for further reduction.
      TensorOp2Args (IDimCons _ ds) (getExpr inputLit -> Just xs) (getExpr accessStackTensor -> Just ys) -> do
        newElements <- zipWithM (evalFull ds) (unstackExpr xs) (stackElements ys)
        evalStackTensorWithPrimitives [Wrapper outputLit] $ ys {stackElements = newElements}
      TensorOp2Args (IDimCons _ ds) (getExpr accessStackTensor -> Just xs) (getExpr inputLit -> Just ys) -> do
        newElements <- zipWithM (evalFull ds) (stackElements xs) (unstackExpr ys)
        evalStackTensorWithPrimitives [Wrapper outputLit] $ xs {stackElements = newElements}
      TensorOp2Args (IDimCons _ ds) (getExpr accessStackTensor -> Just xs) (getExpr accessStackTensor -> Just ys) -> do
        newElements <- zipWithM (evalFull ds) (stackElements xs) (stackElements ys)
        evalStackTensorWithPrimitives [Wrapper outputLit] $ xs {stackElements = newElements}
      TensorOp2Args _ds xs ys
        | isJust leftUnit && leftUnit == getConstValue xs -> return $ Evaluated ys
      TensorOp2Args _ds xs ys
        | isJust rightUnit && rightUnit == getConstValue ys -> return $ Evaluated xs
      TensorOp2Args _ds xs _ys
        | isJust leftZero && leftZero == getConstValue xs -> return $ Evaluated xs
      TensorOp2Args _ds _xs ys
        | isJust rightZero && rightZero == getConstValue ys -> return $ Evaluated ys
      args -> return $ Unevaluated $ blocked [1, 2] args

    evalFull :: expr builtin -> expr builtin -> expr builtin -> m (expr builtin)
    evalFull d x y = evalSimpleOrReturn accessOp2 eval (TensorOp2Args d x y)

    unstackExpr :: Tensor a -> [expr builtin]
    unstackExpr xs = mkExpr inputLit <$> unstack xs

    getConstValue :: expr builtin -> Maybe a
    getConstValue value = case getExpr inputLit value of
      Just (ConstantTensor _ v) -> Just v
      _ -> case getExpr accessConstTensor value of
        Just constTensor -> getConstValue (constValue constTensor)
        _ -> Nothing

evalReduceTensor ::
  forall expr builtin a m.
  (MonadNormBuiltin m, HasTensorExpr expr builtin, PrintableBuiltin builtin) =>
  Accessor (expr builtin) (TensorReductionArgs (expr builtin)) ->
  Accessor (expr builtin) (TensorOp2Args (expr builtin)) ->
  Accessor (expr builtin) (Tensor a) ->
  SimpleStandardBuiltinEvaluation TensorOp2Args builtin m ->
  (a -> a -> a) ->
  SimpleStandardBuiltinEvaluation TensorReductionArgs builtin m
evalReduceTensor accessReductionOp accessBop accessLit evalOp2 op2 = eval
  where
    eval :: SimpleStandardBuiltinEvaluation TensorReductionArgs builtin m
    eval = \case
      TensorReductionArgs _ (getExpr accessLit -> Just e) (getExpr accessLit -> Just xs) ->
        return $ Evaluated $ mkExpr accessLit $ foldTensor op2 e xs
      TensorReductionArgs (IDimCons _ ds) e (getExpr accessStackTensor -> Just xs) ->
        Evaluated <$> foldM (foldFn e ds) e (stackElements xs)
      TensorReductionArgs IDimNil _e xs ->
        return $ Evaluated xs
      args -> return $ Unevaluated $ blocked [1] args

    evalFull :: expr builtin -> expr builtin -> expr builtin -> m (expr builtin)
    evalFull ds e xs = evalSimpleOrReturn accessReductionOp eval (TensorReductionArgs ds e xs)

    evalBop :: expr builtin -> expr builtin -> expr builtin -> m (expr builtin)
    evalBop ds xs ys = evalSimpleOrReturn accessBop evalOp2 (TensorOp2Args ds xs ys)

    foldFn e ds r y = do
      y' <- evalFull ds e y
      evalBop ds r y'

-----------------------------------------------------------------------------
-- Individual builtin evaluation
-----------------------------------------------------------------------------
-- Not

evalNot :: (MonadNormBuiltin m, HasBoolExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp1Args builtin m
evalNot = evalTensorOp1 accessNotTensor accessBoolTensorLiteral not

-----------------------------------------------------------------------------
-- And

evalAnd :: (MonadNormBuiltin m, HasBoolExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalAnd = evalTensorOp2 accessAndTensor accessBoolTensorLiteral (&&) (Just True) (Just True) (Just False) (Just False)

-----------------------------------------------------------------------------
-- Or

evalOr :: (MonadNormBuiltin m, HasBoolExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalOr = evalTensorOp2 accessOrTensor accessBoolTensorLiteral (||) (Just False) (Just False) (Just True) (Just True)

-----------------------------------------------------------------------------
-- Implies

evalImplies :: (MonadNormBuiltin m, HasBoolExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalImplies (TensorOp2Args ds xs ys) = do
  notXs <- evalSimpleOrReturn accessNotTensor evalNot (TensorOp1Args ds xs)
  Evaluated <$> evalSimpleOrReturn accessOrTensor evalOr (TensorOp2Args ds notXs ys)

-----------------------------------------------------------------------------
-- ReduceAnd

evalReduceAndTensor ::
  (MonadNormBuiltin m, HasBoolExpr expr builtin, PrintableBuiltin builtin) =>
  SimpleStandardBuiltinEvaluation TensorReductionArgs builtin m
evalReduceAndTensor = evalReduceTensor accessReduceAnd accessAndTensor accessBoolTensorLiteral evalAnd (&&)

-----------------------------------------------------------------------------
-- ReduceOr

evalReduceOrTensor ::
  (MonadNormBuiltin m, HasBoolExpr expr builtin, PrintableBuiltin builtin) =>
  SimpleStandardBuiltinEvaluation TensorReductionArgs builtin m
evalReduceOrTensor = evalReduceTensor accessReduceOr accessOrTensor accessBoolTensorLiteral evalOr (||)

-----------------------------------------------------------------------------
-- If

evalIf :: (MonadNormBuiltin m, HasBoolExpr expr builtin) => SimpleStandardBuiltinEvaluation IfArgs builtin m
evalIf args@(IfArgs _t c e1 e2) = case c of
  IBoolLiteral True -> return $ Evaluated e1
  IBoolLiteral False -> return $ Evaluated e2
  _ -> return $ Unevaluated $ blocked [1] args

-----------------------------------------------------------------------------
-- Index

evalCompareIndex ::
  (MonadNormBuiltin m, HasBoolExpr expr builtin, BuiltinHasIndexLiterals builtin) =>
  ComparisonOp ->
  SimpleStandardBuiltinEvaluation IndexComparisonArgs builtin m
evalCompareIndex op = \case
  IndexCompArgs _ _ (IIndexLiteral x _) (IIndexLiteral y _) -> return $ Evaluated $ IBoolLiteral (comparisonOp op x y)
  args -> return $ Unevaluated $ blocked [2, 3] args

-----------------------------------------------------------------------------
-- Nat

evalAddNat ::
  (MonadNormBuiltin m, HasNatExpr expr builtin) =>
  SimpleStandardBuiltinEvaluation Op2Args builtin m
evalAddNat = evalOp2Args accessNatLiteral accessNatLiteral accessNatLiteral (+)

evalMulNat ::
  (MonadNormBuiltin m, HasNatExpr expr builtin) =>
  SimpleStandardBuiltinEvaluation Op2Args builtin m
evalMulNat = evalOp2Args accessNatLiteral accessNatLiteral accessNatLiteral (*)

evalCompareNat ::
  (MonadNormBuiltin m, HasBoolExpr expr builtin, BuiltinHasNatLiterals builtin) =>
  ComparisonOp ->
  SimpleStandardBuiltinEvaluation Op2Args builtin m
evalCompareNat op = evalOp2Args accessNatLiteral accessNatLiteral accessBoolTensorLiteral (\x y -> ZeroDimTensor $ comparisonOp op x y)

-----------------------------------------------------------------------------
-- List

evalMapList ::
  forall expr builtin m.
  (MonadLogger m, HasListExpr expr builtin) =>
  NamedBoundCtx ->
  EvalApp builtin m ->
  Eval builtin m ->
  MapListArgs (expr builtin) ->
  m (expr builtin)
evalMapList ctx evalApp eval (MapListArgs a b f xs) = evalList xs
  where
    evalList :: expr builtin -> m (expr builtin)
    evalList = \case
      INil _ -> return $ INil b
      ICons _ v vs -> do
        v' <- evalApp ctx f [explicit v]
        vs' <- evalMapList ctx evalApp eval (recArgs vs)
        return $ ICons b v' vs'
      vs -> return $ mkExpr accessMapList (recArgs vs)

    recArgs :: expr builtin -> MapListArgs (expr builtin)
    recArgs = MapListArgs a b f

evalFoldList ::
  forall m expr builtin.
  (MonadLogger m, HasListExpr expr builtin) =>
  NamedBoundCtx ->
  EvalApp builtin m ->
  Eval builtin m ->
  FoldListArgs (expr builtin) ->
  m (expr builtin)
evalFoldList ctx evalApp eval (FoldListArgs a b f e xs) = evalList xs
  where
    evalList :: expr builtin -> m (expr builtin)
    evalList = \case
      INil _ -> return e
      ICons _ v vs -> do
        r <- evalFoldList ctx evalApp eval (recArgs vs)
        evalApp ctx f [explicit v, explicit r]
      vs -> return $ mkExpr accessFoldList (recArgs vs)

    recArgs :: expr builtin -> FoldListArgs (expr builtin)
    recArgs = FoldListArgs a b f e

-----------------------------------------------------------------------------
-- Rational tensors

evalNegRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp1Args builtin m
evalNegRatTensor = evalTensorOp1 accessNegRatTensor accessRatTensorLiteral (\x -> -x)

evalAddRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalAddRatTensor = evalTensorOp2 accessAddRatTensor accessRatTensorLiteral (+) (Just 0) (Just 0) Nothing Nothing

evalMulRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalMulRatTensor = evalTensorOp2 accessMulRatTensor accessRatTensorLiteral (*) (Just 1) (Just 1) (Just 0) (Just 0)

evalSubRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalSubRatTensor = evalTensorOp2 accessSubRatTensor accessRatTensorLiteral (-) Nothing (Just 0) Nothing Nothing

evalDivRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalDivRatTensor args = evalTensorOp2 accessDivRatTensor accessRatTensorLiteral (/) Nothing (Just 1) Nothing Nothing args

evalMinRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalMinRatTensor = evalTensorOp2 accessMinRatTensor accessRatTensorLiteral min Nothing Nothing Nothing Nothing

evalMaxRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin) => SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalMaxRatTensor = evalTensorOp2 accessMaxRatTensor accessRatTensorLiteral max Nothing Nothing Nothing Nothing

evalPowRat ::
  (MonadNormBuiltin m, HasRatExpr expr builtin, BuiltinHasNatLiterals builtin) =>
  SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalPowRat = \case
  TensorOp2Args _ (IRatTensor xs) (INatLiteral n) -> return $ Evaluated $ IRatTensor (mapTensor (^^ n) xs)
  args -> return $ Unevaluated $ blocked [0, 1] args

evalReduceAddRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin, PrintableBuiltin builtin) => SimpleStandardBuiltinEvaluation TensorReductionArgs builtin m
evalReduceAddRatTensor = evalReduceTensor accessReduceAddRat accessAddRatTensor accessRatTensorLiteral evalAddRatTensor (+)

evalReduceMulRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin, PrintableBuiltin builtin) => SimpleStandardBuiltinEvaluation TensorReductionArgs builtin m
evalReduceMulRatTensor = evalReduceTensor accessReduceMulRat accessMulRatTensor accessRatTensorLiteral evalMulRatTensor (*)

evalReduceMinRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin, PrintableBuiltin builtin) => SimpleStandardBuiltinEvaluation TensorReductionArgs builtin m
evalReduceMinRatTensor = evalReduceTensor accessReduceMinRat accessMinRatTensor accessRatTensorLiteral evalMinRatTensor min

evalReduceMaxRatTensor :: (MonadNormBuiltin m, HasRatExpr expr builtin, PrintableBuiltin builtin) => SimpleStandardBuiltinEvaluation TensorReductionArgs builtin m
evalReduceMaxRatTensor = evalReduceTensor accessReduceMaxRat accessMaxRatTensor accessRatTensorLiteral evalMaxRatTensor max

evalCompareRatTensorPointwise ::
  (MonadNormBuiltin m, HasBoolExpr expr builtin, HasRatExpr expr builtin, PrintableBuiltin builtin) =>
  ComparisonOp ->
  SimpleStandardBuiltinEvaluation TensorOp2Args builtin m
evalCompareRatTensorPointwise op =
  evalHeteroTensorOp2
    (mkExpr accessCompareRatTensorPointwiseBuiltin op)
    accessRatTensorLiteral
    accessBoolTensorLiteral
    (comparisonOp op)
    Nothing
    Nothing
    Nothing
    Nothing

-----------------------------------------------------------------------------
-- Generic vector operations

evalAtVector ::
  forall expr builtin m.
  (MonadNormBuiltin m, BuiltinHasIndexLiterals builtin, HasVectorExpr expr builtin) =>
  SimpleStandardBuiltinEvaluation AtVectorArgs builtin m
evalAtVector args@(AtVectorArgs _t _d vector index) = case (vector, index) of
  (IVecLiteral _t _d xs, IIndexLiteral i _) -> return $ Evaluated $ xs !! i
  _ -> return $ Unevaluated $ blocked [2, 3] args

-----------------------------------------------------------------------------
-- Generic tensor operations
-----------------------------------------------------------------------------

type TensorOpEvalData args expr builtin m =
  ( Accessor (expr builtin) (args (expr builtin)),
    SimpleStandardBuiltinEvaluation args builtin m,
    VType builtin
  )

class HasLiftableTensorOperations expr builtin where
  liftableTensorOp1s :: (MonadNormBuiltin m) => [TensorOpEvalData TensorOp1Args expr builtin m]
  liftableTensorOp2s :: (MonadNormBuiltin m) => [TensorOpEvalData TensorOp2Args expr builtin m]

data TensorLiteralAccessor expr builtin
  = forall a. (Eq a) => Wrapper (Accessor (expr builtin) (Tensor a))

class HasTensorLiterals expr builtin where
  tensorLiterals :: [TensorLiteralAccessor expr builtin]

-----------------------------------------------------------------------------
-- At

-- | An optimised evaluation procedure for `At` that attempts to minimise the
-- amount of work needed by deferring evaluation of operations until after indexing.
-- For example `(xs + ys) ! i` becomes `xs ! i + ys ! i`.
evalAtTensor ::
  forall expr builtin m.
  (MonadNormBuiltin m, HasTensorLiterals expr builtin, HasLiftableTensorOperations expr builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr expr builtin, BuiltinHasForeach builtin) =>
  NamedBoundCtx ->
  EvalApp builtin m ->
  Eval builtin m ->
  SimpleStandardBuiltinEvaluation AtTensorArgs builtin m
evalAtTensor ctx evalApp eval args@(AtTensorArgs t d ds tensor index) = do
  maybeOptimisedResult <- goOp1 liftableTensorOp1s <|> goOp2 liftableTensorOp2s <|> goForeach
  case maybeOptimisedResult of
    Just result -> return $ Evaluated result
    Nothing -> unoptimisedEvalAtTensor args
  where
    recEvalAt :: expr builtin -> m (expr builtin)
    recEvalAt ys = evalSimpleOrReturn accessAtTensor (evalAtTensor ctx evalApp eval) (AtTensorArgs t d ds ys index)

    goOp1 :: [TensorOpEvalData TensorOp1Args expr builtin m] -> m (Maybe (expr builtin))
    goOp1 = \case
      (accessOp1, evalOp1, _) : remainingOp1s -> case getExpr accessOp1 tensor of
        Just (TensorOp1Args _ xs) -> do
          xsi <- recEvalAt xs
          Just <$> evalSimpleOrReturn accessOp1 evalOp1 (TensorOp1Args ds xsi)
        _ -> goOp1 remainingOp1s
      [] -> return Nothing

    goOp2 :: [TensorOpEvalData TensorOp2Args expr builtin m] -> m (Maybe (expr builtin))
    goOp2 = \case
      (accessOp2, evalOp2, _) : remainingOps2 -> case getExpr accessOp2 tensor of
        Just (TensorOp2Args _ xs ys) -> do
          xsi <- recEvalAt xs
          ysi <- recEvalAt ys
          Just <$> evalSimpleOrReturn accessOp2 evalOp2 (TensorOp2Args ds xsi ysi)
        _ -> goOp2 remainingOps2
      _ -> return Nothing

    goForeach :: m (Maybe (expr builtin))
    goForeach = case getExpr accessForeachTensor tensor of
      Just (ForeachTensorArgs _ _ _ fn) -> do
        Just <$> evalApp ctx fn [explicit index]
      _ -> return Nothing

unoptimisedEvalAtTensor ::
  forall expr builtin m.
  (MonadNormBuiltin m, HasTensorLiterals expr builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr expr builtin) =>
  SimpleStandardBuiltinEvaluation AtTensorArgs builtin m
unoptimisedEvalAtTensor args@(AtTensorArgs _t _d ds tensor index) = do
  case (index, tensor) of
    (IIndexLiteral i _, getExpr accessStackTensor -> Just stackArgs) ->
      return $ Evaluated $ stackElements stackArgs !! i
    (IIndexLiteral _i _, getExpr accessConstTensor -> Just constArgs) ->
      return $ Evaluated $ mkExpr accessConstTensor $ constArgs {constDims = ds}
    _ -> goLiterals tensorLiterals
  where
    goLiterals :: [TensorLiteralAccessor expr builtin] -> m (BuiltinEvaluationResult builtin)
    goLiterals literals = case literals of
      Wrapper Access {..} : remainingLiterals -> case (index, getExpr tensor) of
        (IIndexLiteral i, Just xs) -> return $ Evaluated $ mkExpr (xs `at` i)
        _ -> goLiterals remainingLiterals
      _ -> return $ Unevaluated $ blocked [3, 4] args

-----------------------------------------------------------------------------
-- Foreach

type HasOptimisedAtBuiltins expr builtin =
  ( HasTensorLiterals expr builtin,
    HasLiftableTensorOperations expr builtin,
    NormalisableBuiltin builtin,
    BuiltinHasListLiterals builtin,
    BuiltinHasNatType builtin,
    BuiltinHasNatLiterals builtin,
    BuiltinHasIndexLiterals builtin,
    BuiltinHasTensors builtin,
    BuiltinHasForeach builtin
  )

unoptimisedEvalForeachTensor ::
  (MonadLogger m, HasTensorLiterals expr builtin, HasTensorExpr expr builtin, BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  NamedBoundCtx ->
  EvalApp builtin m ->
  ForeachTensorArgs (expr builtin) ->
  m (BuiltinEvaluationResult builtin)
unoptimisedEvalForeachTensor ctx evalApp args@(ForeachTensorArgs t d ds f) = case d of
  INatLiteral n -> do
    xs <- traverse (\i -> evalApp ctx f [explicit (IIndexLiteral i d)]) [0 .. (n - 1 :: Int)]
    Evaluated <$> evalSimpleOrReturn (mkExpr accessStackTensorBuiltin ()) evalStackTensor (StackTensorArgs t d ds xs)
  _ -> return $ Unevaluated $ blocked [1] args

-----------------------------------------------------------------------------
-- Stack

evalStackTensor ::
  (MonadNormBuiltin m, HasTensorLiterals expr builtin, BuiltinHasNatLiterals builtin, HasTensorExpr expr builtin) =>
  SimpleStandardBuiltinEvaluation StackTensorArgs builtin m
evalStackTensor = evalStackTensorWithPrimitives tensorLiterals

evalStackTensorWithPrimitives ::
  forall m builtin expr.
  (MonadNormBuiltin m, BuiltinHasNatLiterals builtin, HasTensorExpr expr builtin) =>
  [TensorLiteralAccessor expr builtin] ->
  SimpleStandardBuiltinEvaluation StackTensorArgs builtin m
evalStackTensorWithPrimitives tensorLits args@(StackTensorArgs _t d ds xs) = do
  case (d, getDims ds) of
    (INatLiteral n, Just ns) | length xs == n -> go ns xs tensorLits
    _ -> return $ Unevaluated $ blocked [1, 2] args
  where
    go :: TensorShape -> [expr builtin] -> [TensorLiteralAccessor expr builtin] -> m (BuiltinEvaluationResult builtin)
    go elemDims elements = \case
      Wrapper Access {..} : prims ->
        case traverse getExpr elements of
          Just xss -> return $ Evaluated $ mkExpr $ stack elemDims xss
          Nothing -> go elemDims elements prims
      [] -> return $ Unevaluated $ blocked [3, 3 + length elements] args

-----------------------------------------------------------------------------
-- Const

evalConstTensor ::
  forall expr builtin m.
  (MonadNormBuiltin m, HasTensorLiterals expr builtin, BuiltinHasNatLiterals builtin, HasTensorExpr expr builtin) =>
  SimpleStandardBuiltinEvaluation ConstTensorArgs builtin m
evalConstTensor args@(ConstTensorArgs _t xs ds) =
  -- Pattern matching on ds here is technically a bug as blocking will not
  -- function correctly. However, to fix it we would need to go via `StackTensor`
  -- and in particular make `StackTensor` take the size argument as an expression.
  -- Our type-system can't handle that easily yet.
  case (`go` tensorLiterals) =<< getDims ds of
    Just result -> return $ Evaluated result
    _ -> return $ Unevaluated $ blocked [1, 2] args
  where
    go :: [Int] -> [TensorLiteralAccessor expr builtin] -> Maybe (expr builtin)
    go dims = \case
      [] -> Nothing
      Wrapper Access {..} : prims -> case getExpr xs of
        Just t -> case t of
          ZeroDimTensor v -> Just $ mkExpr $ ConstantTensor dims v
          _ -> developerError "Non-zero dimensional tensor argument for ConstTensor"
        Nothing -> go dims prims

evalForeachVector ::
  (MonadLogger m, HasTensorLiterals expr builtin, HasVectorExpr expr builtin, BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  NamedBoundCtx ->
  EvalApp builtin m ->
  Eval builtin m ->
  ForeachVectorArgs (expr builtin) ->
  m (expr builtin)
evalForeachVector ctx evalApp _eval args@(ForeachVectorArgs t d f) = case d of
  INatLiteral n -> do
    xs <- traverse (\i -> evalApp ctx f [explicit (IIndexLiteral i d)]) [0 .. (n - 1 :: Int)]
    return $ IVecLiteral t d xs
  _ -> return $ mkExpr accessForeachVector args

evalIterate ::
  (MonadLogger m, HasNatExpr expr builtin, BuiltinHasIterate builtin) =>
  NamedBoundCtx ->
  EvalApp builtin m ->
  Eval builtin m ->
  IterateArgs (expr builtin) ->
  m (expr builtin)
evalIterate ctx evalApp _eval args@(IterateArgs t f n e) = case n of
  INatLiteral 0 -> return e
  INatLiteral v -> do
    let recFn = mkBuiltin accessIterateBuiltin () [t, explicit f, explicit (INatLiteral (v - 1))]
    evalApp ctx f [explicit recFn, explicit e]
  _ -> return $ mkExpr accessIterate args

-----------------------------------------------------------------------------
-- Logging

showFusionEntry :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> expr builtin -> m ()
showFusionEntry _ctx _expr = return ()

showFusionExit :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> expr builtin -> m (expr builtin)
showFusionExit _ctx result = return result

{-
showFusionEntry :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> expr builtin -> m ()
showFusionEntry ctx expr = do
  logDebug MidDetail $ "fusion-entry" <+> prettyFriendly (WithContext expr ctx)
  -- logDebug MidDetail $ "nbe-entry" <+> prettyFriendly (WithContext expr (boundEnvToCtx boundEnv)) <+> "   { boundEnv =" <+> prettyFriendly boundEnv <+> "}"
  -- logDebug MidDetail $ "nbe-entry" <+> prettyVerbose expr -- <+> "   { boundEnv=" <+> prettyVerbose boundEnv <+> "}"
  incrCallDepth
  return ()

showFusionExit :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> expr builtin -> m (expr builtin)
showFusionExit ctx result = do
  decrCallDepth
  -- logDebug MidDetail $ "nbe-exit" <+> prettyVerbose result
  logDebug MidDetail $ "fusion-exit" <+> prettyFriendly (WithContext result ctx)
  return result
-}

fusionEnter ::
  (MonadLogger m, PrintableBuiltin builtin) =>
  NamedBoundCtx ->
  expr builtin ->
  m ()
fusionEnter _ctx _value = return ()

fusionExit ::
  (MonadLogger m, PrintableBuiltin builtin) =>
  NamedBoundCtx ->
  Maybe (VDims builtin, expr builtin) ->
  m (Maybe (VDims builtin, expr builtin))
fusionExit _ctx result = return result

{-
fusionEnter :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> expr builtin -> m ()
fusionEnter ctx value = do
  logDebug MaxDetail $ "fusion-enter" <+> prettyFriendly (WithContext value ctx)
  incrCallDepth

fusionExit :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> Maybe (VArg builtin, expr builtin) -> m (Maybe (VArg builtin, expr builtin))
fusionExit ctx result = do
  decrCallDepth
  logDebug MaxDetail $
    "fusion-exit" <+> case result of
      Nothing -> ""
      Just (dims, value) -> prettyFriendly (WithContext value ctx) <+> parens (prettyFriendly (WithContext (argExpr dims) ctx))
  return result-}
