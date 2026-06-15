module Vehicle.Compile.Normalise.BuiltinForced where

import Control.Applicative ((<|>))
import Control.Monad (foldM, zipWithM)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Foldable (asum)
import Data.Maybe (isJust)
import Data.Ratio
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Core.BasicOperations (ComparisonOp, comparisonOp)
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Print (PrintableBuiltin)
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Code.Interface
import Vehicle.Data.Real (ExtendedRational (..))
import Vehicle.Data.Tensor
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

-- | A method for evaluating an application.
-- Although there is only one implementation of this type, it needs to be
-- passed around as an argument to avoid dependency cycles between
-- this module and the module in which the general NBE algorithm lives in.
type EvalApp expr thunk builtin m =
  NamedBoundCtx ->
  thunk builtin ->
  [GenericArg (thunk builtin)] ->
  m (expr builtin)

type Eval expr builtin m =
  NamedBoundCtx ->
  BoundEnv builtin ->
  Expr builtin ->
  m (expr builtin)

{-
tryTensorLiterals ::
  HasTensorLiterals expr builtin =>
  (Accessor (expr builtin) (Tensor a) -> Maybe b) ->
  expr builtin ->
  Maybe b
tryTensorLiterals f = go tensorLiterals
  where
    go :: [TensorLiteralAccessor expr builtin] -> Maybe a
    go = \case
      Wrapper accessor : prims ->
        case f accessor of
          Just xss -> Just $ mkExpr $ stack elemDims xss
          Nothing -> Nothing
      [] -> Nothing
-}
forceEvaluation ::
  forall expr thunk builtin args m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk builtin m) =>
  Accessor (expr builtin) (args (thunk builtin)) ->
  EvalSimple expr thunk args builtin m ->
  args (thunk builtin) ->
  m (thunk builtin)
forceEvaluation accessOp evalFn args = do
  -- This is a total cludge and we may need to plum the whole monad through `ConstantLike`...
  evalResult <- evalFn args
  return $ case evalResult of
    Evaluated result -> result
    Unevaluable {} -> exprToThunk $ mkExpr accessOp args

--------------------------------------------------------------------------------
-- Evaluation

type EvalSimple expr thunk args builtin m =
  ( HasBuiltinConstructor expr thunk,
    NormalisableExpr expr thunk builtin m
  ) =>
  args (thunk builtin) ->
  m (BuiltinEvaluationResult expr thunk builtin)

type EvalSimplePartial expr thunk args builtin m =
  args (thunk builtin) ->
  Maybe (m (expr builtin))

evalTensorOp1 ::
  forall expr thunk builtin a m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk builtin m, HasTensorExpr expr thunk builtin, Eq a) =>
  Accessor (expr builtin) (TensorOp1Args (thunk builtin)) ->
  Accessor (expr builtin) (Tensor a) ->
  (a -> a) ->
  EvalSimple expr thunk TensorOp1Args builtin m
evalTensorOp1 accessOp accessLit op = go
  where
    go :: EvalSimple expr thunk TensorOp1Args builtin m
    go (TensorOp1Args vds vxs) = do
      ds' <- force vds
      xs' <- force vxs
      case (ds', xs') of
        (_ds, getExpr accessLit -> Just t) ->
          return $ Evaluated $ exprToThunk $ mkExpr accessLit $ mapTensor op t
        (IDimCons _ ds, getExpr accessConstTensor -> Just xs) -> do
          xs'' <- traverseConstTensorValue (evalFull ds) xs
          return $ Evaluated $ exprToThunk $ mkExpr accessConstTensor xs''
        (IDimCons _ ds, getExpr accessStackTensor -> Just xs) -> do
          xs'' <- traverseStackTensorElements (evalFull ds) xs
          return $ Evaluated $ exprToThunk $ mkExpr accessStackTensor xs''
        _ -> return $ Unevaluable [ds', xs']

    evalFull :: thunk builtin -> thunk builtin -> m (thunk builtin)
    evalFull ds x = forceEvaluation accessOp go $ TensorOp1Args ds x

evalTensorOp2 ::
  forall expr thunk builtin a m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk builtin m, HasTensorExpr expr thunk builtin, Eq a) =>
  Accessor (expr builtin) (TensorOp2Args (thunk builtin)) ->
  Accessor (expr builtin) (Tensor a) ->
  (a -> a -> a) ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  EvalSimple expr thunk TensorOp2Args builtin m
evalTensorOp2 accessOp2 accessLit =
  evalHeteroTensorOp2 accessOp2 accessLit accessLit

evalHeteroTensorOp2 ::
  forall expr thunk builtin a b m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk builtin m, HasTensorExpr expr thunk builtin, Eq a, Eq b) =>
  Accessor (expr builtin) (TensorOp2Args (thunk builtin)) ->
  Accessor (expr builtin) (Tensor a) ->
  Accessor (expr builtin) (Tensor b) ->
  (a -> a -> b) ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  EvalSimple expr thunk TensorOp2Args builtin m
evalHeteroTensorOp2 accessOp2 inputLit outputLit op leftUnit rightUnit leftZero rightZero = go
  where
    go :: EvalSimple expr thunk TensorOp2Args builtin m
    go (TensorOp2Args vds vxs vys) = do
      fds <- force @expr vds
      fxs <- force @expr vxs
      fys <- force @expr vys
      case (fds, fxs, fys) of
        (_ds, getExpr inputLit -> Just xs, getExpr inputLit -> Just ys) -> do
          return $ Evaluated $ exprToThunk $ mkExpr outputLit $ zipWithTensor op xs ys
        (IDimCons _ ds, getExpr accessConstTensor -> Just xs, getExpr accessConstTensor -> Just ys) -> do
          newConstValue <- evalFull ds (constValue xs) (constValue ys)
          return $ Evaluated $ exprToThunk $ mkExpr accessConstTensor $ xs {constValue = newConstValue}
        -- Unlike const tensors, we need to eval stack tensors as after being combined with constants, short-circuiting of
        -- operations may allow for further reduction.
        (IDimCons _ ds, getExpr inputLit -> Just xs, getExpr accessStackTensor -> Just ys) -> do
          newElements <- zipWithM (evalFull ds) (unstackExpr xs) (stackElements ys)
          return $ Evaluated $ exprToThunk $ mkExpr accessStackTensor $ ys {stackElements = newElements}
        (IDimCons _ ds, getExpr accessStackTensor -> Just xs, getExpr inputLit -> Just ys) -> do
          newElements <- zipWithM (evalFull ds) (stackElements xs) (unstackExpr ys)
          return $ Evaluated $ exprToThunk $ mkExpr accessStackTensor $ xs {stackElements = newElements}
        (IDimCons _ ds, getExpr accessStackTensor -> Just xs, getExpr accessStackTensor -> Just ys) -> do
          newElements <- zipWithM (evalFull ds) (stackElements xs) (stackElements ys)
          return $ Evaluated $ exprToThunk $ mkExpr accessStackTensor $ xs {stackElements = newElements}
        _ -> do
          maybeLeftConst <- getConstValue fxs
          maybeRightConst <- getConstValue fys
          if isJust leftUnit && leftUnit == maybeLeftConst
            then return $ Evaluated $ exprToThunk fys
            else
              if isJust rightUnit && rightUnit == maybeRightConst
                then return $ Evaluated $ exprToThunk fxs
                else
                  if isJust leftZero && leftZero == maybeLeftConst
                    then return $ Evaluated $ exprToThunk fxs
                    else
                      if isJust rightZero && rightZero == maybeRightConst
                        then return $ Evaluated $ exprToThunk fys
                        else return $ Unevaluable [fds, fxs, fys]

    evalFull :: thunk builtin -> thunk builtin -> thunk builtin -> m (thunk builtin)
    evalFull d x y = forceEvaluation accessOp2 go $ TensorOp2Args d x y

    unstackExpr :: Tensor a -> [thunk builtin]
    unstackExpr xs = exprToThunk . mkExpr inputLit <$> unstack xs

    getConstValue :: expr builtin -> m (Maybe a)
    getConstValue = \case
      (getExpr inputLit -> Just (ConstantTensor _ v)) -> return $ Just v
      (getExpr accessConstTensor -> Just constTensor) -> do
        forcedValue <- force $ constValue constTensor
        getConstValue forcedValue
      _ -> return Nothing

evalReduceTensor ::
  forall expr thunk builtin a m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk builtin m, HasTensorExpr expr thunk builtin) =>
  Accessor (expr builtin) (TensorReductionArgs (thunk builtin)) ->
  Accessor (expr builtin) (Tensor a) ->
  Accessor (expr builtin) (TensorOp2Args (thunk builtin)) ->
  (a -> a -> a) ->
  a ->
  EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceTensor accessReductionOp accessLit accessOp2 op2 unit = go
  where
    go :: EvalSimple expr thunk TensorReductionArgs builtin m
    go (TensorReductionArgs vds vxs) = do
      fds <- force @expr vds
      fxs <- force @expr vxs
      case (fds, fxs) of
        (_, getExpr accessLit -> Just xs) ->
          return $ Evaluated $ exprToThunk $ mkExpr accessLit $ foldTensor op2 unit xs
        (IDimCons _ ds, getExpr accessStackTensor -> Just xs) -> case stackElements xs of
          [] -> return $ Evaluated $ exprToThunk $ mkExpr accessLit (ZeroDimTensor unit)
          v : vs -> do
            v' <- evalFull ds v
            Evaluated <$> foldM (foldFn ds) v' vs
        (IDimNil, _) ->
          return $ Evaluated $ exprToThunk fxs
        _ ->
          return $ Unevaluable [fds, fxs]

    evalFull :: thunk builtin -> thunk builtin -> m (thunk builtin)
    evalFull ds xs = forceEvaluation accessReductionOp go (TensorReductionArgs ds xs)

    evalBop :: thunk builtin -> thunk builtin -> thunk builtin -> thunk builtin
    evalBop ds xs ys = exprToThunk $ mkExpr accessOp2 (TensorOp2Args ds xs ys)

    foldFn :: thunk builtin -> thunk builtin -> thunk builtin -> m (thunk builtin)
    foldFn ds r y = evalBop ds r <$> evalFull ds y

-----------------------------------------------------------------------------
-- Individual builtin evaluation
-----------------------------------------------------------------------------
-- Not

evalNot ::
  (MonadNormBuiltin m, HasBoolExpr expr thunk builtin) =>
  EvalSimple expr thunk TensorOp1Args builtin m
evalNot = evalTensorOp1 accessNotTensor accessBoolTensorLiteral not

-----------------------------------------------------------------------------
-- And

evalAnd ::
  (MonadNormBuiltin m, HasBoolExpr expr thunk builtin) =>
  EvalSimple expr thunk TensorOp2Args builtin m
evalAnd = evalTensorOp2 accessAndTensor accessBoolTensorLiteral (&&) (Just True) (Just True) (Just False) (Just False)

-----------------------------------------------------------------------------
-- Or

evalOr ::
  (MonadNormBuiltin m, HasBoolExpr expr thunk builtin) =>
  EvalSimple expr thunk TensorOp2Args builtin m
evalOr = evalTensorOp2 accessOrTensor accessBoolTensorLiteral (||) (Just False) (Just False) (Just True) (Just True)

-----------------------------------------------------------------------------
-- Implies

elimImplies ::
  (HasBoolExpr expr thunk builtin) =>
  TensorOp2Args (thunk builtin) ->
  thunk builtin
elimImplies (TensorOp2Args ds xs ys) = do
  let notXs = exprToThunk $ mkExpr accessNotTensor (TensorOp1Args ds xs)
  let notXsOrYs = mkExpr accessOrTensor (TensorOp2Args ds notXs ys)
  exprToThunk notXsOrYs

evalImplies ::
  (MonadNormBuiltin m, HasBoolExpr expr thunk builtin) =>
  EvalSimple expr thunk TensorOp2Args builtin m
evalImplies args = return $ Evaluated $ elimImplies args

-----------------------------------------------------------------------------
-- ReduceAnd

evalReduceAndTensor ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, NormalisableBuiltin builtin, BuiltinHasNatType builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin, BuiltinHasTensors builtin, BuiltinHasListLiterals builtin, BuiltinHasNatLiterals builtin, BuiltinHasBoolLiterals builtin, HasTensorLiterals expr builtin, HasLiftableTensorOperations expr thunk builtin) =>
  EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceAndTensor (TensorReductionArgs dims tensor) = do
  forcedTensor <- force @expr tensor
  case getExpr accessAndTensor forcedTensor of
    Just (TensorOp2Args ds xs ys) -> do
      let xs' = exprToThunk $ mkExpr accessReduceAnd (TensorReductionArgs dims xs)
      let ys' = exprToThunk $ mkExpr accessReduceAnd (TensorReductionArgs dims ys)
      return $ Evaluated $ exprToThunk $ mkExpr accessAndTensor (TensorOp2Args ds xs' ys')
    _ -> unoptimisedEvalReduceAndTensor (TensorReductionArgs dims (exprToThunk forcedTensor))

unoptimisedEvalReduceAndTensor ::
  (MonadNormBuiltin m, HasBoolExpr expr thunk builtin, PrintableBuiltin builtin) =>
  EvalSimple expr thunk TensorReductionArgs builtin m
unoptimisedEvalReduceAndTensor =
  evalReduceTensor accessReduceAnd accessBoolTensorLiteral accessAndTensor (&&) True

-----------------------------------------------------------------------------
-- ReduceOr

evalReduceOrTensor :: (MonadNormBuiltin m, HasBoolExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceOrTensor = evalReduceTensor accessReduceOr accessBoolTensorLiteral accessOrTensor (||) False

-----------------------------------------------------------------------------
-- If

evalIf :: forall m expr thunk builtin. (MonadNormBuiltin m, HasBoolExpr expr thunk builtin) => EvalSimple expr thunk IfArgs builtin m
evalIf (IfArgs _t c e1 e2) = do
  fc <- force @expr c
  case fc of
    IBoolLiteral True -> return $ Evaluated e1
    IBoolLiteral False -> return $ Evaluated e2
    _ -> return $ Unevaluable [fc]

-----------------------------------------------------------------------------
-- Index

evalCompareIndex ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, HasBoolExpr expr thunk builtin, BuiltinHasIndexLiterals builtin) =>
  ComparisonOp ->
  EvalSimple expr thunk IndexComparisonArgs builtin m
evalCompareIndex op (IndexComparisonArgs _ _ v1 v2) = do
  v1' <- force @expr v1
  v2' <- force @expr v2
  case (v1', v2') of
    (IIndexLiteral x _, IIndexLiteral y _) ->
      return $ Evaluated $ exprToThunk $ IBoolLiteral (comparisonOp op x y)
    _ -> return $ Unevaluable [v1', v2']

-----------------------------------------------------------------------------
-- Nat

evalNatOp2 ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, NormalisableExpr expr thunk builtin m, HasNatExpr expr thunk builtin) =>
  (Int -> Int -> Int) ->
  EvalSimple expr thunk Op2Args builtin m
evalNatOp2 f (Op2Args vx vy) = do
  fx <- force @expr @thunk vx
  fy <- force @expr @thunk vy
  case (fx, fy) of
    (INatLiteral x, INatLiteral y) -> return $ Evaluated $ exprToThunk $ INatLiteral (f x y)
    _ -> return $ Unevaluable [fx, fy]

evalAddNat ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk builtin m, HasNatExpr expr thunk builtin) =>
  EvalSimple expr thunk Op2Args builtin m
evalAddNat = evalNatOp2 (+)

evalMulNat ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk builtin m, HasNatExpr expr thunk builtin) =>
  EvalSimple expr thunk Op2Args builtin m
evalMulNat = evalNatOp2 (*)

evalCompareNat ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, HasBuiltinConstructor expr thunk, NormalisableExpr expr thunk builtin m, HasBoolExpr expr thunk builtin, HasNatExpr expr thunk builtin) =>
  ComparisonOp ->
  EvalSimple expr thunk Op2Args builtin m
evalCompareNat op (Op2Args vx vy) = do
  fx <- force @expr vx
  fy <- force @expr vy
  case (fx, fy) of
    (INatLiteral x, INatLiteral y) -> return $ Evaluated $ exprToThunk $ IBoolLiteral (comparisonOp op x y)
    _ -> return $ Unevaluable [fx, fy]

-----------------------------------------------------------------------------
-- List

evalMapList ::
  forall expr thunk builtin m.
  (MonadLogger m, HasBuiltinConstructor expr thunk, NormalisableExpr expr thunk builtin m, BuiltinHasListLiterals builtin) =>
  EvalSimple expr thunk MapListArgs builtin m
evalMapList (MapListArgs t1 t2 f xs) = do
  fxs <- force xs
  case fxs of
    INil _ -> return $ Evaluated $ exprToThunk $ INil t2
    ICons _ v vs -> do
      v' <- exprToThunk <$> forceApp f [explicit v]
      let vs' = exprToThunk $ mkExpr accessMapList (MapListArgs t1 t2 f vs)
      return $ Evaluated $ exprToThunk $ ICons t2 v' vs'
    _ -> return $ Unevaluable [fxs]

evalFoldList ::
  forall m expr thunk builtin.
  (MonadLogger m, HasBuiltinConstructor expr thunk, NormalisableExpr expr thunk builtin m, BuiltinHasListLiterals builtin) =>
  EvalSimple expr thunk FoldListArgs builtin m
evalFoldList (FoldListArgs a b f e xs) = do
  fxs <- force xs
  case fxs of
    INil _ -> return $ Evaluated e
    ICons _ v vs -> do
      let r = exprToThunk $ mkExpr accessFoldList (FoldListArgs a b f e vs)
      Evaluated . exprToThunk <$> forceApp f [explicit v, explicit r]
    _ -> return $ Unevaluable [fxs]

-----------------------------------------------------------------------------
-- Rational tensors

evalNegRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp1Args builtin m
evalNegRatTensor = evalTensorOp1 accessNegRatTensor accessRatTensorLiteral (\x -> -x)

evalLogRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp1Args builtin m
evalLogRatTensor _x = return $ Unevaluable []

evalExpRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp1Args builtin m
evalExpRatTensor _x = return $ Unevaluable []

evalAddRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalAddRatTensor = evalTensorOp2 accessAddRatTensor accessRatTensorLiteral (+) (Just 0) (Just 0) Nothing Nothing

evalMulRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalMulRatTensor = evalTensorOp2 accessMulRatTensor accessRatTensorLiteral (*) (Just 1) (Just 1) (Just 0) (Just 0)

evalSubRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalSubRatTensor = evalTensorOp2 accessSubRatTensor accessRatTensorLiteral (-) Nothing (Just 0) Nothing Nothing

evalDivRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalDivRatTensor = evalTensorOp2 accessDivRatTensor accessRatTensorLiteral (/) Nothing (Just 1) Nothing Nothing

evalMinRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalMinRatTensor = evalTensorOp2 accessMinRatTensor accessRatTensorLiteral min Nothing Nothing Nothing Nothing

evalMaxRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalMaxRatTensor = evalTensorOp2 accessMaxRatTensor accessRatTensorLiteral max Nothing Nothing Nothing Nothing

evalPowRatTensor :: forall expr thunk builtin m. (MonadNormBuiltin m, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalPowRatTensor (TensorOp2Args _ xs e) = do
  xs' <- force @expr xs
  e' <- force @expr e
  case (xs', e') of
    (IRatTensor t, IRatLiteral (Finite n))
      -- We can only evaluate this if the exponent is an integer
      | denominator n == 1 -> return $ Evaluated $ exprToThunk $ IRatTensor (mapTensor (^^ numerator n) t)
    _ -> return $ Unevaluable [xs', e']

evalReduceAddRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceAddRatTensor = evalReduceTensor accessReduceAddRat accessRatTensorLiteral accessAddRatTensor (+) 0

evalReduceMulRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceMulRatTensor = evalReduceTensor accessReduceMulRat accessRatTensorLiteral accessMulRatTensor (*) 1

evalReduceMinRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceMinRatTensor = evalReduceTensor accessReduceMinRat accessRatTensorLiteral accessMinRatTensor min PosInfinity

evalReduceMaxRatTensor :: (MonadNormBuiltin m, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceMaxRatTensor = evalReduceTensor accessReduceMaxRat accessRatTensorLiteral accessMaxRatTensor max NegInfinity

evalCompareRatTensorPointwise ::
  (MonadNormBuiltin m, HasBoolExpr expr thunk builtin, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) =>
  ComparisonOp ->
  EvalSimple expr thunk TensorOp2Args builtin m
evalCompareRatTensorPointwise op =
  evalHeteroTensorOp2
    (applyAccessor accessCompareRatTensorPointwise op)
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
  forall expr thunk builtin m.
  (MonadNormBuiltin m, BuiltinHasIndexLiterals builtin, HasVectorExpr expr thunk builtin) =>
  EvalSimple expr thunk AtVectorArgs builtin m
evalAtVector (AtVectorArgs _t _d vector index) = do
  vector' <- force @expr vector
  index' <- force @expr index
  case (vector', index') of
    (IVecLiteral _t _d xs, IIndexLiteral i _) -> do
      return $ Evaluated (xs !! i)
    _ -> return $ Unevaluable [vector', index']

-----------------------------------------------------------------------------
-- Generic tensor operations
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- At

-- | An optimised evaluation procedure for `At` that attempts to minimise the
-- amount of work needed by deferring evaluation of operations until after indexing.
-- For example `(xs + ys) ! i` becomes `xs ! i + ys ! i`.
evalAtTensor ::
  forall expr thunk builtin m.
  (MonadNormBuiltin m, PrintableBuiltin builtin, HasTensorLiterals expr builtin, HasLiftableTensorOperations expr thunk builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr expr thunk builtin, BuiltinHasForeach builtin) =>
  EvalSimple expr thunk AtTensorArgs builtin m
evalAtTensor args@(AtTensorArgs t d ds tensor index) = do
  forcedTensor <- force tensor
  let maybeResult =
        goOp1 forcedTensor liftableTensorOp1s
          <|> goOp2 forcedTensor liftableTensorOp2s
          <|> goForeach forcedTensor
  case maybeResult of
    Nothing -> unoptimisedEvalAtTensor args
    Just result -> Evaluated . exprToThunk <$> result
  where
    recEvalAt :: thunk builtin -> m (thunk builtin)
    recEvalAt ys = forceEvaluation accessAtTensor evalAtTensor (AtTensorArgs t d ds ys index)

    goOp1 :: expr builtin -> [TensorOpEvalData expr thunk TensorOp1Args builtin] -> Maybe (m (expr builtin))
    goOp1 forcedTensor = \case
      (accessOp1, _) : remainingOp1s -> case getExpr accessOp1 forcedTensor of
        Just (TensorOp1Args _ xs) -> Just $ do
          xsi <- recEvalAt xs
          return $ mkExpr accessOp1 (TensorOp1Args ds xsi)
        _ -> goOp1 forcedTensor remainingOp1s
      [] -> Nothing

    goOp2 :: expr builtin -> [TensorOpEvalData expr thunk TensorOp2Args builtin] -> Maybe (m (expr builtin))
    goOp2 forcedTensor = \case
      (accessOp2, _) : remainingOps2 -> case getExpr accessOp2 forcedTensor of
        Just (TensorOp2Args _ xs ys) -> Just $ do
          xsi <- recEvalAt xs
          ysi <- recEvalAt ys
          return $ mkExpr accessOp2 $ TensorOp2Args ds xsi ysi
        _ -> goOp2 forcedTensor remainingOps2
      _ -> Nothing

    goForeach :: expr builtin -> Maybe (m (expr builtin))
    goForeach forcedTensor = case getExpr accessForeachTensor forcedTensor of
      Just (ForeachTensorArgs _ _ _ fn) -> Just $ do
        forceApp fn [explicit index]
      _ -> Nothing

unoptimisedEvalAtTensor ::
  forall expr thunk builtin m.
  (MonadNormBuiltin m, HasTensorLiterals expr builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr expr thunk builtin) =>
  EvalSimple expr thunk AtTensorArgs builtin m
unoptimisedEvalAtTensor (AtTensorArgs _t _d ds tensor index) = do
  fIndex <- force @expr index
  fTensor <- force @expr tensor
  let maybeResult = case fIndex of
        IIndexLiteral i _ -> do
          goLiterals fTensor i tensorLiterals
            <|> case fTensor of
              (getExpr accessStackTensor -> Just stackArgs) -> Just $ return $ Evaluated $ stackElements stackArgs !! i
              (getExpr accessConstTensor -> Just constArgs) -> Just $ return $ Evaluated $ exprToThunk $ mkExpr accessConstTensor $ constArgs {constDims = ds}
              _ -> Nothing
        _ -> Nothing
  case maybeResult of
    Nothing -> return $ Unevaluable [fIndex, fTensor]
    Just result -> result
  where
    goLiterals :: expr builtin -> Int -> [TensorLiteralAccessor expr builtin] -> Maybe (m (BuiltinEvaluationResult expr thunk builtin))
    goLiterals fTensor i literals = case literals of
      Wrapper Access {..} : remainingLiterals -> case getExpr fTensor of
        Just xs -> Just $ return $ Evaluated $ exprToThunk $ mkExpr (xs `at` i)
        Nothing -> do
          goLiterals fTensor i remainingLiterals
      _ -> Nothing

-----------------------------------------------------------------------------
-- Foreach

type HasOptimisedAtBuiltins builtin =
  ( NormalisableBuiltin builtin,
    BuiltinHasListLiterals builtin,
    BuiltinHasNatType builtin,
    BuiltinHasNatLiterals builtin,
    BuiltinHasIndexLiterals builtin,
    BuiltinHasTensors builtin,
    BuiltinHasForeach builtin
  )

-- | An optimised evaluation procedure for `Foreach` that attempts to minimise the
-- amount of work needed by lifting operations to higher-tensor levels.
-- For example `foreach i . xs ! i + ys ! i` becomes `xs + ys`.
liftAndEvalForeachTensor ::
  forall builtin m.
  (MonadNormBuiltin m, MonadNameContext m, HasBuiltinConstructor ForcedValue Thunk, NormalisableExpr ForcedValue Thunk builtin m, HasTensorLiterals ForcedValue builtin, HasLiftableTensorOperations ForcedValue Thunk builtin, HasLambdaConstructor ForcedValue Thunk Closure, HasOptimisedAtBuiltins builtin) =>
  EvalSimple ForcedValue Thunk ForeachTensorArgs builtin m
liftAndEvalForeachTensor args@(ForeachTensorArgs _t d ds fn) =
  case getExpr accessForcedLamC fn of
    Just (binder, closure) -> do
      ctx <- getNameContext
      let lv = boundCtxLv ctx
      let body = extendClosureWithBound closure binder lv
      body' <- addNameToContext binder $ force body

      let createForeachArgs tElem newBody = do
            let newBody' = quote mempty (lv + 1) newBody
            let newLam = mkExpr accessForcedLamC (binder, Closure (namedBoundContextToEnv ctx) newBody')
            ForeachTensorArgs tElem d ds newLam

      maybeResult <- liftForeach createForeachArgs lv d (exprToThunk body')
      case maybeResult of
        Just liftedResult -> return $ Evaluated liftedResult
        Nothing -> evalForeachTensor args
    _ -> unexpectedExprError "NBE" "foreachIndex"

liftForeach ::
  forall builtin m.
  (MonadNormBuiltin m, NormalisableExpr ForcedValue Thunk builtin m, HasTensorLiterals ForcedValue builtin, HasBuiltinConstructor ForcedValue Thunk, HasLiftableTensorOperations ForcedValue Thunk builtin, HasOptimisedAtBuiltins builtin, HasLambdaConstructor ForcedValue Thunk Closure) =>
  (Thunk builtin -> Thunk builtin -> ForeachTensorArgs (Thunk builtin)) ->
  Lv ->
  Thunk builtin ->
  Thunk builtin ->
  m (Maybe (Thunk builtin))
liftForeach createForeachArgs lv dim = go
  where
    go ::
      Thunk builtin ->
      m (Maybe (Thunk builtin))
    go body = logForeachFusion body $ do
      forcedBody <- force body
      -- Try each of the following in turn until it works.
      runMaybeT $
        asum $
          map
            MaybeT
            [ goOp1 forcedBody liftableTensorOp1s,
              goOp2 forcedBody liftableTensorOp2s,
              goConst forcedBody,
              goLiterals forcedBody tensorLiterals,
              goAt forcedBody
            ]

    goRec ::
      ForcedValue builtin ->
      Thunk builtin ->
      m (Thunk builtin)
    goRec typ body = do
      maybeLiftedResult <- go body
      case maybeLiftedResult of
        Just liftedResult -> return liftedResult
        Nothing -> do
          let args = createForeachArgs (exprToThunk typ) body
          forceEvaluation accessForeachTensor evalForeachTensor args

    -- Distribute the `forallIndex` across a liftable operation (e.g. `not`).
    -- e.g. `foreach i . op (x(i))` -> `op (foreach i . x(i))`
    goOp1 ::
      ForcedValue builtin ->
      [TensorOpEvalData ForcedValue Thunk TensorOp1Args builtin] ->
      m (Maybe (Thunk builtin))
    goOp1 body = \case
      (accessOp1, typ) : remainingOp1s -> case getExpr accessOp1 body of
        Just (TensorOp1Args ds e) -> do
          e' <- goRec typ e
          return $ Just $ Forced $ mkExpr accessOp1 (TensorOp1Args (exprToThunk $ IDimCons dim ds) e')
        _ -> goOp1 body remainingOp1s
      [] -> return Nothing

    -- Distribute the `forallIndex` across a liftable operation (e.g. `and`).
    -- e.g. `foreach i . x(i) op y(i)` -> `(foreach i . x(i)) op (forall i . y(i))`
    goOp2 ::
      ForcedValue builtin ->
      [TensorOpEvalData ForcedValue Thunk TensorOp2Args builtin] ->
      m (Maybe (Thunk builtin))
    goOp2 body = \case
      (accessOp2, typ) : remainingOps -> case getExpr accessOp2 body of
        Just (TensorOp2Args ds e1 e2) -> do
          e1' <- goRec typ e1
          e2' <- goRec typ e2
          let newSpine = TensorOp2Args (exprToThunk $ IDimCons dim ds) e1' e2'
          return $ Just $ Forced $ mkExpr accessOp2 newSpine
        _ -> goOp2 body remainingOps
      [] -> return Nothing

    -- Eliminate `forall i . xs ! i` into `xs`
    goAt :: ForcedValue builtin -> m (Maybe (Thunk builtin))
    goAt value = case getExpr accessAtTensor value of
      Just (AtTensorArgs _ _ _ xs i) -> do
        i' <- force i
        case getExpr accessBoundVarC i' of
          Just (lv1, [] :: [GenericArg (Thunk builtin)]) | lv1 == lv -> return $ Just xs
          _ -> return Nothing
      _ -> return Nothing

    goLiterals :: ForcedValue builtin -> [TensorLiteralAccessor ForcedValue builtin] -> m (Maybe (Thunk builtin))
    goLiterals value literals = case literals of
      Wrapper Access {..} : remainingLiterals -> do
        forcedDim <- force dim
        case (getExpr value, forcedDim) of
          (Just xs, INatLiteral dim') -> return $ Just $ Forced $ mkExpr $ extendTensor dim' xs
          _ -> goLiterals value remainingLiterals
      _ -> return Nothing

    goConst :: ForcedValue builtin -> m (Maybe (Thunk builtin))
    goConst value = case getExpr accessConstTensor value of
      Just (ConstTensorArgs t x ds) ->
        return $
          Just $
            Forced $
              mkExpr accessConstTensor $
                ConstTensorArgs t x (exprToThunk $ IDimCons dim ds)
      _ -> return Nothing

evalForeachTensor ::
  forall m expr thunk builtin.
  (MonadLogger m, NormalisableExpr expr thunk builtin m, HasTensorLiterals expr builtin, HasTensorExpr expr thunk builtin, BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  EvalSimple expr thunk ForeachTensorArgs builtin m
evalForeachTensor (ForeachTensorArgs t d ds f) = do
  d' <- force @expr d
  case d' of
    INatLiteral n -> do
      xs <- traverse (\i -> exprToThunk <$> forceApp f [explicit (exprToThunk $ IIndexLiteral i d)]) [0 .. (n - 1 :: Int)]
      let stackArgs = StackTensorArgs t d ds xs
      return $ Evaluated $ exprToThunk $ mkExpr accessStackTensor stackArgs
    _ -> return $ Unevaluable [d']

-----------------------------------------------------------------------------
-- Stack

evalStackTensor ::
  (MonadNormBuiltin m, HasTensorLiterals expr builtin, BuiltinHasNatLiterals builtin, HasTensorExpr expr thunk builtin) =>
  EvalSimple expr thunk StackTensorArgs builtin m
evalStackTensor = evalStackTensorWithPrimitives tensorLiterals

evalStackTensorWithPrimitives ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, BuiltinHasNatLiterals builtin, HasTensorExpr expr thunk builtin) =>
  [TensorLiteralAccessor expr builtin] ->
  EvalSimple expr thunk StackTensorArgs builtin m
evalStackTensorWithPrimitives tensorLits (StackTensorArgs _t d ds xs) = do
  fd <- force @expr d
  fds <- getDims ds
  -- If we know that all the tensors being stacked are concrete tensors, then
  -- we must know the dimensions as well.
  maybeResult <- case (fd, fds) of
    (INatLiteral n, Just ns) | length xs == n -> do
      fxs <- traverse force xs
      sequence $ go ns fxs tensorLits
    _ -> return Nothing
  case maybeResult of
    Nothing -> return $ Unevaluable [fd]
    Just result -> return result
  where
    go :: TensorShape -> [expr builtin] -> [TensorLiteralAccessor expr builtin] -> Maybe (m (BuiltinEvaluationResult expr thunk builtin))
    go elemDims elements = \case
      Wrapper Access {..} : prims ->
        case traverse getExpr elements of
          Just xss -> Just $ return $ Evaluated $ exprToThunk $ mkExpr $ stack elemDims xss
          Nothing -> go elemDims elements prims
      [] -> Nothing

-----------------------------------------------------------------------------
-- Const

evalConstTensor ::
  forall expr thunk builtin m.
  ( MonadNormBuiltin m,
    NormalisableExpr expr thunk builtin m,
    HasTensorLiterals expr builtin,
    BuiltinHasNatLiterals builtin,
    HasTensorExpr expr thunk builtin
  ) =>
  EvalSimple expr thunk ConstTensorArgs builtin m
evalConstTensor (ConstTensorArgs _t xs ds) = do
  fxs <- force xs
  -- Pattern matching on ds here is technically a bug as blocking will not
  -- function correctly. However, to fix it we would need to go via `StackTensor`
  -- and in particular make `StackTensor` take the size argument as an expression.
  -- Our type-system can't handle that easily yet.
  maybeDims <- getDims ds
  case (\dims -> go dims fxs tensorLiterals) =<< maybeDims of
    Just result -> return $ Evaluated $ exprToThunk result
    _ -> do
      forcedDims <- force ds
      return $ Unevaluable [fxs, forcedDims]
  where
    go :: [Int] -> expr builtin -> [TensorLiteralAccessor expr builtin] -> Maybe (expr builtin)
    go dims fxs = \case
      [] -> Nothing
      Wrapper Access {..} : prims -> case getExpr fxs of
        Just t -> case t of
          ZeroDimTensor v -> Just $ mkExpr $ ConstantTensor dims v
          _ -> developerError "Non-zero dimensional tensor argument for ConstTensor"
        Nothing -> go dims fxs prims

evalForeachVector ::
  forall m expr thunk builtin.
  (MonadLogger m, NormalisableExpr expr thunk builtin m, HasTensorLiterals expr builtin, HasVectorExpr expr thunk builtin, BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  EvalSimple expr thunk ForeachVectorArgs builtin m
evalForeachVector (ForeachVectorArgs t d f) = do
  fd <- force @expr d
  case fd of
    INatLiteral n -> do
      xs <- traverse (\i -> exprToThunk <$> forceApp f [explicit (exprToThunk $ IIndexLiteral i d)]) [0 .. (n - 1 :: Int)]
      return $ Evaluated $ exprToThunk $ IVecLiteral t d xs
    _ -> return $ Unevaluable [fd]

evalIterate ::
  forall m expr thunk builtin.
  (MonadLogger m, NormalisableExpr expr thunk builtin m, HasNatExpr expr thunk builtin, BuiltinHasIterate builtin) =>
  EvalSimple expr thunk IterateArgs builtin m
evalIterate (IterateArgs t f n e) = do
  fn <- force @expr n
  case fn of
    INatLiteral 0 -> return $ Evaluated e
    INatLiteral v -> do
      let recFn = exprToThunk $ mkBuiltin accessIterateBuiltin () [t, explicit f, explicit (exprToThunk $ INatLiteral (v - 1))]
      Evaluated . exprToThunk <$> forceApp f [explicit recFn, explicit e]
    _ -> return $ Unevaluable [fn]

-----------------------------------------------------------------------------
-- Utils

getDim ::
  forall expr thunk builtin m.
  (NormalisableExpr expr thunk builtin m, HasNatExpr expr thunk builtin, Monad m) =>
  thunk builtin ->
  m (Maybe Int)
getDim value = do
  forcedValue <- force @expr value
  return $ case forcedValue of
    INatLiteral n -> Just n
    _ -> Nothing

getDimsExprs ::
  forall expr thunk builtin m.
  (NormalisableExpr expr thunk builtin m, HasNatType expr thunk builtin, HasNatExpr expr thunk builtin, HasListExpr expr thunk builtin, Monad m) =>
  thunk builtin ->
  m (Either (expr builtin) [thunk builtin])
getDimsExprs value = do
  forcedValue <- force @expr value
  case forcedValue of
    IDimNil -> return $ Right []
    IDimCons d ds -> do
      r <- getDimsExprs ds
      return ((d :) <$> r)
    e -> return $ Left e

getDims ::
  (NormalisableExpr expr thunk builtin m, HasNatType expr thunk builtin, HasNatExpr expr thunk builtin, HasListExpr expr thunk builtin, Monad m) =>
  thunk builtin ->
  m (Maybe TensorShape)
getDims value = do
  dims <- getDimsExprs value
  case dims of
    Left {} -> return Nothing
    Right xs -> do
      rs <- traverse getDim xs
      return $ sequence rs

-----------------------------------------------------------------------------
-- Logging

logForeachFusion ::
  (MonadLogger m, PrintableBuiltin builtin) =>
  expr builtin ->
  m (Maybe (Thunk builtin)) ->
  m (Maybe (Thunk builtin))
logForeachFusion _input action = action

{-
showFusionEntry :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> Value builtin -> m ()
showFusionEntry ctx expr = do
  logDebug MidDetail $ "fusion-entry" <+> prettyFriendly (WithContext expr ctx)
  -- logDebug MidDetail $ "nbe-entry" <+> prettyFriendly (WithContext expr (boundEnvToCtx boundEnv)) <+> "   { boundEnv =" <+> prettyFriendly boundEnv <+> "}"
  -- logDebug MidDetail $ "nbe-entry" <+> prettyVerbose expr -- <+> "   { boundEnv=" <+> prettyVerbose boundEnv <+> "}"
  incrCallDepth
  return ()

showFusionExit :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> Value builtin -> m (Value builtin)
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
  Maybe (thunk builtin, expr builtin) ->
  m (Maybe (thunk builtin, expr builtin))
fusionExit _ctx result = return result

{-
fusionEnter :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> Value builtin -> m ()
fusionEnter ctx value = do
  logDebug MaxDetail $ "fusion-enter" <+> prettyFriendly (WithContext value ctx)
  incrCallDepth

fusionExit :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> Maybe (VArg builtin, Value builtin) -> m (Maybe (VArg builtin, Value builtin))
fusionExit ctx result = do
  decrCallDepth
  logDebug MaxDetail $
    "fusion-exit" <+> case result of
      Nothing -> ""
      Just (dims, value) -> prettyFriendly (WithContext value ctx) <+> parens (prettyFriendly (WithContext (argExpr dims) ctx))
  return result-}
