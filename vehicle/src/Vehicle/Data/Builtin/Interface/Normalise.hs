{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
module Vehicle.Data.Builtin.Interface.Normalise where

import Control.Applicative ((<|>))
import Control.Monad (foldM, zipWithM)
import Control.Monad.Error.Class (MonadError (..))
import Data.Maybe (fromMaybe, isJust)
import Data.Ratio (denominator, numerator)
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Blocked
import Vehicle.Data.Builtin.Interface.Print (PrintableBuiltin)
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Real (ExtendedRational (..))
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

data EvalScheme expr thunk builtin m
  = forall args.
    (IsArgs args) =>
    Simple (args (thunk builtin) -> m (expr builtin))
  | forall args.
    (IsArgs args) =>
    NonSimple (NamedBoundCtx -> EvalApp expr thunk builtin m -> Eval expr builtin m -> args (thunk builtin) -> m (expr builtin))
  | Derived Identifier
  | None

-- | A type-class for builtins that can be normalised compositionally.
class (PrintableBuiltin builtin) => NormalisableBuiltin builtin where
  evalScheme ::
    ( MonadLogger m,
      Quote (expr builtin) (Expr builtin),
      NormalisableExpr expr thunk,
      HasBuiltinConstructor expr thunk,
      HasLambdaConstructor expr thunk Closure
    ) =>
    builtin ->
    EvalScheme expr thunk builtin m
  blockingStatus :: builtin -> Spine builtin -> BlockingStatus builtin
  isTypeClassOp :: builtin -> Bool
  isCast :: (MonadLogger m) => Provenance -> builtin -> Maybe ([GenericArg (Expr builtin)] -> m (Expr builtin))

forceEvalSimpleBuiltin ::
  (IsArgs args, MonadLogger m, Pretty builtin, PrintableBuiltin builtin) =>
  Provenance ->
  builtin ->
  EvalSimple Expr Expr args builtin m ->
  [GenericArg (Expr builtin)] ->
  m (Expr builtin)
forceEvalSimpleBuiltin p b eval spine =
  case getExpr accessSpine spine of
    Just args -> eval args
    Nothing -> return $ normAppList (Builtin p b) spine

class NormalisableExpr expr thunk where
  force :: thunk builtin -> expr builtin

instance NormalisableExpr Value Value where
  force = id

instance NormalisableExpr Expr Expr where
  force = id

--------------------------------------------------------------------------------
-- Evaluation

type EvalSimple expr thunk args builtin m =
  args (thunk builtin) ->
  m (expr builtin)

type EvalSimplePartial expr thunk args builtin m =
  args (thunk builtin) ->
  Maybe (m (expr builtin))

evalSimple ::
  (MonadNormBuiltin m, IsArgs args, HasBuiltinConstructor expr thunk) =>
  builtin ->
  EvalSimplePartial expr thunk args builtin m ->
  EvalSimple expr thunk args builtin m
evalSimple b eval args = case eval args of
  Just result -> result
  Nothing -> return $ mkExpr accessBuiltinC (b, mkExpr accessSpine args)

evalTensorOp1 ::
  forall expr thunk builtin a m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasTensorExpr expr thunk builtin, Eq a) =>
  Accessor builtin () ->
  Accessor (expr builtin) (Tensor a) ->
  (a -> a) ->
  EvalSimple expr thunk TensorOp1Args builtin m
evalTensorOp1 accessBuiltinOp accessLit op =
  evalSimple (mkExpr accessBuiltinOp ()) eval
  where
    eval :: EvalSimplePartial expr thunk TensorOp1Args builtin m
    eval (TensorOp1Args vds vxs) = do
      let ds' = force vds
      let xs' = force vxs
      case (ds', xs') of
        (_ds, getExpr accessLit -> Just t) ->
          Just $ return $ mkExpr accessLit $ mapTensor op t
        (IDimCons _ ds, getExpr accessConstTensor -> Just xs) ->
          Just $ mkExpr accessConstTensor <$> traverseConstTensorValue (evalFull ds) xs
        (IDimCons _ ds, getExpr accessStackTensor -> Just xs) ->
          Just $ mkExpr accessStackTensor <$> traverseStackTensorElements (evalFull ds) xs
        _ -> Nothing

    evalFull :: thunk builtin -> thunk builtin -> m (thunk builtin)
    evalFull ds x = exprToThunk <$> evalSimple (mkExpr accessBuiltinOp ()) eval (TensorOp1Args ds x)

evalTensorOp2 ::
  forall expr thunk builtin a m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasTensorExpr expr thunk builtin, Eq a) =>
  Accessor builtin () ->
  Accessor (expr builtin) (Tensor a) ->
  (a -> a -> a) ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  EvalSimple expr thunk TensorOp2Args builtin m
evalTensorOp2 accessBuiltin accessLit =
  evalHeteroTensorOp2 (mkExpr accessBuiltin ()) accessLit accessLit

evalHeteroTensorOp2 ::
  forall expr thunk builtin a b m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasTensorExpr expr thunk builtin, Eq a, Eq b) =>
  builtin ->
  Accessor (expr builtin) (Tensor a) ->
  Accessor (expr builtin) (Tensor b) ->
  (a -> a -> b) ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  EvalSimple expr thunk TensorOp2Args builtin m
evalHeteroTensorOp2 b inputLit outputLit op leftUnit rightUnit leftZero rightZero args =
  evalSimple b eval args
  where
    eval :: EvalSimplePartial expr thunk TensorOp2Args builtin m
    eval (TensorOp2Args vds vxs vys) = do
      let fds = force @expr vds
      let fxs = force @expr vxs
      let fys = force @expr vys
      case (fds, fxs, fys) of
        (_ds, getExpr inputLit -> Just xs, getExpr inputLit -> Just ys) ->
          Just $ return $ mkExpr outputLit $ zipWithTensor op xs ys
        (IDimCons _ ds, getExpr accessConstTensor -> Just xs, getExpr accessConstTensor -> Just ys) ->
          Just $ do
            newConstValue <- evalFull ds (constValue xs) (constValue ys)
            return $ mkExpr accessConstTensor $ xs {constValue = newConstValue}
        -- Unlike const tensors, we need to eval stack tensors as after being combined with constants, short-circuiting of
        -- operations may allow for further reduction.
        (IDimCons _ ds, getExpr inputLit -> Just xs, getExpr accessStackTensor -> Just ys) ->
          Just $ do
            newElements <- zipWithM (evalFull ds) (unstackExpr xs) (stackElements ys)
            evalStackTensorWithPrimitives [Wrapper outputLit] $ ys {stackElements = newElements}
        (IDimCons _ ds, getExpr accessStackTensor -> Just xs, getExpr inputLit -> Just ys) ->
          Just $ do
            newElements <- zipWithM (evalFull ds) (stackElements xs) (unstackExpr ys)
            evalStackTensorWithPrimitives [Wrapper outputLit] $ xs {stackElements = newElements}
        (IDimCons _ ds, getExpr accessStackTensor -> Just xs, getExpr accessStackTensor -> Just ys) ->
          Just $ do
            newElements <- zipWithM (evalFull ds) (stackElements xs) (stackElements ys)
            evalStackTensorWithPrimitives [Wrapper outputLit] $ xs {stackElements = newElements}
        _
          | isJust leftUnit && leftUnit == getConstValue fxs -> Just $ return fys
        _
          | isJust rightUnit && rightUnit == getConstValue fys -> Just $ return fxs
        _
          | isJust leftZero && leftZero == getConstValue fxs -> Just $ return fxs
        _
          | isJust rightZero && rightZero == getConstValue fys -> Just $ return fys
        _ -> Nothing

    evalFull :: thunk builtin -> thunk builtin -> thunk builtin -> m (thunk builtin)
    evalFull d x y = exprToThunk <$> evalSimple b eval (TensorOp2Args d x y)

    unstackExpr :: Tensor a -> [thunk builtin]
    unstackExpr xs = exprToThunk . mkExpr inputLit <$> unstack xs

    getConstValue :: expr builtin -> Maybe a
    getConstValue = \case
      (getExpr inputLit -> Just (ConstantTensor _ v)) -> Just v
      (getExpr accessConstTensor -> Just constTensor) -> getConstValue (force $ constValue constTensor)
      _ -> Nothing

evalReduceTensor ::
  forall expr thunk builtin a m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasTensorExpr expr thunk builtin, PrintableBuiltin builtin) =>
  Accessor builtin () ->
  Accessor (expr builtin) (Tensor a) ->
  EvalSimple expr thunk TensorOp2Args builtin m ->
  (a -> a -> a) ->
  a ->
  EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceTensor accessReductionOp accessLit evalOp2 op2 unit = do
  evalSimple (mkExpr accessReductionOp ()) eval
  where
    eval :: EvalSimplePartial expr thunk TensorReductionArgs builtin m
    eval (TensorReductionArgs vds vxs) = do
      let fds = force @expr vds
      let fxs = force @expr vxs
      case (fds, fxs) of
        (_, getExpr accessLit -> Just xs) ->
          Just $ return $ mkExpr accessLit $ foldTensor op2 unit xs
        (IDimCons _ ds, getExpr accessStackTensor -> Just xs) ->
          Just $ foldM (foldFn ds) (mkExpr accessLit (ZeroDimTensor unit)) (stackElements xs)
        (IDimNil, xs) ->
          Just $ return xs
        _ -> Nothing

    evalFull :: thunk builtin -> thunk builtin -> m (thunk builtin)
    evalFull ds xs = exprToThunk <$> evalSimple (mkExpr accessReductionOp ()) eval (TensorReductionArgs ds xs)

    evalBop :: thunk builtin -> expr builtin -> thunk builtin -> m (expr builtin)
    evalBop ds xs ys = evalOp2 (TensorOp2Args ds (exprToThunk xs) ys)

    foldFn :: thunk builtin -> expr builtin -> thunk builtin -> m (expr builtin)
    foldFn ds r y = do
      y' <- evalFull ds y
      evalBop ds r y'

-----------------------------------------------------------------------------
-- Individual builtin evaluation
-----------------------------------------------------------------------------
-- Not

evalNot :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin) => EvalSimple expr thunk TensorOp1Args builtin m
evalNot = evalTensorOp1 accessNotBuiltin accessBoolTensorLiteral not

-----------------------------------------------------------------------------
-- And

evalAnd :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalAnd = evalTensorOp2 accessAndBuiltin accessBoolTensorLiteral (&&) (Just True) (Just True) (Just False) (Just False)

-----------------------------------------------------------------------------
-- Or

evalOr :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalOr args = evalTensorOp2 accessOrBuiltin accessBoolTensorLiteral (||) (Just False) (Just False) (Just True) (Just True) args

-----------------------------------------------------------------------------
-- Implies

evalImplies ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin) =>
  EvalSimple expr thunk TensorOp2Args builtin m
evalImplies (TensorOp2Args ds xs ys) = do
  notXs <- exprToThunk <$> evalNot (TensorOp1Args ds xs)
  evalOr (TensorOp2Args ds notXs ys)

-----------------------------------------------------------------------------
-- ReduceAnd

evalReduceAndTensor ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, PrintableBuiltin builtin, Quote (expr builtin) (Expr builtin), HasLambdaConstructor expr thunk Closure, HasBuiltinConstructor expr thunk, NormalisableExpr expr thunk, NormalisableBuiltin builtin, BuiltinHasNatType builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin, BuiltinHasTensors builtin, BuiltinHasListLiterals builtin, BuiltinHasNatLiterals builtin, BuiltinHasBoolLiterals builtin, HasTensorLiterals expr builtin, HasLiftableTensorOperations expr thunk builtin) =>
  NamedBoundCtx ->
  EvalApp expr thunk builtin m ->
  Eval expr builtin m ->
  EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceAndTensor ctx evalApp eval (TensorReductionArgs dims t) = go t
  where
    go :: thunk builtin -> m (expr builtin)
    go tensor = do
      let forcedTensor = force tensor
      case getExpr accessAndTensor forcedTensor of
        Just (TensorOp2Args ds xs ys) -> do
          xs' <- exprToThunk <$> go xs
          ys' <- exprToThunk <$> go ys
          evalAnd (TensorOp2Args ds xs' ys')
        _ -> do
          result <- fuseReduceAndForeachTensor ctx evalApp eval forcedTensor
          case result of
            Nothing -> unoptimisedEvalReduceAndTensor (TensorReductionArgs dims (exprToThunk forcedTensor))
            Just (newDims, fusedTensor) ->
              return $ mkExpr accessReduceAnd (TensorReductionArgs newDims fusedTensor)

-- | An optimised evaluation procedure for `Foreach` that attempts to minimise the
-- amount of work needed by lifting operations to higher-tensor levels.
-- For example `foreach i . xs ! i + ys ! i` becomes `xs + ys`.
fuseReduceAndForeachTensor ::
  forall m expr thunk builtin.
  (MonadLogger m, PrintableBuiltin builtin, Quote (expr builtin) (Expr builtin), NormalisableExpr expr thunk, HasBuiltinConstructor expr thunk, HasLambdaConstructor expr thunk Closure, NormalisableBuiltin builtin, BuiltinHasNatType builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin, BuiltinHasTensors builtin, BuiltinHasListLiterals builtin, BuiltinHasNatLiterals builtin, BuiltinHasBoolLiterals builtin, HasTensorLiterals expr builtin, HasLiftableTensorOperations expr thunk builtin) =>
  NamedBoundCtx ->
  EvalApp expr thunk builtin m ->
  Eval expr builtin m ->
  expr builtin ->
  m (Maybe (thunk builtin, thunk builtin))
fuseReduceAndForeachTensor ctx evalApp eval value = do
  fusionEnter ctx value
  fusionExit ctx =<< case getExpr accessForeachTensor value of
    Just (ForeachTensorArgs typ d _ (getExpr accessForcedLamC -> Just (binder, Closure env body))) -> do
      let lv = boundCtxLv ctx
      let newEnv = extendEnvWithBound lv binder env
      let newCtx = nameOf binder : ctx
      body' <- eval newCtx newEnv body
      case getExpr accessReduceAnd body' of
        Just (TensorReductionArgs (tensorDims :: thunk builtin) tensor) -> do
          (newDims, newTensor) <- fromMaybe (tensorDims, tensor) <$> fuseReduceAndForeachTensor @m @expr @thunk newCtx evalApp eval (force tensor)
          let newTensor' = quote @(expr builtin) mempty (lv + 1) (force newTensor)
          let newLam = mkExpr accessForcedLamC (binder, Closure (namedBoundContextToEnv ctx) newTensor')
          let newForeachArgs = ForeachTensorArgs typ d newDims newLam
          newBody' <- evalForeachTensor newCtx evalApp eval newForeachArgs
          return $ Just (exprToThunk $ IDimCons d newDims, exprToThunk newBody')
        _ -> return Nothing
    _ -> return Nothing

unoptimisedEvalReduceAndTensor ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin, PrintableBuiltin builtin) =>
  EvalSimple expr thunk TensorReductionArgs builtin m
unoptimisedEvalReduceAndTensor =
  evalReduceTensor accessReduceAndBuiltin accessBoolTensorLiteral evalAnd (&&) True

-----------------------------------------------------------------------------
-- ReduceOr

evalReduceOrTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceOrTensor = evalReduceTensor accessReduceOrBuiltin accessBoolTensorLiteral evalOr (||) False

-----------------------------------------------------------------------------
-- If

evalIf :: forall m expr thunk builtin. (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin) => EvalSimple expr thunk IfArgs builtin m
evalIf args@(IfArgs _t c e1 e2) = do
  let fc = force @expr c
  return $ case fc of
    IBoolLiteral True -> force e1
    IBoolLiteral False -> force e2
    _ -> mkExpr accessIf args

-----------------------------------------------------------------------------
-- Index

evalCompareIndex ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin, BuiltinHasIndexLiterals builtin) =>
  ComparisonOp ->
  EvalSimple expr thunk IndexComparisonArgs builtin m
evalCompareIndex op args@(IndexComparisonArgs _ _ v1 v2) = do
  let v1' = force @expr v1
  let v2' = force @expr v2
  case (v1', v2') of
    (IIndexLiteral x _, IIndexLiteral y _) -> return $ IBoolLiteral (comparisonOp op x y)
    _ -> return $ mkExpr accessCompareIndex (op, args)

-----------------------------------------------------------------------------
-- Nat

evalNatOp2 ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasNatExpr expr thunk builtin) =>
  Op2Accessor expr thunk builtin ->
  (Int -> Int -> Int) ->
  EvalSimple expr thunk Op2Args builtin m
evalNatOp2 accessOp f args@(Op2Args vx vy) = do
  let fx = force @expr @thunk vx
  let fy = force @expr @thunk vy
  case (fx, fy) of
    (INatLiteral x, INatLiteral y) -> return $ INatLiteral (f x y)
    _ -> return $ mkExpr accessOp args

evalAddNat ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasNatExpr expr thunk builtin) =>
  EvalSimple expr thunk Op2Args builtin m
evalAddNat = evalNatOp2 accessAddNat (+)

evalMulNat ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasNatExpr expr thunk builtin) =>
  EvalSimple expr thunk Op2Args builtin m
evalMulNat = evalNatOp2 accessMulNat (*)

evalCompareNat ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin, HasNatExpr expr thunk builtin) =>
  ComparisonOp ->
  EvalSimple expr thunk Op2Args builtin m
evalCompareNat op args@(Op2Args vx vy) = do
  let fx = force @expr vx
  let fy = force @expr vy
  case (fx, fy) of
    (INatLiteral x, INatLiteral y) -> return $ IBoolLiteral (comparisonOp op x y)
    _ -> return $ mkExpr accessCompareNat (op, args)

-----------------------------------------------------------------------------
-- List

evalMapList ::
  forall expr thunk builtin m.
  (MonadLogger m, HasBuiltinConstructor expr thunk, NormalisableExpr expr thunk, BuiltinHasListLiterals builtin) =>
  NamedBoundCtx ->
  EvalApp expr thunk builtin m ->
  Eval expr builtin m ->
  MapListArgs (thunk builtin) ->
  m (expr builtin)
evalMapList ctx evalApp eval (MapListArgs a b f xs) = evalList xs
  where
    evalList :: thunk builtin -> m (expr builtin)
    evalList vxs = do
      let fxs = force vxs
      case fxs of
        INil _ -> return $ INil b
        ICons _ v vs -> do
          v' <- exprToThunk <$> evalApp ctx f [explicit v]
          vs' <- exprToThunk <$> evalMapList ctx evalApp eval (recArgs vs)
          return $ ICons b v' vs'
        vs -> return $ mkExpr accessMapList (recArgs $ exprToThunk vs)

    recArgs :: thunk builtin -> MapListArgs (thunk builtin)
    recArgs = MapListArgs a b f

evalFoldList ::
  forall m expr thunk builtin.
  (MonadLogger m, NormalisableExpr expr thunk, HasBuiltinConstructor expr thunk, BuiltinHasListLiterals builtin) =>
  NamedBoundCtx ->
  EvalApp expr thunk builtin m ->
  Eval expr builtin m ->
  FoldListArgs (thunk builtin) ->
  m (expr builtin)
evalFoldList ctx evalApp eval (FoldListArgs a b f e xs) = evalList xs
  where
    evalList :: thunk builtin -> m (expr builtin)
    evalList vxs = do
      let fxs = force vxs
      case fxs of
        INil _ -> return $ force e
        ICons _ v vs -> do
          r <- exprToThunk <$> evalFoldList ctx evalApp eval (recArgs vs)
          evalApp ctx f [explicit v, explicit r]
        vs -> return $ mkExpr accessFoldList (recArgs $ exprToThunk vs)

    recArgs :: thunk builtin -> FoldListArgs (thunk builtin)
    recArgs = FoldListArgs a b f e

-----------------------------------------------------------------------------
-- Rational tensors

evalNegRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp1Args builtin m
evalNegRatTensor = evalTensorOp1 accessNegRatTensorBuiltin accessRatTensorLiteral (\x -> -x)

evalLogRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp1Args builtin m
evalLogRatTensor x = return $ mkExpr accessLogRatTensor x

evalExpRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp1Args builtin m
evalExpRatTensor x = return $ mkExpr accessExpRatTensor x

evalAddRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalAddRatTensor = evalTensorOp2 accessAddRatTensorBuiltin accessRatTensorLiteral (+) (Just 0) (Just 0) Nothing Nothing

evalMulRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalMulRatTensor = evalTensorOp2 accessMulRatTensorBuiltin accessRatTensorLiteral (*) (Just 1) (Just 1) (Just 0) (Just 0)

evalSubRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalSubRatTensor = evalTensorOp2 accessSubRatTensorBuiltin accessRatTensorLiteral (-) Nothing (Just 0) Nothing Nothing

evalDivRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalDivRatTensor args = evalTensorOp2 accessDivRatTensorBuiltin accessRatTensorLiteral (/) Nothing (Just 1) Nothing Nothing args

evalMinRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalMinRatTensor = evalTensorOp2 accessMinRatTensorBuiltin accessRatTensorLiteral min Nothing Nothing Nothing Nothing

evalMaxRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalMaxRatTensor = evalTensorOp2 accessMaxRatTensorBuiltin accessRatTensorLiteral max Nothing Nothing Nothing Nothing

evalPowRatTensor :: forall expr thunk builtin m. (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin) => EvalSimple expr thunk TensorOp2Args builtin m
evalPowRatTensor args@(TensorOp2Args _ xs e) = do
  let xs' = force @expr xs
  let e' = force @expr e
  case (xs', e') of
    (IRatTensor t, IRatLiteral (Finite n))
      -- We can only evaluate this if the exponent is an integer
      | denominator n == 1 -> return $ IRatTensor (mapTensor (^^ numerator n) t)
    _ -> return $ mkExpr accessPowRatTensor args

evalReduceAddRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceAddRatTensor = evalReduceTensor accessReduceAddRatBuiltin accessRatTensorLiteral evalAddRatTensor (+) 0

evalReduceMulRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceMulRatTensor = evalReduceTensor accessReduceMulRatBuiltin accessRatTensorLiteral evalMulRatTensor (*) 1

evalReduceMinRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceMinRatTensor = evalReduceTensor accessReduceMinRatBuiltin accessRatTensorLiteral evalMinRatTensor min PosInfinity

evalReduceMaxRatTensor :: (MonadNormBuiltin m, NormalisableExpr expr thunk, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) => EvalSimple expr thunk TensorReductionArgs builtin m
evalReduceMaxRatTensor = evalReduceTensor accessReduceMaxRatBuiltin accessRatTensorLiteral evalMaxRatTensor max NegInfinity

evalCompareRatTensorPointwise ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasBoolExpr expr thunk builtin, HasRatExpr expr thunk builtin, PrintableBuiltin builtin) =>
  ComparisonOp ->
  EvalSimple expr thunk TensorOp2Args builtin m
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
  forall expr thunk builtin m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, BuiltinHasIndexLiterals builtin, HasVectorExpr expr thunk builtin) =>
  EvalSimple expr thunk AtVectorArgs builtin m
evalAtVector args@(AtVectorArgs _t _d vector index) = do
  fromMaybe (return $ mkExpr accessAtVector args) $ do
    let vector' = force @expr vector
    let index' = force @expr index
    case (vector', index') of
      (IVecLiteral _t _d xs, IIndexLiteral i _) -> Just $ return $ force $ xs !! i
      _ -> Nothing

-----------------------------------------------------------------------------
-- Generic tensor operations
-----------------------------------------------------------------------------

type TensorOpEvalData expr thunk args builtin m =
  ( Destruct (expr builtin) (args (thunk builtin)),
    EvalSimple expr thunk args builtin m,
    expr builtin -- The element type
  )

class HasLiftableTensorOperations expr thunk builtin where
  liftableTensorOp1s :: (MonadNormBuiltin m) => [TensorOpEvalData expr thunk TensorOp1Args builtin m]
  liftableTensorOp2s :: (MonadNormBuiltin m) => [TensorOpEvalData expr thunk TensorOp2Args builtin m]

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
  forall expr thunk builtin m.
  (MonadNormBuiltin m, PrintableBuiltin builtin, NormalisableExpr expr thunk, HasTensorLiterals expr builtin, HasLiftableTensorOperations expr thunk builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr expr thunk builtin, BuiltinHasForeach builtin) =>
  NamedBoundCtx ->
  EvalApp expr thunk builtin m ->
  Eval expr builtin m ->
  EvalSimple expr thunk AtTensorArgs builtin m
evalAtTensor ctx evalApp eval args@(AtTensorArgs t d ds tensor index) =
  fromMaybe (unoptimisedEvalAtTensor args) $ do
    let forcedTensor = force tensor
    goOp1 forcedTensor liftableTensorOp1s
      <|> goOp2 forcedTensor liftableTensorOp2s
      <|> goForeach forcedTensor
  where
    recEvalAt :: thunk builtin -> m (expr builtin)
    recEvalAt ys = evalAtTensor ctx evalApp eval (AtTensorArgs t d ds ys index)

    goOp1 :: expr builtin -> [TensorOpEvalData expr thunk TensorOp1Args builtin m] -> Maybe (m (expr builtin))
    goOp1 forcedTensor = \case
      (accessOp1, evalOp1, _) : remainingOp1s -> case accessOp1 forcedTensor of
        Just (TensorOp1Args _ xs) -> Just $ do
          xsi <- exprToThunk <$> recEvalAt xs
          evalOp1 (TensorOp1Args ds xsi)
        _ -> goOp1 forcedTensor remainingOp1s
      [] -> Nothing

    goOp2 :: expr builtin -> [TensorOpEvalData expr thunk TensorOp2Args builtin m] -> Maybe (m (expr builtin))
    goOp2 forcedTensor = \case
      (accessOp2, evalOp2, _) : remainingOps2 -> case accessOp2 forcedTensor of
        Just (TensorOp2Args _ xs ys) -> Just $ do
          xsi <- exprToThunk <$> recEvalAt xs
          ysi <- exprToThunk <$> recEvalAt ys
          evalOp2 $ TensorOp2Args ds xsi ysi
        _ -> goOp2 forcedTensor remainingOps2
      _ -> Nothing

    goForeach :: expr builtin -> Maybe (m (expr builtin))
    goForeach forcedTensor = case getExpr accessForeachTensor forcedTensor of
      Just (ForeachTensorArgs _ _ _ fn) -> Just $ do
        evalApp ctx fn [explicit index]
      _ -> Nothing

unoptimisedEvalAtTensor ::
  forall expr thunk builtin m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasTensorLiterals expr builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr expr thunk builtin) =>
  EvalSimple expr thunk AtTensorArgs builtin m
unoptimisedEvalAtTensor args@(AtTensorArgs _t _d ds tensor index) = do
  fromMaybe (return $ mkExpr accessAtTensor args) $ do
    let fIndex = force @expr index
    case fIndex of
      IIndexLiteral i _ -> do
        let fTensor = force @expr tensor
        goLiterals fTensor i tensorLiterals
          <|> case fTensor of
            (getExpr accessStackTensor -> Just stackArgs) -> Just $ return $ force $ stackElements stackArgs !! i
            (getExpr accessConstTensor -> Just constArgs) -> Just $ return $ mkExpr accessConstTensor $ constArgs {constDims = ds}
            _ -> Nothing
      _ -> Nothing
  where
    goLiterals :: expr builtin -> Int -> [TensorLiteralAccessor expr builtin] -> Maybe (m (expr builtin))
    goLiterals fTensor i literals = case literals of
      Wrapper Access {..} : remainingLiterals -> case getExpr fTensor of
        Just xs -> Just $ return $ mkExpr (xs `at` i)
        Nothing -> do
          goLiterals fTensor i remainingLiterals
      _ -> Nothing

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
evalForeachTensor ::
  forall expr thunk builtin m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, Quote (expr builtin) (Expr builtin), HasTensorLiterals expr builtin, HasBuiltinConstructor expr thunk, HasLiftableTensorOperations expr thunk builtin, HasLambdaConstructor expr thunk Closure, HasOptimisedAtBuiltins builtin) =>
  NamedBoundCtx ->
  EvalApp expr thunk builtin m ->
  Eval expr builtin m ->
  ForeachTensorArgs (thunk builtin) ->
  m (expr builtin)
evalForeachTensor ctx evalApp eval (ForeachTensorArgs typ d ds fn) =
  case getExpr accessForcedLamC fn of
    Just (binder, Closure env body) -> do
      let lv = boundCtxLv ctx
      let newEnv = extendEnvWithBound lv binder env
      let newCtx = nameOf binder : ctx
      body' <- eval newCtx newEnv body
      let createForeach t newBody = do
            let newBody' = quote @(expr builtin) mempty (lv + 1) (force newBody)
            let newLam = mkExpr accessForcedLamC (binder, Closure (namedBoundContextToEnv ctx) newBody')
            let args = ForeachTensorArgs t d ds newLam
            unoptimisedEvalForeachTensor ctx evalApp args
      result <- liftForeach newCtx createForeach lv d typ (exprToThunk body')
      return result
    _ -> unexpectedExprError "NBE" "foreachIndex"

liftForeach ::
  forall expr thunk builtin m.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasTensorLiterals expr builtin, HasLiftableTensorOperations expr thunk builtin, HasOptimisedAtBuiltins builtin, HasLambdaConstructor expr thunk Closure, HasBuiltinConstructor expr thunk) =>
  NamedBoundCtx ->
  (thunk builtin -> thunk builtin -> m (expr builtin)) ->
  Lv ->
  thunk builtin ->
  thunk builtin ->
  thunk builtin ->
  m (expr builtin)
liftForeach ctx evalForeach lv d = go (force d)
  where
    go :: expr builtin -> thunk builtin -> thunk builtin -> m (expr builtin)
    go dim typ body = do
      showFusionEntry ctx body
      let forcedBody = force body
      let maybeResult =
            goOp1 dim forcedBody liftableTensorOp1s
              <|> goOp2 dim forcedBody liftableTensorOp2s
              <|> goAt forcedBody
              <|> goConst forcedBody
              <|> goLiterals dim forcedBody tensorLiterals
      result <- fromMaybe (evalForeach typ body) maybeResult
      showFusionExit ctx result

    -- Distribute the `forallIndex` across a liftable operation (e.g. `not`).
    -- e.g. `foreach i . op (x(i))` -> `op (foreach i . x(i))`
    goOp1 :: expr builtin -> expr builtin -> [TensorOpEvalData expr thunk TensorOp1Args builtin m] -> Maybe (m (expr builtin))
    goOp1 dim body = \case
      (accessOp1, evalOp1, typ) : remainingOp1s -> case accessOp1 body of
        Just (TensorOp1Args ds e) -> Just $ do
          e' <- exprToThunk <$> go dim (exprToThunk typ) e
          evalOp1 (TensorOp1Args (exprToThunk $ IDimCons d ds) e')
        _ -> goOp1 dim body remainingOp1s
      [] -> Nothing

    -- Distribute the `forallIndex` across a liftable operation (e.g. `and`).
    -- e.g. `foreach i . x(i) op y(i)` -> `(foreach i . x(i)) op (forall i . y(i))`
    goOp2 :: expr builtin -> expr builtin -> [TensorOpEvalData expr thunk TensorOp2Args builtin m] -> Maybe (m (expr builtin))
    goOp2 dim body = \case
      (accessOp, evalOp, typ) : remainingOps -> case accessOp body of
        Just (TensorOp2Args ds e1 e2) -> Just $ do
          e1' <- exprToThunk <$> go dim (exprToThunk typ) e1
          e2' <- exprToThunk <$> go dim (exprToThunk typ) e2
          let newSpine = TensorOp2Args (exprToThunk $ IDimCons d ds) e1' e2'
          evalOp newSpine
        _ -> goOp2 dim body remainingOps
      [] -> Nothing

    -- Eliminate `forall i . xs ! i` into `xs`
    goAt :: expr builtin -> Maybe (m (expr builtin))
    goAt value = case getExpr accessAtTensor value of
      Just (AtTensorArgs _ _ _ xs i) -> do
        let i' = force i
        case getExpr accessBoundVarC i' of
          Just (lv1, [] :: [GenericArg (thunk builtin)]) | lv1 == lv -> Just $ return $ force xs
          _ -> Nothing
      _ -> Nothing

    goLiterals :: expr builtin -> expr builtin -> [TensorLiteralAccessor expr builtin] -> Maybe (m (expr builtin))
    goLiterals dim value literals = case literals of
      Wrapper Access {..} : remainingLiterals -> case (getExpr value, dim) of
        (Just xs, INatLiteral dim') -> Just $ return $ mkExpr $ extendTensor dim' xs
        _ -> goLiterals dim value remainingLiterals
      _ -> Nothing

    goConst :: expr builtin -> Maybe (m (expr builtin))
    goConst value = case getExpr accessConstTensor value of
      Just (ConstTensorArgs t x ds) ->
        Just $
          evalConstTensor $
            ConstTensorArgs t x (exprToThunk $ IDimCons d ds)
      _ -> Nothing

unoptimisedEvalForeachTensor ::
  forall m expr thunk builtin.
  (MonadLogger m, NormalisableExpr expr thunk, HasTensorLiterals expr builtin, HasTensorExpr expr thunk builtin, BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  NamedBoundCtx ->
  EvalApp expr thunk builtin m ->
  ForeachTensorArgs (thunk builtin) ->
  m (expr builtin)
unoptimisedEvalForeachTensor ctx evalApp args@(ForeachTensorArgs t d ds f) = do
  let d' = force @expr d
  case d' of
    INatLiteral n -> do
      xs <- traverse (\i -> exprToThunk <$> evalApp ctx f [explicit (exprToThunk $ IIndexLiteral i d)]) [0 .. (n - 1 :: Int)]
      evalStackTensor (StackTensorArgs t d ds xs)
    _ -> return $ mkExpr accessForeachTensor args

-----------------------------------------------------------------------------
-- Stack

evalStackTensor ::
  (MonadNormBuiltin m, NormalisableExpr expr thunk, HasTensorLiterals expr builtin, BuiltinHasNatLiterals builtin, HasTensorExpr expr thunk builtin) =>
  EvalSimple expr thunk StackTensorArgs builtin m
evalStackTensor = evalStackTensorWithPrimitives tensorLiterals

evalStackTensorWithPrimitives ::
  forall m expr thunk builtin.
  (MonadNormBuiltin m, NormalisableExpr expr thunk, BuiltinHasNatLiterals builtin, HasTensorExpr expr thunk builtin) =>
  [TensorLiteralAccessor expr builtin] ->
  EvalSimple expr thunk StackTensorArgs builtin m
evalStackTensorWithPrimitives tensorLits args@(StackTensorArgs _t d ds xs) = do
  return $
    fromMaybe (mkExpr accessStackTensor args) $ do
      let fd = force @expr d
      let fds = getDims ds
      -- If we know that all the tensors being stacked are concrete tensors, then
      -- we must know the dimensions as well.
      case (fd, fds) of
        (INatLiteral n, Just ns) | length xs == n -> do
          let fxs = fmap force xs
          go ns fxs tensorLits
        _ -> Nothing
  where
    go :: TensorShape -> [expr builtin] -> [TensorLiteralAccessor expr builtin] -> Maybe (expr builtin)
    go elemDims elements = \case
      Wrapper Access {..} : prims ->
        case traverse getExpr elements of
          Just xss -> Just $ mkExpr $ stack elemDims xss
          Nothing -> go elemDims elements prims
      [] -> Nothing

-----------------------------------------------------------------------------
-- Const

evalConstTensor ::
  forall expr thunk builtin m.
  ( MonadNormBuiltin m,
    NormalisableExpr expr thunk,
    HasTensorLiterals expr builtin,
    BuiltinHasNatLiterals builtin,
    HasTensorExpr expr thunk builtin
  ) =>
  EvalSimple expr thunk ConstTensorArgs builtin m
evalConstTensor args@(ConstTensorArgs _t xs ds) = do
  let fxs = force xs
  -- Pattern matching on ds here is technically a bug as blocking will not
  -- function correctly. However, to fix it we would need to go via `StackTensor`
  -- and in particular make `StackTensor` take the size argument as an expression.
  -- Our type-system can't handle that easily yet.
  case (\dims -> go dims fxs tensorLiterals) =<< getDims ds of
    Just result -> return result
    _ -> return $ mkExpr accessConstTensor args
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
  (MonadLogger m, NormalisableExpr expr thunk, HasTensorLiterals expr builtin, HasVectorExpr expr thunk builtin, BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  NamedBoundCtx ->
  EvalApp expr thunk builtin m ->
  Eval expr builtin m ->
  ForeachVectorArgs (thunk builtin) ->
  m (expr builtin)
evalForeachVector ctx evalApp _eval args@(ForeachVectorArgs t d f) = do
  let d' = force @expr d
  case d' of
    INatLiteral n -> do
      xs <- traverse (\i -> exprToThunk <$> evalApp ctx f [explicit (exprToThunk $ IIndexLiteral i d)]) [0 .. (n - 1 :: Int)]
      return $ IVecLiteral t d xs
    _ -> return $ mkExpr accessForeachVector args

evalIterate ::
  forall m expr thunk builtin.
  (MonadLogger m, NormalisableExpr expr thunk, HasNatExpr expr thunk builtin, BuiltinHasIterate builtin) =>
  NamedBoundCtx ->
  EvalApp expr thunk builtin m ->
  Eval expr builtin m ->
  IterateArgs (thunk builtin) ->
  m (expr builtin)
evalIterate ctx evalApp _eval args@(IterateArgs t f n e) = do
  let n' = force @expr n
  case n' of
    INatLiteral 0 -> return $ force e
    INatLiteral v -> do
      let recFn = exprToThunk $ mkBuiltin accessIterateBuiltin () [t, explicit f, explicit (exprToThunk $ INatLiteral (v - 1))]
      evalApp ctx f [explicit recFn, explicit e]
    _ -> return $ mkExpr accessIterate args

-----------------------------------------------------------------------------
-- Utils

getDim ::
  forall expr thunk builtin.
  (NormalisableExpr expr thunk, HasNatExpr expr thunk builtin) =>
  thunk builtin ->
  Maybe Int
getDim value = case force @expr value of
  INatLiteral n -> Just n
  _ -> Nothing

getDimsExprs ::
  forall expr thunk builtin.
  (NormalisableExpr expr thunk, HasNatType expr thunk builtin, HasNatExpr expr thunk builtin, HasListExpr expr thunk builtin) =>
  thunk builtin ->
  Either (expr builtin) [thunk builtin]
getDimsExprs value = case force @expr value of
  IDimNil -> return []
  IDimCons d ds -> (d :) <$> getDimsExprs ds
  e -> throwError e

getDims ::
  (NormalisableExpr expr thunk, HasNatType expr thunk builtin, HasNatExpr expr thunk builtin, HasListExpr expr thunk builtin) =>
  thunk builtin ->
  Maybe TensorShape
getDims v = case getDimsExprs v of
  Left {} -> Nothing
  Right xs -> traverse getDim xs

-----------------------------------------------------------------------------
-- Logging

showFusionEntry :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> expr builtin -> m ()
showFusionEntry _ctx _expr = return ()

showFusionExit :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> expr builtin -> m (expr builtin)
showFusionExit _ctx result = return result

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
