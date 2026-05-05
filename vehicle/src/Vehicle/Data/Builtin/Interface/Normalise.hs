{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Vehicle.Data.Builtin.Interface.Normalise where

import Control.Applicative ((<|>))
import Data.Bifunctor (Bifunctor (..))
import Vehicle.Compile.Normalise.Core (BuiltinEvaluationResult (..), TypedEvalScheme (..))
import Vehicle.Compile.Normalise.NBE (MonadNorm)
import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Print (PrintableBuiltin)
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (Tensor, TensorDimension, TensorShape, at, foldTensor, mapTensor, stack, unstack, zipWithTensor, pattern ConstantTensor, pattern ZeroDimTensor)
import Vehicle.Data.Tensor.Traversal
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

-- | A method for evaluating builtins that takes in an argument allowing the
-- recursive evaluation of applications. that takes in an argument allowing
-- the subsequent further evaluation of applications.
-- Such recursive evaluation is necessary when evaluating higher order
-- functions such as fold, map etc.
type BuiltinEvaluation args builtin m =
  args (Thunk builtin) ->
  m (BuiltinEvaluationResult Thunk Value builtin)

forceEvalCast ::
  (IsArgs args, MonadLogger m, Pretty builtin, PrintableBuiltin builtin) =>
  Provenance ->
  builtin ->
  (args (Expr builtin) -> m (BuiltinEvaluationResult Expr Expr builtin)) ->
  [GenericArg (Expr builtin)] ->
  m (Expr builtin)
forceEvalCast _p _b evalCast spine = do
  case getExpr accessSpine spine of
    Nothing -> developerError "Unexpectedly unable to evaluate cast"
    Just args -> do
      maybeResult <- evalCast args
      case maybeResult of
        Evaluated result -> return result
        Unevaluated {} -> developerError "Unexpectedly unable to evaluate cast"

unforcedBuiltinApp ::
  (IsArgs args) =>
  Accessor builtin () ->
  args (Thunk builtin) ->
  Thunk builtin
unforcedBuiltinApp accessBuiltin args =
  forceBuiltin (mkExpr accessBuiltin ()) (mkExpr accessSpine args)

--------------------------------------------------------------------------------
-- Blocking

{-
blocked :: (IsArgs args) => Arity -> args (Value builtin) -> BlockingStatus builtin
blocked indices spine
  | arity <= length spine = Blocked _
  | otherwise = InsufficientArgs

traverseArgsAtIndices ::
  (Monad m) =>
  [Int] ->
  Int ->
  Spine builtin ->
  m [Value builtin]
traverseArgsAtIndices _blockingArgs _currentIndex [] = return []
traverseArgsAtIndices [] _currentIndex args = return args
traverseArgsAtIndices (blockingIndex : blockingIndices) currentIndex (arg : args)
  | currentIndex == blockingIndex = do
      as <- traverseArgsAtIndices blockingIndices (currentIndex + 1) args
      return $ arg : as
  | otherwise = do
      args' <- traverseArgsAtIndices (blockingIndex : blockingIndices) (currentIndex + 1) args f
      return $ arg : args'
-}

--------------------------------------------------------------------------------
-- Evaluation

evalOp2Args ::
  (MonadNorm builtin m) =>
  Accessor (Value builtin) a ->
  Accessor (Value builtin) b ->
  Accessor (Value builtin) c ->
  (a -> b -> c) ->
  BuiltinEvaluation Op2Args builtin m
evalOp2Args accessArg1 accessArg2 accessRes f (Op2Args e1 e2) = do
  fe1 <- forceValue e1
  fe2 <- forceValue e2
  case (getExpr accessArg1 fe1, getExpr accessArg2 fe2) of
    (Just a, Just b) -> return $ Evaluated $ Forced $ mkExpr accessRes (f a b)
    _ -> return $ Unevaluated [fe1, fe2]

evalTensorOp1 ::
  forall builtin a m.
  (MonadNorm builtin m, HasTensorExpr Value Thunk builtin, Eq a) =>
  Accessor builtin () ->
  Accessor (Value builtin) (Tensor a) ->
  (a -> a) ->
  BuiltinEvaluation TensorOp1Args builtin m
evalTensorOp1 accessBuiltinOp accessLit op = eval
  where
    eval :: BuiltinEvaluation TensorOp1Args builtin m
    eval (TensorOp1Args vds vxs) = do
      fds <- forceValue vds
      fxs <- forceValue vxs
      case (fds, fxs) of
        (_, getExpr accessLit -> Just t) ->
          return $ Evaluated $ Forced $ mkExpr accessLit $ mapTensor op t
        (ICons _ d _, getExpr accessConstTensor -> Just xs) -> do
          let xs' = mapConstTensorValue (evalFull d) xs
          return $ Evaluated $ Forced $ mkExpr accessConstTensor xs'
        (ICons _ d _, getExpr accessStackTensor -> Just xs) -> do
          let xs' = mapStackTensorElements (evalFull d) xs
          return $ Evaluated $ Forced $ mkExpr accessStackTensor xs'
        _ -> return $ Unevaluated [fxs]

    evalFull :: Thunk builtin -> Thunk builtin -> Thunk builtin
    evalFull d x = unforcedBuiltinApp accessBuiltinOp (TensorOp1Args d x)

evalTensorOp2 ::
  forall builtin a m.
  (MonadNorm builtin m, HasTensorExpr Value Thunk builtin, Eq a) =>
  Accessor builtin () ->
  Accessor (Value builtin) (Tensor a) ->
  (a -> a -> a) ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  BuiltinEvaluation TensorOp2Args builtin m
evalTensorOp2 accessOp2 accessLit = evalHeteroTensorOp2 accessOp2 accessLit accessLit

evalHeteroTensorOp2 ::
  forall builtin a b m.
  (MonadNorm builtin m, HasTensorExpr Value Thunk builtin, Eq a, Eq b) =>
  Accessor builtin () ->
  Accessor (Value builtin) (Tensor a) ->
  Accessor (Value builtin) (Tensor b) ->
  (a -> a -> b) ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  Maybe a ->
  BuiltinEvaluation TensorOp2Args builtin m
evalHeteroTensorOp2 accessOp2 inputLit outputLit op leftUnit rightUnit leftZero rightZero = eval
  where
    eval :: BuiltinEvaluation TensorOp2Args builtin m
    eval (TensorOp2Args vds vxs vys) = do
      fxs <- forceValue vxs
      fys <- forceValue vys
      fds <- forceValue vds
      case (fds, fxs, fys) of
        (_, getExpr inputLit -> Just xs, getExpr inputLit -> Just ys) ->
          return $ Evaluated $ Forced $ mkExpr outputLit $ zipWithTensor op xs ys
        (ICons _ _ ds, getExpr accessConstTensor -> Just xs, getExpr accessConstTensor -> Just ys) -> do
          let newConstValue = evalFull ds (constValue xs) (constValue ys)
          return $ Evaluated $ Forced $ mkExpr accessConstTensor $ xs {constValue = newConstValue}
        -- Unlike const tensors, we need to eval stack tensors as after being combined with constants, short-circuiting of
        -- operations may allow for further reduction.
        (ICons _ _ ds, getExpr inputLit -> Just xs, getExpr accessStackTensor -> Just ys) -> do
          let newElements = zipWith (evalFull ds) (unstackExpr xs) (stackElements ys)
          evalStackTensorWithPrimitives [Wrapper outputLit] $ ys {stackElements = newElements}
        (ICons _ _ ds, getExpr accessStackTensor -> Just xs, getExpr inputLit -> Just ys) -> do
          let newElements = zipWith (evalFull ds) (stackElements xs) (unstackExpr ys)
          evalStackTensorWithPrimitives [Wrapper outputLit] $ xs {stackElements = newElements}
        (ICons _ _ ds, getExpr accessStackTensor -> Just xs, getExpr accessStackTensor -> Just ys) -> do
          let newElements = zipWith (evalFull ds) (stackElements xs) (stackElements ys)
          evalStackTensorWithPrimitives [Wrapper outputLit] $ xs {stackElements = newElements}
        _ -> do
          leftConstant <- getConstValue fxs
          rightConstant <- getConstValue fys
          if justEqual leftUnit leftConstant || justEqual rightZero rightConstant
            then return $ Evaluated $ Forced fys
            else
              if justEqual rightUnit rightConstant || justEqual leftZero leftConstant
                then return $ Evaluated $ Forced fxs
                else return $ Unevaluated [fds, fxs, fys]

    evalFull :: Thunk builtin -> Thunk builtin -> Thunk builtin -> Thunk builtin
    evalFull d x y =
      unforcedBuiltinApp accessOp2 $
        TensorOp2Args
          { tensorOp2Dims = d,
            tensorOp2Arg1 = x,
            tensorOp2Arg2 = y
          }

    unstackExpr :: Tensor a -> [Thunk builtin]
    unstackExpr xs = Forced . mkExpr inputLit <$> unstack xs

    getConstValue :: Value builtin -> m (Maybe a)
    getConstValue value = case getExpr inputLit value of
      Just (ConstantTensor _ v) -> return $ Just v
      _ -> case getExpr accessConstTensor value of
        Nothing -> return Nothing
        Just constTensor -> do
          forcedValue <- forceValue (constValue constTensor)
          getConstValue forcedValue

evalReduceTensor ::
  forall builtin a m.
  (MonadNorm builtin m, HasTensorExpr Value Thunk builtin, PrintableBuiltin builtin) =>
  Accessor builtin () ->
  Accessor builtin () ->
  Accessor (Value builtin) (Tensor a) ->
  (a -> a -> a) ->
  BuiltinEvaluation TensorReductionArgs builtin m
evalReduceTensor accessReductionOp accessBop accessLit op2 (TensorReductionArgs vd ve vxs) = do
  fd <- forceValue vd
  fe <- forceValue ve
  fxs <- forceValue vxs
  case (fd, fe, fxs) of
    (_, getExpr accessLit -> Just e, getExpr accessLit -> Just xs) ->
      return $ Evaluated $ Forced $ mkExpr accessLit $ foldTensor op2 e xs
    (ICons _ _ ds, e, getExpr accessStackTensor -> Just xs) ->
      return $ Evaluated $ foldl (foldFn (Forced e) ds) (Forced e) (stackElements xs)
    (INil _, _, _) ->
      return $ Evaluated $ Forced fxs
    _ -> return $ Unevaluated [fxs]
  where
    evalFull :: Thunk builtin -> Thunk builtin -> Thunk builtin -> Thunk builtin
    evalFull ds e xs = unforcedBuiltinApp accessReductionOp (TensorReductionArgs ds e xs)

    evalBop :: Thunk builtin -> Thunk builtin -> Thunk builtin -> Thunk builtin
    evalBop ds xs ys = unforcedBuiltinApp accessBop (TensorOp2Args ds xs ys)

    foldFn :: Thunk builtin -> Thunk builtin -> Thunk builtin -> Thunk builtin -> Thunk builtin
    foldFn e ds r y = evalBop ds r (evalFull ds e y)

-----------------------------------------------------------------------------
-- Individual builtin evaluation
-----------------------------------------------------------------------------
-- Not

evalNot :: (MonadNorm builtin m, HasBoolExpr Value Thunk builtin) => BuiltinEvaluation TensorOp1Args builtin m
evalNot = evalTensorOp1 accessNotTensorBuiltin accessBoolTensorLiteral not

-----------------------------------------------------------------------------
-- And

evalAnd :: (MonadNorm builtin m, HasBoolExpr Value Thunk builtin) => BuiltinEvaluation TensorOp2Args builtin m
evalAnd = evalTensorOp2 accessAndTensorBuiltin accessBoolTensorLiteral (&&) (Just True) (Just True) (Just False) (Just False)

-----------------------------------------------------------------------------
-- Or

evalOr :: (MonadNorm builtin m, HasBoolExpr Value Thunk builtin) => BuiltinEvaluation TensorOp2Args builtin m
evalOr = evalTensorOp2 accessOrTensorBuiltin accessBoolTensorLiteral (||) (Just False) (Just False) (Just True) (Just True)

-----------------------------------------------------------------------------
-- Implies

evalImplies :: (MonadNorm builtin m, HasBoolExpr Value Thunk builtin) => BuiltinEvaluation TensorOp2Args builtin m
evalImplies (TensorOp2Args ds xs ys) = do
  let notXs = unforcedBuiltinApp accessNotTensorBuiltin (TensorOp1Args ds xs)
  let notXsOrYs = unforcedBuiltinApp accessOrTensorBuiltin (TensorOp2Args ds notXs ys)
  return $ Evaluated notXsOrYs

-----------------------------------------------------------------------------
-- ReduceAnd

evalReduceAndTensor ::
  (MonadNorm builtin m, HasBoolExpr Value Thunk builtin, PrintableBuiltin builtin) =>
  BuiltinEvaluation TensorReductionArgs builtin m
evalReduceAndTensor = evalReduceTensor accessReduceAndBuiltin accessAndTensorBuiltin accessBoolTensorLiteral (&&)

-----------------------------------------------------------------------------
-- ReduceOr

evalReduceOrTensor ::
  (MonadNorm builtin m, HasBoolExpr Value Thunk builtin, PrintableBuiltin builtin) =>
  BuiltinEvaluation TensorReductionArgs builtin m
evalReduceOrTensor = evalReduceTensor accessReduceOrBuiltin accessOrTensorBuiltin accessBoolTensorLiteral (||)

-----------------------------------------------------------------------------
-- If

evalIf :: (MonadNorm builtin m, HasBoolExpr Value Thunk builtin) => BuiltinEvaluation IfArgs builtin m
evalIf (IfArgs _t vc ve1 ve2) = do
  fc <- forceValue vc
  case fc of
    IBoolLiteral True -> return $ Evaluated ve1
    IBoolLiteral False -> return $ Evaluated ve2
    _ -> return $ Unevaluated [fc]

-----------------------------------------------------------------------------
-- Index

evalCompareIndex ::
  (MonadNorm builtin m, HasBoolExpr Value Thunk builtin, BuiltinHasIndexLiterals builtin) =>
  ComparisonOp ->
  BuiltinEvaluation IndexComparisonArgs builtin m
evalCompareIndex op (IndexCompArgs _ _ vx vy) = do
  fx <- forceValue vx
  fy <- forceValue vy
  case (fx, fy) of
    (IIndexLiteral x _, IIndexLiteral y _) -> return $ Evaluated $ Forced $ IBoolLiteral (comparisonOp op x y)
    _ -> return $ Unevaluated [fx, fy]

-----------------------------------------------------------------------------
-- Nat

evalAddNat ::
  (MonadNorm builtin m, HasNatExpr Value Thunk builtin) =>
  BuiltinEvaluation Op2Args builtin m
evalAddNat = evalOp2Args accessNatLiteral accessNatLiteral accessNatLiteral (+)

evalMulNat ::
  (MonadNorm builtin m, HasNatExpr Value Thunk builtin) =>
  BuiltinEvaluation Op2Args builtin m
evalMulNat = evalOp2Args accessNatLiteral accessNatLiteral accessNatLiteral (*)

evalCompareNat ::
  (MonadNorm builtin m, HasBoolExpr Value Thunk builtin, BuiltinHasNatLiterals builtin) =>
  ComparisonOp ->
  BuiltinEvaluation Op2Args builtin m
evalCompareNat op = evalOp2Args accessNatLiteral accessNatLiteral accessBoolTensorLiteral (\x y -> ZeroDimTensor $ comparisonOp op x y)

-----------------------------------------------------------------------------
-- List

evalMapList ::
  forall builtin m.
  (MonadNorm builtin m, HasListExpr Value Thunk builtin) =>
  BuiltinEvaluation MapListArgs builtin m
evalMapList (MapListArgs a b f vxs) = do
  fxs <- forceValue vxs
  case fxs of
    INil _ -> return $ Evaluated $ Forced $ INil b
    ICons _ v vs -> do
      let v' = UnforcedApp f [explicit v]
      let vs' = unforcedBuiltinApp accessMapListBuiltin (MapListArgs a b f vs)
      return $ Evaluated $ Forced $ ICons b v' vs'
    _ -> return $ Unevaluated [fxs]

evalFoldList ::
  forall m builtin.
  (MonadNorm builtin m, HasListExpr Value Thunk builtin) =>
  BuiltinEvaluation FoldListArgs builtin m
evalFoldList (FoldListArgs a b f e vxs) = do
  fxs <- forceValue vxs
  case fxs of
    INil _ -> return $ Evaluated e
    ICons _ v vs -> do
      let r = unforcedBuiltinApp accessFoldListBuiltin (FoldListArgs a b f e vs)
      return $ Evaluated $ UnforcedApp f [explicit v, explicit r]
    _ -> return $ Unevaluated [fxs]

-----------------------------------------------------------------------------
-- Rational tensors

evalNegRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin) => BuiltinEvaluation TensorOp1Args builtin m
evalNegRatTensor = evalTensorOp1 accessNegRatTensorBuiltin accessRatTensorLiteral (\x -> -x)

evalAddRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin) => BuiltinEvaluation TensorOp2Args builtin m
evalAddRatTensor = evalTensorOp2 accessAddRatTensorBuiltin accessRatTensorLiteral (+) (Just 0) (Just 0) Nothing Nothing

evalMulRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin) => BuiltinEvaluation TensorOp2Args builtin m
evalMulRatTensor = evalTensorOp2 accessMulRatTensorBuiltin accessRatTensorLiteral (*) (Just 1) (Just 1) (Just 0) (Just 0)

evalSubRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin) => BuiltinEvaluation TensorOp2Args builtin m
evalSubRatTensor = evalTensorOp2 accessSubRatTensorBuiltin accessRatTensorLiteral (-) Nothing (Just 0) Nothing Nothing

evalDivRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin) => BuiltinEvaluation TensorOp2Args builtin m
evalDivRatTensor = evalTensorOp2 accessDivRatTensorBuiltin accessRatTensorLiteral (/) Nothing (Just 1) Nothing Nothing

evalMinRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin) => BuiltinEvaluation TensorOp2Args builtin m
evalMinRatTensor = evalTensorOp2 accessMinRatTensorBuiltin accessRatTensorLiteral min Nothing Nothing Nothing Nothing

evalMaxRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin) => BuiltinEvaluation TensorOp2Args builtin m
evalMaxRatTensor = evalTensorOp2 accessMaxRatTensorBuiltin accessRatTensorLiteral max Nothing Nothing Nothing Nothing

evalPowRat ::
  (MonadNorm builtin m, HasRatExpr Value Thunk builtin, BuiltinHasNatLiterals builtin) =>
  BuiltinEvaluation TensorOp2Args builtin m
evalPowRat (TensorOp2Args _ vxs vn) = do
  fxs <- forceValue vxs
  fn <- forceValue vn
  case (fxs, fn) of
    (IRatTensor xs, INatLiteral n) -> return $ Evaluated $ Forced $ IRatTensor (mapTensor (^^ n) xs)
    _ -> return $ Unevaluated [fxs, fn]

evalReduceAddRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin, PrintableBuiltin builtin) => BuiltinEvaluation TensorReductionArgs builtin m
evalReduceAddRatTensor = evalReduceTensor accessReduceAddRatBuiltin accessAddRatTensorBuiltin accessRatTensorLiteral (+)

evalReduceMulRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin, PrintableBuiltin builtin) => BuiltinEvaluation TensorReductionArgs builtin m
evalReduceMulRatTensor = evalReduceTensor accessReduceMulRatBuiltin accessMulRatTensorBuiltin accessRatTensorLiteral (*)

evalReduceMinRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin, PrintableBuiltin builtin) => BuiltinEvaluation TensorReductionArgs builtin m
evalReduceMinRatTensor = evalReduceTensor accessReduceMinRatBuiltin accessMinRatTensorBuiltin accessRatTensorLiteral min

evalReduceMaxRatTensor :: (MonadNorm builtin m, HasRatExpr Value Thunk builtin, PrintableBuiltin builtin) => BuiltinEvaluation TensorReductionArgs builtin m
evalReduceMaxRatTensor = evalReduceTensor accessReduceMaxRatBuiltin accessMaxRatTensorBuiltin accessRatTensorLiteral max

evalCompareRatTensor ::
  (MonadNorm builtin m, HasBoolExpr Value Thunk builtin, HasRatExpr Value Thunk builtin, PrintableBuiltin builtin) =>
  ComparisonOp ->
  BuiltinEvaluation TensorComparisonArgs builtin m
evalCompareRatTensor op (TensorComparisonArgs pointwiseDims flattenedDims _ _) = do
  forcedDims <- forceValue pointwiseDims
  case forcedDims of
    ICons _ _ _ -> evalHeteroTensorOp2 _ accessRatTensorLiteral accessBoolTensorLiteral _ _ _ _ _ _
    INil _ -> _
    _ -> return $ Unevaluated [forcedDims]

-- evalHeteroTensorOp2
--   (applyAccessor accessCompareRatTensorPointwiseBuiltin op)
--   accessRatTensorLiteral
--   accessBoolTensorLiteral
--   (comparisonOp op)
--   Nothing
--   Nothing
--   Nothing
--   Nothing

-----------------------------------------------------------------------------
-- Generic vector operations

evalAtVector ::
  forall builtin m.
  (MonadNorm builtin m, BuiltinHasIndexLiterals builtin, HasVectorExpr Value Thunk builtin) =>
  BuiltinEvaluation AtVectorArgs builtin m
evalAtVector (AtVectorArgs _t _d vector index) = do
  forcedVector <- forceValue vector
  forcedIndex <- forceValue index
  case (forcedVector, forcedIndex) of
    (IVecLiteral _t _d xs, IIndexLiteral i _) -> return $ Evaluated $ xs !! i
    _ -> return $ Unevaluated [forcedVector, forcedIndex]

-----------------------------------------------------------------------------
-- Generic tensor operations
-----------------------------------------------------------------------------

type TensorOpEvalData args builtin =
  ( Accessor (Value builtin) (args (Thunk builtin)),
    Accessor builtin (),
    VType builtin
  )

class HasLiftableTensorOperations builtin where
  liftableTensorOp1s :: [TensorOpEvalData TensorOp1Args builtin]
  liftableTensorOp2s :: [TensorOpEvalData TensorOp2Args builtin]

data TensorLiteralAccessor builtin
  = forall a. (Eq a) => Wrapper (Accessor (Value builtin) (Tensor a))

class HasTensorLiterals builtin where
  tensorLiterals :: [TensorLiteralAccessor builtin]

-----------------------------------------------------------------------------
-- At

-- | An optimised evaluation procedure for `At` that attempts to minimise the
-- amount of work needed by deferring evaluation of operations until after indexing.
-- For example `(xs + ys) ! i` becomes `xs ! i + ys ! i`.
evalAtTensor ::
  forall builtin m.
  (MonadNorm builtin m, HasTensorLiterals builtin, HasLiftableTensorOperations builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr Value Thunk builtin, BuiltinHasForeach builtin) =>
  BuiltinEvaluation AtTensorArgs builtin m
evalAtTensor args@(AtTensorArgs t d ds tensor index) = do
  ftensor <- forceValue tensor
  let maybeOptimisedResult =
        goOp1 ftensor liftableTensorOp1s
          <|> goOp2 ftensor liftableTensorOp2s
          <|> goForeach ftensor

  case maybeOptimisedResult of
    Just result -> Evaluated <$> result
    Nothing -> unoptimisedEvalAtTensor args
  where
    recEvalAt :: Thunk builtin -> Thunk builtin
    recEvalAt ys =
      unforcedBuiltinApp accessAtTensorBuiltin $
        AtTensorArgs
          { atType = t,
            atFirstDim = d,
            atRemainingDims = ds,
            atTensor = ys,
            atIndex = index
          }

    goOp1 :: Value builtin -> [TensorOpEvalData TensorOp1Args builtin] -> Maybe (m (Thunk builtin))
    goOp1 ftensor = \case
      (accessOp1Args, accessOp1, _) : remainingOp1s -> case getExpr accessOp1Args ftensor of
        Just (TensorOp1Args _ xs) -> Just $ do
          let xsi = recEvalAt xs
          return $ unforcedBuiltinApp accessOp1 (TensorOp1Args ds xsi)
        _ -> goOp1 ftensor remainingOp1s
      [] -> Nothing

    goOp2 :: Value builtin -> [TensorOpEvalData TensorOp2Args builtin] -> Maybe (m (Thunk builtin))
    goOp2 ftensor = \case
      (accessOp2Args, accessOp2, _) : remainingOps2 -> case getExpr accessOp2Args ftensor of
        Just (TensorOp2Args _ xs ys) -> Just $ do
          let xsi = recEvalAt xs
          let ysi = recEvalAt ys
          return $ unforcedBuiltinApp accessOp2 (TensorOp2Args ds xsi ysi)
        _ -> goOp2 ftensor remainingOps2
      _ -> Nothing

    goForeach :: Value builtin -> Maybe (m (Thunk builtin))
    goForeach ftensor = case getExpr accessForeachTensor ftensor of
      Just (ForeachTensorArgs _ _ _ fn) -> Just $ return $ UnforcedApp fn [explicit index]
      _ -> Nothing

unoptimisedEvalAtTensor ::
  forall builtin m.
  (MonadNorm builtin m, HasTensorLiterals builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr Value Thunk builtin) =>
  BuiltinEvaluation AtTensorArgs builtin m
unoptimisedEvalAtTensor (AtTensorArgs _t _d ds tensor index) = do
  ftensor <- forceValue tensor
  findex <- forceValue index
  case (findex, ftensor) of
    (IIndexLiteral i _, getExpr accessStackTensor -> Just stackArgs) ->
      return $ Evaluated $ stackElements stackArgs !! i
    (IIndexLiteral _i _, getExpr accessConstTensor -> Just constArgs) ->
      return $ Evaluated $ Forced $ mkExpr accessConstTensor $ constArgs {constDims = ds}
    _ -> goLiterals ftensor findex tensorLiterals
  where
    goLiterals ::
      Value builtin ->
      Value builtin ->
      [TensorLiteralAccessor builtin] ->
      m (BuiltinEvaluationResult Thunk Value builtin)
    goLiterals ftensor findex literals = case literals of
      Wrapper Access {..} : remainingLiterals -> case (findex, getExpr ftensor) of
        (IIndexLiteral i _, Just xs) -> return $ Evaluated $ Forced $ mkExpr (xs `at` i)
        _ -> goLiterals ftensor findex remainingLiterals
      _ -> return $ Unevaluated [ftensor, findex]

-----------------------------------------------------------------------------
-- Foreach

evalForeachTensor ::
  (MonadNorm builtin m, HasTensorLiterals builtin, HasTensorExpr Value Thunk builtin, BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  BuiltinEvaluation ForeachTensorArgs builtin m
evalForeachTensor (ForeachTensorArgs t d ds f) = do
  fd <- forceValue d
  case fd of
    INatLiteral n -> do
      let xs = fmap (\i -> UnforcedApp f [explicit (Forced $ IIndexLiteral i d)]) [0 .. (n - 1 :: Int)]
      let stackArgs = StackTensorArgs t d ds xs
      return $ Evaluated $ unforcedBuiltinApp accessStackTensorBuiltin stackArgs
    _ -> return $ Unevaluated [fd]

-----------------------------------------------------------------------------
-- Stack

evalStackTensor ::
  (MonadNorm builtin m, HasTensorLiterals builtin, BuiltinHasNatLiterals builtin, HasTensorExpr Value Thunk builtin) =>
  BuiltinEvaluation StackTensorArgs builtin m
evalStackTensor = evalStackTensorWithPrimitives tensorLiterals

evalStackTensorWithPrimitives ::
  forall m builtin.
  (MonadNorm builtin m, BuiltinHasNatLiterals builtin, HasTensorExpr Value Thunk builtin) =>
  [TensorLiteralAccessor builtin] ->
  BuiltinEvaluation StackTensorArgs builtin m
evalStackTensorWithPrimitives tensorLits (StackTensorArgs _t d ds xs) = do
  fd <- forceValue d
  fds <- forceValue ds
  maybeDims <- forceDims (Forced fds)
  case (fd, maybeDims) of
    (INatLiteral n, Just ns) | length xs == n -> do
      fxs <- traverse forceValue xs
      go ns fxs tensorLits
    _ -> return $ Unevaluated [fd, fds]
  where
    go ::
      TensorShape ->
      [Value builtin] ->
      [TensorLiteralAccessor builtin] ->
      m (BuiltinEvaluationResult Thunk Value builtin)
    go elemDims elements = \case
      Wrapper Access {..} : prims ->
        case traverse getExpr elements of
          Just xss -> return $ Evaluated $ Forced $ mkExpr $ stack elemDims xss
          Nothing -> go elemDims elements prims
      [] -> return $ Unevaluated elements

-----------------------------------------------------------------------------
-- Const

evalConstTensor ::
  forall builtin m.
  (MonadNorm builtin m, HasTensorLiterals builtin, BuiltinHasNatLiterals builtin, HasTensorExpr Value Thunk builtin) =>
  BuiltinEvaluation ConstTensorArgs builtin m
evalConstTensor (ConstTensorArgs _t xs ds) = do
  fxs <- forceValue xs
  fds <- forceValue ds
  maybeDims <- forceDims (Forced fds)
  -- Pattern matching on ds here is technically a bug as blocking will not
  -- function correctly. However, to fix it we would need to go via `StackTensor`
  -- and in particular make `StackTensor` take the size argument as an Thunk.
  -- Our type-system can't handle that easily yet.
  case maybeDims of
    Just dims -> go dims fxs tensorLiterals
    _ -> return $ Unevaluated [fds]
  where
    go ::
      TensorShape ->
      Value builtin ->
      [TensorLiteralAccessor builtin] ->
      m (BuiltinEvaluationResult Thunk Value builtin)
    go dims value = \case
      [] -> return $ Unevaluated [value]
      Wrapper Access {..} : prims -> case getExpr value of
        Just t -> case t of
          ZeroDimTensor v -> return $ Evaluated $ Forced $ mkExpr $ ConstantTensor dims v
          _ -> developerError "Non-zero dimensional tensor argument for ConstTensor"
        Nothing -> go dims value prims

evalForeachVector ::
  (MonadNorm builtin m, HasTensorLiterals builtin, HasVectorExpr Value Thunk builtin, BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  BuiltinEvaluation ForeachVectorArgs builtin m
evalForeachVector (ForeachVectorArgs t d f) = do
  fd <- forceValue d
  case fd of
    INatLiteral n -> do
      let xs = fmap (\i -> UnforcedApp f [explicit (Forced $ IIndexLiteral i d)]) [0 .. (n - 1 :: Int)]
      return $ Evaluated $ Forced $ IVecLiteral t d xs
    _ -> return $ Unevaluated [fd]

evalIterate ::
  (MonadNorm builtin m, HasNatExpr Value Thunk builtin, BuiltinHasIterate builtin) =>
  BuiltinEvaluation IterateArgs builtin m
evalIterate (IterateArgs t f n e) = do
  fn <- forceValue n
  case fn of
    INatLiteral 0 -> return $ Evaluated e
    INatLiteral v -> do
      let recFn = Forced $ mkBuiltin accessIterateBuiltin () [t, explicit f, explicit (Forced $ INatLiteral (v - 1))]
      return $ Evaluated (UnforcedApp f [explicit recFn, explicit e])
    _ -> return $ Unevaluated [fn]

-----------------------------------------------------------------------------
-- Utilities

forceDim ::
  (MonadNorm builtin m, HasNatExpr Value Thunk builtin) =>
  Thunk builtin ->
  m (Maybe TensorDimension)
forceDim value = do
  forcedValue <- forceValue value
  return $ case forcedValue of
    INatLiteral n -> Just n
    _ -> Nothing

forceDimsHead ::
  (MonadNorm builtin m, HasNatType Value Thunk builtin, HasNatExpr Value Thunk builtin, HasListExpr Value Thunk builtin) =>
  Thunk builtin ->
  m (Maybe (TensorDimension, Thunk builtin))
forceDimsHead value = do
  forcedValue <- forceValue value
  case forcedValue of
    ICons _ d ds -> do
      maybeDim <- forceDim d
      return $ (,ds) <$> maybeDim
    _ -> return Nothing

forceDimsExprs ::
  (MonadNorm builtin m, HasNatType Value Thunk builtin, HasNatExpr Value Thunk builtin, HasListExpr Value Thunk builtin) =>
  Thunk builtin ->
  m (Either (Value builtin) [Thunk builtin])
forceDimsExprs value = do
  forcedValue <- forceValue value
  case forcedValue of
    INil _ -> return $ Right []
    ICons _ d ds -> ((d :) <$>) <$> forceDimsExprs ds
    e -> return $ Left e

forceDims ::
  (MonadNorm builtin m, HasNatType Value Thunk builtin, HasNatExpr Value Thunk builtin, HasListExpr Value Thunk builtin) =>
  Thunk builtin ->
  m (Maybe TensorShape)
forceDims value = do
  forcedValue <- forceDimsExprs value
  case forcedValue of
    Left {} -> return Nothing
    Right xs -> sequence <$> traverse forceDim xs

extractPartialShape ::
  forall m.
  (MonadNorm Builtin m) =>
  Thunk Builtin ->
  m PartiallyKnownTensorShape
extractPartialShape v = do
  (knownPrefix, unknownSuffix) <- go v
  return $ PartiallyKnownTensorShape knownPrefix unknownSuffix
  where
    go :: Thunk Builtin -> m (TensorShape, Value Builtin)
    go value = do
      forcedValue <- forceValue value
      case forcedValue of
        ICons _ dim dims -> do
          forcedDim <- forceValue dim
          case forcedDim of
            INatLiteral d -> first (d :) <$> go dims
            _ -> return ([], forcedValue)
        _ -> return ([], forcedValue)

-----------------------------------------------------------------------------
-- Logging

showFusionEntry :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> Value builtin -> m ()
showFusionEntry _ctx _ForcedValue = return ()

showFusionExit :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> Value builtin -> m (Value builtin)
showFusionExit _ctx = return

{-
showFusionEntry :: (MonadLogger m, PrintableBuiltin builtin) => NamedBoundCtx -> Value builtin -> m ()
showFusionEntry ctx Value = do
  logDebug MidDetail $ "fusion-entry" <+> prettyFriendly (WithContext Value ctx)
  -- logDebug MidDetail $ "nbe-entry" <+> prettyFriendly (WithContext Value (boundEnvToCtx boundEnv)) <+> "   { boundEnv =" <+> prettyFriendly boundEnv <+> "}"
  -- logDebug MidDetail $ "nbe-entry" <+> prettyVerbose Value -- <+> "   { boundEnv=" <+> prettyVerbose boundEnv <+> "}"
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
  Value builtin ->
  m ()
fusionEnter _ctx _value = return ()

fusionExit ::
  (MonadLogger m, PrintableBuiltin builtin) =>
  NamedBoundCtx ->
  Maybe (VDims builtin, Value builtin) ->
  m (Maybe (VDims builtin, Value builtin))
fusionExit _ctx = return

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
