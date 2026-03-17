module Vehicle.Compile.EquivalenceLaws where

import Control.Applicative ((<|>))
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor
import Vehicle.Data.Variable.Bound.Level
import Vehicle.Prelude

type EquivalenceLaw args builtin m =
  (MonadNorm builtin m) =>
  args (Value builtin) ->
  m (Maybe (Value builtin))

---------------
-- reduceAnd --
---------------

foldReduceAndComparison :: EquivalenceLaw TensorReductionArgs Builtin m
foldReduceAndComparison (TensorReductionArgs _ unit tensor) =
  case (unit, getExpr accessCompareRatTensorPointwise tensor) of
    (IBoolLiteral True, Just (op, TensorOp2Args (ICons _ d ds) xs ys)) | op /= Ne -> do
      let compareArgs = TensorReduceComparisonArgs d ds xs ys
      return $ Just $ mkExpr accessCompareRatTensorReduced (op, compareArgs)
    _ -> return Nothing

-------------
-- foreach --
-------------

-- | An optimised evaluation procedure for `Foreach` that attempts to minimise the
-- amount of work needed by lifting operations to higher-tensor levels.
-- For example `foreach i . xs ! i + ys ! i` becomes `xs + ys`.
evalForeachTensor :: forall builtin m. EquivalenceLaw ForeachTensorArgs builtin m
evalForeachTensor (ForeachTensorArgs typ d ds fn) = do
  forcedFn <- forceValue fn
  case forcedFn of
    VLam binder (Closure env body) -> do
      let lv = boundCtxLv ctx
      let newEnv = extendEnvWithBound lv binder env
      let newCtx = nameOf binder : ctx
      body' <- forceValue newCtx newEnv body
      result <- liftForeach createForeach lv d typ body'
      return result
    e -> unexpectedExprError "NBE" ("foreachIndex" <+> prettyVerbose e)

liftForeach ::
  forall builtin m.
  (MonadNorm builtin m) =>
  Lv ->
  Value builtin ->
  VType builtin ->
  ForcedValue builtin ->
  m (Maybe (Value builtin))
liftForeach lv d typ forcedBody = do
  return $
    goOp1 liftableTensorOp1s
      <|> goOp2 liftableTensorOp2s
      <|> goAt
      <|> goLiterals tensorLiterals
  where
    appForeach :: Value builtin -> Value builtin
    appForeach newBody = do
      let newBody' = quote mempty (lv + 1) newBody
      let newLam = VLam binder (Closure (namedBoundContextToEnv ctx) newBody')
      unforcedBuiltinApp accessForeachTensorBuiltin $
        ForeachTensorArgs
          { foreachTensorType = t,
            foreachTensorFirstDim = d,
            foreachTensorRemainingDims = ds,
            foreachTensorFn = newLam
          }

    -- Distribute the `forallIndex` across a liftable operation (e.g. `not`).
    -- e.g. `foreach i . op (x(i))` ---> `op (foreach i . x(i))`
    goOp1 :: [TensorOpEvalData TensorOp1Args builtin] -> Maybe (Value builtin)
    goOp1 = \case
      (accessOp1, evalOp1, typ) : remainingOp1s -> case getExpr accessOp1 forcedBody of
        Just (TensorOp1Args ds e) -> Just $ do
          let e' = appForeach e
          unforcedBuiltinApp evalOp1 (TensorOp1Args (Forced $ ICons (Forced INatType) d ds) e')
        _ -> goOp1 remainingOp1s
      [] -> Nothing

    -- Distribute the `forallIndex` across a liftable operation (e.g. `and`).
    -- `foreach i . x(i) op y(i)` ---> `(foreach i . x(i)) op (forall i . y(i))`
    goOp2 :: [TensorOpEvalData TensorOp2Args builtin] -> Maybe (Value builtin)
    goOp2 = \case
      (accessOp, evalOp, typ) : remainingOps -> case getExpr accessOp forcedBody of
        Just (TensorOp2Args ds e1 e2) -> Just $ do
          let e1' = appForeach e1
          let e2' = appForeach e2
          let newSpine = TensorOp2Args (Forced $ ICons (Forced INatType) d ds) e1' e2'
          unforcedBuiltinApp evalOp newSpine
        _ -> goOp2 remainingOps
      [] -> Nothing

    -- `foreach i . xs ! i` ---> `xs`
    -- TODO BUG here! xs may depend on i
    goAt :: Maybe (Value builtin)
    goAt = case getExpr accessAtTensor forcedBody of
      Just (AtTensorArgs _ _ _ xs (VBoundVar lv1 [])) | lv1 == lv -> _ -- Just xs
      _ -> Nothing

    -- `foreach i . c` ---> `broadcast i c`
    goLiterals :: [TensorLiteralAccessor builtin] -> Maybe (Value builtin)
    goLiterals literals = case literals of
      Wrapper Access {..} : remainingLiterals -> case (getExpr value, d) of
        (Just xs, INatLiteral dim) -> Just $ return $ Forced $ mkExpr $ extendTensor dim xs
        _ -> goLiterals value remainingLiterals
      _ -> Nothing

--------
-- at --
--------

-- | An optimised evaluation procedure for `At` that attempts to minimise the
-- amount of work needed by deferring evaluation of operations until after indexing.
evalAtTensor ::
  forall builtin m.
  (HasTensorLiterals builtin, HasLiftableTensorOperations builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  EquivalenceLaw AtTensorArgs builtin m
evalAtTensor (AtTensorArgs t d ds tensor index) = do
  tensor <- forceValue tensor
  goOp1 liftableTensorOp1s
    <|> goOp2 liftableTensorOp2s
    <|> goForeach
  where
    recEvalAt :: Value builtin -> Value builtin
    recEvalAt ys =
      unforcedBuiltinApp accessAtTensorBuiltin $
        AtTensorArgs
          { atType = t,
            atFirstDim = d,
            atRemainingDims = ds,
            atTensor = ys,
            atIndex = index
          }

    -- `(- xs) ! i` ---> `- (xs ! i)
    goOp1 :: [TensorOpEvalData TensorOp1Args builtin] -> Maybe (Value builtin)
    goOp1 = \case
      (accessOp1, evalOp1, _) : remainingOp1s -> case getExpr accessOp1 tensor of
        Just (TensorOp1Args _ xs) -> Just $ do
          let xsi = recEvalAt xs
          unforcedBuiltinApp evalOp1 (TensorOp1Args ds xsi)
        _ -> goOp1 remainingOp1s
      [] -> Nothing

    goOp2 :: ForcedValue builtin -> [TensorOpEvalData TensorOp2Args builtin] -> Maybe (m (Value builtin))
    goOp2 forcedBody = \case
      (accessOp2, evalOp2, _) : remainingOps2 -> case getExpr accessOp2 forcedBody of
        Just (TensorOp2Args _ xs ys) -> Just $ do
          let xsi = recEvalAt xs
          let ysi = recEvalAt ys
          evalOp2 $ TensorOp2Args ds xsi ysi
        _ -> goOp2 forcedBody remainingOps2
      _ -> Nothing

    goForeach :: Maybe (m (Value builtin))
    goForeach = case getExpr accessForeachTensor tensor of
      Just (ForeachTensorArgs _ _ _ fn) -> Just $ do
        return $ UnforcedApp fn [explicit index]
      _ -> Nothing

--------
-- at --
--------

evalReduceAndTensor ::
  forall m builtin.
  (MonadNorm builtin m, PrintableBuiltin builtin, NormalisableBuiltin builtin, BuiltinHasNatType builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin, BuiltinHasTensors builtin, BuiltinHasListLiterals builtin, BuiltinHasNatLiterals builtin, BuiltinHasBoolLiterals builtin, HasLiftableTensorOperations builtin) =>
  EquivalenceLaw TensorReductionArgs builtin m
evalReduceAndTensor args@(TensorReductionArgs dims e tensor) = case e of
  IBoolLiteral True -> go tensor
  _ -> unoptimisedEvalReduceAndTensor args
  where
    go :: Value builtin -> m (Value builtin)
    go = \case
      (getExpr accessAndTensor -> Just (TensorOp2Args ds xs ys)) -> do
        xs' <- go xs
        ys' <- go ys
        evalAnd (TensorOp2Args ds xs' ys')
      vs -> do
        result <- fuseReduceAndForeachTensor ctx evalApp eval tensor
        case result of
          Nothing -> unoptimisedEvalReduceAndTensor (TensorReductionArgs dims e vs)
          Just (newDims, fusedTensor) -> return $ mkExpr accessReduceAnd (TensorReductionArgs newDims e fusedTensor)

-- | An optimised evaluation procedure for `Foreach` that attempts to minimise the
-- amount of work needed by lifting operations to higher-tensor levels.
-- For example `foreach i . xs ! i + ys ! i` becomes `xs + ys`.
fuseReduceAndForeachTensor ::
  (MonadNorm builtin m, PrintableBuiltin builtin, NormalisableBuiltin builtin, BuiltinHasNatType builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin, BuiltinHasTensors builtin, BuiltinHasListLiterals builtin, BuiltinHasNatLiterals builtin, BuiltinHasBoolLiterals builtin, HasLiftableTensorOperations builtin) =>
  Value builtin ->
  m (Maybe (VDims builtin, Value builtin))
fuseReduceAndForeachTensor value = do
  case getExpr accessForeachTensor value of
    Just (ForeachTensorArgs typ d _ (VLam binder (Closure env body))) -> do
      let lv = boundCtxLv ctx
      let newEnv = extendEnvWithBound lv binder env
      let newCtx = nameOf binder : ctx
      body' <- eval newCtx newEnv body
      case getExpr accessReduceAnd body' of
        Just (TensorReductionArgs tensorDims (IBoolLiteral True) tensor) -> do
          (newDims, newTensor) <- fromMaybe (tensorDims, tensor) <$> fuseReduceAndForeachTensor newCtx evalApp eval tensor
          let newTensor' = quote mempty (lv + 1) newTensor
          let newLam = VLam binder (Closure (namedBoundContextToEnv ctx) newTensor')
          let newForeachArgs = ForeachTensorArgs typ d newDims newLam
          newBody' <- unforcedBuiltinApp _ newForeachArgs
          return $ Just (IDimCons d newDims, newBody')
        _ -> return Nothing
    _ -> return Nothing
