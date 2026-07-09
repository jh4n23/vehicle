module Vehicle.Compile.Normalise.RewriteRules
  ( rewriteReduceAndTensor,
    rewriteForeachTensor,
    rewriteAtTensor,
  )
where

import Control.Applicative ((<|>))
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Foldable (asum)
import Vehicle.Compile.Normalise.BuiltinForced
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Normalise.NBEForced
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Data.Builtin.Core.BasicOperations (ComparisonOp (..))
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Print (PrintableBuiltin)
import Vehicle.Data.Builtin.Standard.Core (ComparisonOp)
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Code.Interface
import Vehicle.Data.Tensor
import Vehicle.Data.Variable.Bound.Context.Name

type MonadRewrite builtin m =
  ( MonadNorm builtin m,
    MonadNameContext m,
    NormalisableBuiltin builtin,
    BuiltinHasNatType builtin,
    BuiltinHasIndexLiterals builtin,
    BuiltinHasRatLiterals builtin,
    BuiltinHasForeach builtin,
    BuiltinHasTensors builtin,
    BuiltinHasListLiterals builtin,
    BuiltinHasNatLiterals builtin,
    BuiltinHasBoolLiterals builtin,
    HasTensorLiterals ForcedValue builtin,
    HasLiftableTensorOperations ForcedValue Thunk builtin,
    BuiltinHasRatType builtin
  )

rewriteTensor ::
  forall builtin m.
  (MonadRewrite builtin m) =>
  Thunk builtin ->
  m (BuiltinEvaluationResult ForcedValue Thunk builtin)
rewriteTensor value = do
  forcedValue <- forceThunk @builtin @m @(ForcedValue builtin) value
  case forcedValue of
    (getExpr accessAtTensor -> Just args) -> rewriteAtTensor args
    (getExpr accessForeachTensor -> Just args) -> rewriteForeachTensor args
    (getExpr accessReduceAnd -> Just args) -> rewriteReduceAndTensor args
    (getExpr accessReduceOr -> Just args) -> rewriteReduceOrTensor args
    (getExpr accessReduceMinRat -> Just args) -> rewriteReduceMinTensor args
    (getExpr accessReduceMaxRat -> Just args) -> rewriteReduceMaxTensor args
    (getExpr accessReduceAddRat -> Just args) -> rewriteReduceAddTensor args
    (getExpr accessReduceMulRat -> Just args) -> rewriteReduceMulTensor args
    _ -> return $ Unevaluable []

-----------------------------------------------------------------------------
-- ReduceAnd

rewriteReduceTensor ::
  forall m builtin b.
  (MonadRewrite builtin m) =>
  Doc b ->
  TensorOp2Accessor ForcedValue Thunk builtin ->
  EvalSimple ForcedValue Thunk TensorReductionArgs builtin m ->
  Maybe ((ComparisonOp, TensorOp2Args (Thunk builtin)) -> m (BuiltinEvaluationResult ForcedValue Thunk builtin)) ->
  EvalSimple ForcedValue Thunk TensorReductionArgs builtin m
rewriteReduceTensor opName accessBop evalReductionOp rewriteComparison (TensorReductionArgs dims t) = do
  maybeResult <- rewriteTensor t
  case maybeResult of
    Evaluated t' -> go t'
    Unevaluable {} -> go t
  where
    go :: Thunk builtin -> m (BuiltinEvaluationResult ForcedValue Thunk builtin)
    go tensor = logRewrite opName tensor $ do
      forcedTensor <- force tensor
      case forcedTensor of
        (getExpr accessBop -> Just (TensorOp2Args ds xs ys)) -> do
          xs' <- goRec xs
          ys' <- goRec ys
          return $
            Evaluated $
              exprToThunk $
                mkExpr accessBop $
                  TensorOp2Args
                    { tensorOp2Dims = ds,
                      tensorOp2Arg1 = xs',
                      tensorOp2Arg2 = ys'
                    }
        (getExpr accessCompareRatTensorPointwise -> Just args) ->
          case rewriteComparison of
            Nothing -> return $ Unevaluable []
            Just rewrite -> rewrite args
        _ -> do
          evalReductionOp (TensorReductionArgs dims (exprToThunk forcedTensor))

    goRec :: Thunk builtin -> m (Thunk builtin)
    goRec tensor = do
      maybeResult <- go tensor
      case maybeResult of
        Evaluated result -> return result
        Unevaluable {} ->
          return $
            Forced $
              mkExpr accessReduceAnd $
                TensorReductionArgs
                  { tensorReductionDims = dims,
                    tensorReductionTensor = tensor
                  }

rewriteReduceAndTensor ::
  forall m builtin.
  (MonadRewrite builtin m) =>
  EvalSimple ForcedValue Thunk TensorReductionArgs builtin m
rewriteReduceAndTensor = rewriteReduceTensor "reduceAnd" accessAndTensor evalReduceAndTensor (Just rewritePointwiseComparison)
  where
    rewritePointwiseComparison :: (ComparisonOp, TensorOp2Args (Thunk builtin)) -> m (BuiltinEvaluationResult ForcedValue Thunk builtin)
    rewritePointwiseComparison (op, TensorOp2Args ds xs ys)
      | op == Ne = return $ Unevaluable []
      | otherwise = do
          forcedDims <- force ds
          case forcedDims of
            IDimCons fd fds -> do
              let args =
                    TensorReduceComparisonArgs
                      { tensorReduceOp2Dim = fd,
                        tensorReduceOp2Dims = fds,
                        tensorReduceOp2Arg1 = xs,
                        tensorReduceOp2Arg2 = ys
                      }
              return $ Evaluated $ Forced $ mkExpr accessCompareRatTensorReduced (op, args)
            _ -> return $ Unevaluable []

rewriteReduceOrTensor ::
  (MonadRewrite builtin m) =>
  EvalSimple ForcedValue Thunk TensorReductionArgs builtin m
rewriteReduceOrTensor = rewriteReduceTensor "reduceOr" accessOrTensor evalReduceOrTensor Nothing

rewriteReduceMinTensor ::
  (MonadRewrite builtin m) =>
  EvalSimple ForcedValue Thunk TensorReductionArgs builtin m
rewriteReduceMinTensor = rewriteReduceTensor "reduceMin" accessMinRatTensor evalReduceMinRatTensor Nothing

rewriteReduceMaxTensor ::
  (MonadRewrite builtin m) =>
  EvalSimple ForcedValue Thunk TensorReductionArgs builtin m
rewriteReduceMaxTensor = rewriteReduceTensor "reduceMax" accessMaxRatTensor evalReduceMaxRatTensor Nothing

rewriteReduceAddTensor ::
  (MonadRewrite builtin m) =>
  EvalSimple ForcedValue Thunk TensorReductionArgs builtin m
rewriteReduceAddTensor = rewriteReduceTensor "reduceAdd" accessAddRatTensor evalReduceAddRatTensor Nothing

rewriteReduceMulTensor ::
  (MonadRewrite builtin m) =>
  EvalSimple ForcedValue Thunk TensorReductionArgs builtin m
rewriteReduceMulTensor = rewriteReduceTensor "reduceMul" accessMulRatTensor evalReduceMulRatTensor Nothing

-----------------------------------------------------------------------------
-- At

-- | An optimised evaluation procedure for `At` that attempts to minimise the
-- amount of work needed by deferring evaluation of operations until after indexing.
-- For example:
--    `(xs + ys) ! i` becomes `xs ! i + ys ! i`.
--    `(foreach j . f j) ! i` becomes `f i`
rewriteAtTensor ::
  forall builtin m.
  (MonadRewrite builtin m) =>
  EvalSimple ForcedValue Thunk AtTensorArgs builtin m
rewriteAtTensor args@(AtTensorArgs tElem d ds t index) = go t
  where
    go :: Thunk builtin -> m (BuiltinEvaluationResult ForcedValue Thunk builtin)
    go value = logRewrite "at" value $ do
      maybeRewrittenBody <- rewriteTensor value
      forcedTensor <- case maybeRewrittenBody of
        Unevaluable {} -> forceThunk value
        Evaluated rewrittenBody -> forceThunk rewrittenBody
      let maybeResult =
            goOp1 forcedTensor liftableTensorOp1s
              <|> goOp2 forcedTensor liftableTensorOp2s
              <|> goForeach forcedTensor
      case maybeResult of
        Nothing -> evalAtTensor args
        Just result -> Evaluated . exprToThunk <$> result

    recEvalAt :: Thunk builtin -> m (Thunk builtin)
    recEvalAt ys =
      forceEvaluation accessAtTensor rewriteAtTensor $
        AtTensorArgs tElem d ds ys index

    goOp1 :: ForcedValue builtin -> [TensorOpEvalData ForcedValue Thunk TensorOp1Args builtin] -> Maybe (m (ForcedValue builtin))
    goOp1 forcedTensor = \case
      (accessOp1, _) : remainingOp1s -> case getExpr accessOp1 forcedTensor of
        Just (TensorOp1Args _ xs) -> Just $ do
          xsi <- recEvalAt xs
          return $ mkExpr accessOp1 (TensorOp1Args ds xsi)
        _ -> goOp1 forcedTensor remainingOp1s
      [] -> Nothing

    goOp2 :: ForcedValue builtin -> [TensorOpEvalData ForcedValue Thunk TensorOp2Args builtin] -> Maybe (m (ForcedValue builtin))
    goOp2 forcedTensor = \case
      (accessOp2, _) : remainingOps2 -> case getExpr accessOp2 forcedTensor of
        Just (TensorOp2Args _ xs ys) -> Just $ do
          xsi <- recEvalAt xs
          ysi <- recEvalAt ys
          return $ mkExpr accessOp2 $ TensorOp2Args ds xsi ysi
        _ -> goOp2 forcedTensor remainingOps2
      _ -> Nothing

    goForeach :: ForcedValue builtin -> Maybe (m (ForcedValue builtin))
    goForeach forcedTensor = case getExpr accessForeachTensor forcedTensor of
      Just (ForeachTensorArgs _ _ _ fn) -> Just $ do
        forceApp fn [explicit index]
      _ -> Nothing

-----------------------------------------------------------------------------
-- Foreach

-- | An optimised evaluation procedure for `Foreach` that attempts to minimise the
-- amount of work needed by lifting operations to higher-tensor levels.
-- For example `foreach i . xs ! i + ys ! i` becomes `xs + ys`.
rewriteForeachTensor ::
  forall builtin m.
  (MonadRewrite builtin m) =>
  EvalSimple ForcedValue Thunk ForeachTensorArgs builtin m
rewriteForeachTensor (ForeachTensorArgs _t d ds fn) =
  case getExpr accessForcedLamC fn of
    Just (binder, closure) -> do
      ctx <- getNameContext
      let lv = boundCtxLv ctx
      let body = extendClosureWithBound closure binder lv

      let createForeachArgs tElem newBody = do
            let newBody' = quote mempty (lv + 1) newBody
            let newLam = mkExpr accessForcedLamC (binder, Closure (namedBoundContextToEnv ctx) newBody')
            ForeachTensorArgs tElem d ds newLam

      addNameToContext binder $ do
        maybeRewrittenBody <- rewriteTensor body
        body' <- case maybeRewrittenBody of
          Unevaluable {} -> Forced <$> forceThunk body
          Evaluated rewrittenBody -> return rewrittenBody
        liftForeach ctx createForeachArgs lv d body'
    _ -> unexpectedExprError "NBE" "foreachIndex"

liftForeach ::
  forall builtin m.
  (MonadRewrite builtin m) =>
  NamedBoundCtx ->
  (Thunk builtin -> Thunk builtin -> ForeachTensorArgs (Thunk builtin)) ->
  Lv ->
  Thunk builtin ->
  Thunk builtin ->
  m (BuiltinEvaluationResult ForcedValue Thunk builtin)
liftForeach outputCtx createForeachArgs lv dim = go
  where
    go ::
      Thunk builtin ->
      m (BuiltinEvaluationResult ForcedValue Thunk builtin)
    go body = logForeachRewrite outputCtx createForeachArgs "foreach" body $ do
      forcedBody <- force body
      -- Try each of the following in turn until it works.
      maybeResult <-
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
      return $ maybe (Unevaluable []) Evaluated maybeResult

    goRec ::
      ForcedValue builtin ->
      Thunk builtin ->
      m (Thunk builtin)
    goRec typ body = do
      maybeLiftedResult <- go body
      case maybeLiftedResult of
        Evaluated liftedResult -> return liftedResult
        Unevaluable {} -> forceEvaluation accessForeachTensor evalForeachTensor (createForeachArgs (Forced typ) body)

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

{-

fuseReduceAndForeachTensor ::
  forall m expr thunk builtin.
  (MonadLogger m, PrintableBuiltin builtin, Quote (expr builtin) (Expr builtin), HasBuiltinConstructor expr thunk, HasLambdaConstructor expr thunk Closure, NormalisableBuiltin builtin, BuiltinHasNatType builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin, BuiltinHasTensors builtin, BuiltinHasListLiterals builtin, BuiltinHasNatLiterals builtin, BuiltinHasBoolLiterals builtin, HasTensorLiterals expr builtin, HasLiftableTensorOperations expr thunk builtin) =>
  NamedBoundCtx ->
  expr builtin ->
  m (Maybe (thunk builtin, thunk builtin))
fuseReduceAndForeachTensor ctx value = do
  fusionEnter ctx value
  fusionExit ctx =<< case getExpr accessForeachTensor value of
    Just (ForeachTensorArgs typ d _ (getExpr accessForcedLamC -> Just (binder, Closure env body))) -> do
      let lv = boundCtxLv ctx
      let newEnv = extendEnvWithBound lv binder env
      let newCtx = nameOf binder : ctx
      body' <- eval newCtx newEnv body
      case getExpr accessReduceAnd body' of
        Just (TensorReductionArgs (tensorDims :: thunk builtin) tensor) -> do
          (newDims, newTensor) <- fromMaybe (tensorDims, tensor) <$> fuseReduceAndForeachTensor @m @expr @thunk newCtx (force tensor)
          let newTensor' = quote @(expr builtin) mempty (lv + 1) (force newTensor)
          let newLam = mkExpr accessForcedLamC (binder, Closure (namedBoundContextToEnv ctx) newTensor')
          let newForeachArgs = ForeachTensorArgs typ d newDims newLam
          newBody' <- evalForeachTensor newCtx newForeachArgs
          return $ Just (exprToThunk $ IDimCons d newDims, exprToThunk newBody')
        _ -> return Nothing
    _ -> return Nothing

-}

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

logRewrite ::
  (MonadNormBuiltin m, PrintableBuiltin builtin) =>
  Doc b ->
  Thunk builtin ->
  m (BuiltinEvaluationResult expr Thunk builtin) ->
  m (BuiltinEvaluationResult expr Thunk builtin)
logRewrite op input outputFn = do
  logDebugM MaxDetail $ do
    inputDoc <- prettyFriendlyInCtx input
    return $ "rewrite-" <> op <> "-enter:" <+> inputDoc
  incrCallDepth

  output <- outputFn

  decrCallDepth
  logDebugM MaxDetail $ do
    outputDoc <- case output of
      Unevaluable {} -> return ""
      Evaluated result -> prettyFriendlyInCtx result
    return $ "rewrite-" <> op <> "-exit:" <+> outputDoc

  return output

logForeachRewrite ::
  (MonadNormBuiltin m, HasRatType ForcedValue Thunk builtin, BuiltinHasForeach builtin, PrintableBuiltin builtin) =>
  NamedBoundCtx ->
  (Thunk builtin -> Thunk builtin -> ForeachTensorArgs (Thunk builtin)) ->
  Doc b ->
  Thunk builtin ->
  m (BuiltinEvaluationResult ForcedValue Thunk builtin) ->
  m (BuiltinEvaluationResult ForcedValue Thunk builtin)
logForeachRewrite outputCtx createForeachArgs op input outputFn = do
  logDebugM MaxDetail $ do
    let expr = mkExpr accessForeachTensor (createForeachArgs (Forced IRatType) input)
    let inputDoc = prettyFriendly (WithContext expr outputCtx)
    return $ "rewrite-" <> op <> "-enter:" <+> inputDoc
  incrCallDepth

  output <- outputFn

  decrCallDepth
  logDebugM MaxDetail $ do
    outputDoc <- case output of
      Unevaluable {} -> return ""
      Evaluated result -> return $ prettyFriendly (WithContext result outputCtx)
    return $ "rewrite-" <> op <> "-exit:" <+> outputDoc

  return output
