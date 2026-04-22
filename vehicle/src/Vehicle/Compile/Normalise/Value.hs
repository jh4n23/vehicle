{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Compile.Normalise.Value where

import Data.Data (Proxy (..))
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Type.Core
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context

forceValue :: (MonadNorm builtin m) => Value builtin -> m (ForcedValue builtin, BlockingMetas)
forceValue = _

{-
forceValue :: (MonadNorm builtin m) => Value builtin -> m (ForcedValue builtin)
forceValue = \case
  Forced value -> return value
  Unforced thunk -> forceThunk thunk
-}
instance TypedEvalScheme (ForcedValue builtin) builtin m where
  forceBuiltin = _
  forceMeta = _
  handleUniverse proxy = Just VUniverse
  handleBoundVar = _
  handlePi = Just VPi
  handleLam = _
  handleRecord = Just $ VRecord
  handleFreeVar = _
  handleRecordAcc = VRecordAcc

-----------------------------------------------------------------------------
-- Value specific

--     let recordType' = thunkifyExpr env recordType
--     let fields' = mapRecordFields (thunkifyExpr env) fields
--     return $ VRecord recordType' $ OMap.fromList fields'

forceValueInCtx ::
  (MonadNormCore builtin m, MonadFreeContext builtin m) =>
  NamedBoundCtx ->
  Value builtin ->
  m (ForcedValue builtin)
forceValueInCtx ctx value = runNameBoundContextT ctx (forceValue value)

evalBuiltin ::
  (MonadNorm builtin m) =>
  builtin ->
  Spine builtin ->
  m (ForcedValue builtin)
evalBuiltin builtin spine = do
  maybeResult <- evalBuiltinDetailed builtin spine
  case maybeResult of
    EvaluationResult value -> forceValue value
    _ -> return $ VBuiltin builtin spine

evalBuiltinDetailed ::
  (MonadNorm builtin m) =>
  builtin ->
  Spine builtin ->
  m (DetailedBuiltinEvaluationResult builtin)
evalBuiltinDetailed b spine = case evaluationScheme b of
  StandardEvaluation evalFn -> case getExpr accessSpine spine of
    Nothing -> return InsufficientArgs
    Just args -> do
      maybeResult <- evalFn args
      case maybeResult of
        Evaluated result -> return $ EvaluationResult result
        Unevaluated blockingArgs -> return $ Blocked blockingArgs
  DerivedEvaluation ident -> do
    forceFreeVar Proxy ident spine
  TypeClassEvaluation -> do
    (inst, remainingArgs) <- findInstanceArg b spine
    forceApp _ inst remainingArgs
  Unevaluable ->
    return DoesNotReduce

{-
forceExpr ::
  (MonadNorm builtin m) =>
  BoundEnv builtin ->
  Expr builtin ->
  m (ForcedValue builtin)
forceExpr env expr = do
  showEntry env expr
  result <- case expr of
    Hole {} -> resolutionError currentPass "Hole"
    Meta _ m -> return $ VMeta m []
    Universe _ u -> return $ VUniverse u
    BoundVar _ v -> forceValue $ lookupIxInEnv env v
    FreeVar _ v -> forceValue =<< lookupIdentValue v
    Builtin _ b -> return $ VBuiltin b []
    Lam _ binder body ->
      return $ VLam (thunkifyBinder env binder) (Closure env body)
    Pi _ binder body ->
      return $ VPi (thunkifyBinder env binder) (Closure env body)
    Let _ bound binder body -> do
      let boundNormExpr = thunkifyExpr env bound
      let newBoundEnv = extendEnvWithDefined boundNormExpr binder env
      forceExpr newBoundEnv body
    App fun args -> do
      forceApp (thunkifyExpr env fun) (thunkifyArgs env args)
    Record _p recordType fields -> do
      let recordType' = thunkifyExpr env recordType
      let fields' = mapRecordFields (thunkifyExpr env) fields
      return $ VRecord recordType' $ OMap.fromList fields'
    RecordProj _p recordType record field -> do
      record' <- forceExpr env record
      case record' of
        VRecord _ fields -> do
          let fieldValue = lookupRecordFieldS fields field
          forceValue fieldValue
        _ -> do
          let recordType' = thunkifyExpr env recordType
          return $ VRecordAcc recordType' (Forced record') field []

  showExit result
  return result

forceApp ::
  (MonadNorm builtin m) =>
  Value builtin ->
  Spine builtin ->
  m (ForcedValue builtin)
forceApp fun args = do
  forcedFun <- forceValue fun
  case args of
    [] -> return forcedFun
    (a : as) -> do
      showApp forcedFun args
      result <- case forcedFun of
        VMeta v spine -> return $ VMeta v (spine <> args)
        VBoundVar v spine -> return $ VBoundVar v (spine <> args)
        VFreeVar v spine -> return $ VFreeVar v (spine <> args)
        VRecordAcc recordType record field spine -> return $ VRecordAcc recordType record field (spine <> args)
        VBuiltin b spine -> evalBuiltin b (spine <> args)
        VLam binder closure
          | not (visibilityMatches binder a) ->
              visibilityError forcedFun a
          | otherwise -> do
              -- TODO force deeply?
              let body = extendClosure closure binder (argExpr a)
              forceApp body as
        VUniverse {} -> unexpected "VUniverse"
        VPi {} -> unexpected "VPi"
        VRecord {} -> unexpected "VRecord"
      showAppExit result
      return result
  where
    unexpected name = unexpectedExprError currentPass (name <+> prettyVerbose args)
-}
