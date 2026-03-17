module Vehicle.Compile.Normalise.NBE
  ( MonadNorm,
    evalBuiltin,
    forceValue,
    forceValueInCtx,
    forceThunk,
    forceClosure,
    extendClosureWithBound,
    forceExpr,
    forceExprInEmptyEnv,
    findInstanceArg,
    evalBuiltinDetailed,
  )
where

import Data.Data (Proxy (..))
import Data.Map.Ordered.Strict qualified as OMap
import GHC.Stack (HasCallStack)
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Code.Interface (IsArgs (..))
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context.Class (MonadFreeContext (..))

-----------------------------------------------------------------------------
-- Evaluation

forceExprInEmptyEnv ::
  (MonadNorm builtin m) =>
  Expr builtin ->
  m (ForcedValue builtin)
forceExprInEmptyEnv = forceExpr emptyBoundEnv

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

forceThunk :: (MonadNorm builtin m) => Thunk builtin -> m (ForcedValue builtin)
forceThunk (Thunk env builtin) = forceExpr env builtin

forceClosure :: (MonadNorm builtin m) => VBinder builtin -> Closure builtin -> m (ForcedValue builtin)
forceClosure binder closure = forceValue =<< extendClosureWithBound binder closure

forceValue :: (MonadNorm builtin m) => Value builtin -> m (ForcedValue builtin)
forceValue = \case
  Forced value -> return value
  Unforced thunk -> forceThunk thunk
  UnforcedApp f xs -> forceApp f xs

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
    value <- lookupIdentValue ident
    return $ EvaluationResult $ UnforcedApp value spine
  TypeClassEvaluation -> do
    (inst, remainingArgs) <- findInstanceArg b spine
    return $ EvaluationResult $ UnforcedApp inst remainingArgs
  Unevaluable ->
    return DoesNotReduce

lookupIdentValue :: forall builtin m. (MonadFreeContext builtin m) => Identifier -> m (Value builtin)
lookupIdentValue ident = do
  decl <- getDeclEntry (Proxy @builtin) ident
  return $ case decl of
    DefFunction _ _ _ _ value -> thunkifyExpr emptyBoundEnv value
    _ -> Forced $ VFreeVar ident []

findInstanceArg :: (MonadLogger m, Show op) => op -> [GenericArg a] -> m (a, [GenericArg a])
findInstanceArg op = \case
  (InstanceArg _ inst : xs) -> return (inst, xs)
  (_ : xs) -> findInstanceArg op xs
  [] -> developerError $ "Malformed type class operation:" <+> pretty (show op)

-----------------------------------------------------------------------------
-- Other

currentPass :: Doc ()
currentPass = "normalisation by evaluation"

showEntry :: (MonadNorm builtin m) => BoundEnv builtin -> Expr builtin -> m ()
showEntry _ _ = return ()

showExit :: (MonadNorm builtin m) => ForcedValue builtin -> m ()
showExit _ = return ()

{-
showEntry :: (MonadNorm builtin m) => BoundEnv builtin -> Expr builtin -> m ()
showEntry _ctx env expr = do
  logDebug MaxDetail $ "nbe-entry" <+> prettyFriendly (WithContext expr (envToCtx env)) -- <+> "   (ctx =" <+> pretty ctx <> "," <+> "env =" <+> prettyFriendly (WithContext env ctx) <+> ")"
  -- logDebug MidDetail $ "nbe-entry" <+> prettyFriendly (WithContext expr (envToCtx env)) <+> "   { env =" <+> prettyFriendly env <+> "}"
  -- logDebug MidDetail $ "nbe-entry" <+> prettyVerbose expr <+> "   { env=" <+> prettyVerbose env <+> "}"
  incrCallDepth
  return ()

showExit :: (MonadNorm builtin m) => Value builtin -> m ()
showExit ctx result = do
  decrCallDepth
  -- logDebug MidDetail $ "nbe-exit" <+> prettyVerbose result
  logDebug MaxDetail $ "nbe-exit" <+> prettyFriendly (WithContext result ctx)
  return ()
-}

showApp :: (MonadNorm builtin m) => ForcedValue builtin -> Spine builtin -> m ()
showApp _ _ = return ()

showAppExit :: (MonadNorm builtin m) => ForcedValue builtin -> m ()
showAppExit _ = return ()

{-
showApp :: (MonadNorm builtin m) => Value builtin -> Spine builtin -> m ()
showApp _ctx fun spine = do
  logDebug MaxDetail $ "nbe-app:" <+> prettyVerbose fun <+> "@" <+> prettyVerbose spine
  incrCallDepth
  return ()

showAppExit :: (MonadNorm builtin m) => Value builtin -> m ()
showAppExit _ctx result = do
  decrCallDepth
  logDebug MaxDetail $ "nbe-app-exit:" <+> prettyVerbose result
  return ()
-}

visibilityError ::
  (HasCallStack, MonadNorm builtin m) =>
  ForcedValue builtin ->
  VArg builtin ->
  m b
visibilityError fun arg = do
  funDoc <- prettyFriendlyInCtx fun
  argsDoc <- prettyFriendlyInCtx (argExpr arg)
  let visDoc = pretty (visibilityOf arg)
  developerError $
    unexpectedExpr currentPass (visDoc <+> "arg" <+> squotes argsDoc)
      <+> "Does not match function's visibility:"
      <> line
      <> indent 2 funDoc
