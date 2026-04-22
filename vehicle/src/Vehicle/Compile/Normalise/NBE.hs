module Vehicle.Compile.Normalise.NBE
  ( MonadNorm,
    forceThunk,
    extendClosureWithBound,
    findInstanceArg,
  )
where

import Data.Data (Proxy (..))
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import GHC.Stack (HasCallStack)
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Prelude
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context.Class (MonadFreeContext (..))

-----------------------------------------------------------------------------
-- Evaluation

forceThunk ::
  forall typedExpr builtin m.
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  Thunk builtin ->
  m typedExpr
forceThunk (Thunk env expr) = logForce env expr $
  case expr of
    Hole {} -> resolutionError currentPass "Hole"
    -- Non-neutral
    BoundVar _ v -> forceBoundVar env v
    FreeVar _ v -> forceFreeVar (Proxy @builtin) v
    Builtin _ b -> forceBuiltin b []
    Meta _ m -> forceMeta @typedExpr @builtin m []
    Let _ bound binder body -> forceLet env bound binder body
    App fun args -> forceApp (Thunk env fun) env args
    RecordProj _p recordType record field -> forceRecordAcc env recordType record field
    -- Values
    Universe _ u -> case handleUniverse (Proxy @builtin) of
      Just handler -> handler u
      Nothing -> developerError "ill-typed Universe"
    Lam _ binder body -> case handleLam @typedExpr @builtin of
      Just handler -> handler binder (Closure env body)
      Nothing -> developerError "ill-typed Lam"
    Pi _ binder body -> case handlePi @typedExpr @builtin of
      Just handler -> handler binder (Closure env body)
      Nothing -> developerError "ill-typed Pi"
    Record _p recordType fields -> case handleRecord @typedExpr @builtin of
      Just handler -> handler recordType fields
      Nothing -> developerError "ill-typed Record"

forceApp ::
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  Thunk builtin ->
  BoundEnv builtin ->
  NonEmpty (Arg builtin) ->
  m typedExpr
forceApp fn argsEnv args@(a :| as) = do
  forcedFun <- forceThunk fn
  showApp forcedFun args
  showAppExit $ case forcedFun of
    VFunctionBuiltin b spine -> forceBuiltin b (spine <> NonEmpty.toList args)
    VFunctionFreeVar v spine -> handleFreeVar v (spine <> NonEmpty.toList args)
    VFunctionMeta v spine -> forceMeta v (spine <> NonEmpty.toList args)
    VFunctionBoundVar v spine -> handleBoundVar v (spine <> NonEmpty.toList args)
    VFunctionRecordAcc recordType record field spine -> handleRecordAcc recordType record field (spine <> NonEmpty.toList args)
    VFunctionLam binder closure
      | not (visibilityMatches binder a) ->
          visibilityError fn forcedFun a
      | otherwise -> do
          let body = extendClosure closure binder (Thunk argsEnv $ argExpr a)
          case as of
            a' : as' -> forceApp body argsEnv (a' :| as')
            _ -> forceThunk body

forceFreeVar ::
  forall typedExpr builtin m.
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  Proxy builtin ->
  Identifier ->
  m typedExpr
forceFreeVar proxy ident = do
  decl <- getDeclEntry proxy ident
  case decl of
    DefFunction _ _ _ _ body -> forceThunk $ Thunk emptyBoundEnv body
    _ -> handleFreeVar @typedExpr @builtin ident []

forceBoundVar ::
  forall typedExpr builtin m.
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  BoundEnv builtin ->
  Ix ->
  m typedExpr
forceBoundVar env ix =
  case lookupIxInEnv env ix of
    Bound thunk -> forceThunk thunk
    Unbound lv -> handleBoundVar @typedExpr @builtin lv []

forceLet ::
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  BoundEnv builtin ->
  Expr builtin ->
  Binder builtin ->
  Expr builtin ->
  m typedExpr
forceLet env bound binder body = do
  let boundNormExpr = Thunk env bound
  let newBoundEnv = extendEnvWithDefined boundNormExpr binder env
  forceThunk $ Thunk newBoundEnv body

forceRecordAcc ::
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  BoundEnv builtin ->
  Type builtin ->
  Expr builtin ->
  FieldName ->
  m typedExpr
forceRecordAcc env recordType record field = do
  record' <- forceThunk $ Thunk env record
  case record' of
    VRecordRecord _ fields -> do
      let fieldValue = lookupRecordField fields field
      forceThunk $ Thunk env fieldValue
    _ -> handleRecordAcc recordType record' field []

findInstanceArg :: (MonadLogger m, Show op) => op -> [GenericArg a] -> m (a, [GenericArg a])
findInstanceArg op = \case
  (InstanceArg _ inst : xs) -> return (inst, xs)
  (_ : xs) -> findInstanceArg op xs
  [] -> developerError $ "Malformed type class operation:" <+> pretty (show op)

-----------------------------------------------------------------------------
-- Other

currentPass :: Doc ()
currentPass = "normalisation by evaluation"

logForce :: (MonadReadableNameContext m) => BoundEnv builtin -> Expr builtin -> m typedExpr -> m typedExpr
logForce _ _ result = result

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

showApp :: (MonadNorm builtin m) => FunctionExpr builtin -> NonEmpty (Arg builtin) -> m ()
showApp _ _ = return ()

showAppExit :: (MonadReadableNameContext m) => m typedExpr -> m typedExpr
showAppExit e = e

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
  Thunk builtin ->
  FunctionExpr builtin ->
  Arg builtin ->
  m b
visibilityError funThunk fun arg = do
  funDoc <- prettyFriendlyInCtx _ -- (toExpr fun)
  argsDoc <- prettyFriendlyInCtx (argExpr arg)
  let visDoc = pretty (visibilityOf arg)
  developerError $
    unexpectedExpr currentPass (visDoc <+> "arg" <+> squotes argsDoc)
      <+> "Does not match function's visibility:"
      <> line
      <> indent 2 funDoc
