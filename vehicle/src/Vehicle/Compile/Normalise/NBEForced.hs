{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Compile.Normalise.NBEForced
  ( MonadNorm,
    eval,
    forceApplication,
    forceThunk,
    forceFreeVar,
    forceInEmptyEnv,
    findInstanceArg,
    forceRecordAcc,
  )
where

import Control.Monad (when)
import Data.Bifunctor (Bifunctor (..))
import Data.Data (Proxy (..))
import Data.List.NonEmpty as NonEmpty (toList)
import Data.Map.Ordered qualified as OMap
import GHC.Stack (HasCallStack)
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Normalise.TypedValueForced
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendlyEmptyCtx)
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Variable.Bound.Context.Name (prettyFriendlyInCtx)
import Vehicle.Data.Variable.Free.Context.Class (MonadFreeContext (..))

-----------------------------------------------------------------------------
-- Evaluation

instance
  ( MonadNorm builtin m,
    TypedEvalScheme (ForcedValue builtin) builtin m
  ) =>
  NormalisableExpr ForcedValue Thunk builtin m
  where
  force = forceThunk
  forceApp = forceApplication

forceThunk ::
  (MonadNorm builtin m, TypedEvalScheme typedExpr builtin m) =>
  Thunk builtin ->
  m typedExpr
forceThunk = \case
  Forced value -> patternMatch value
  Unforced env expr -> eval env expr

eval ::
  forall typedExpr builtin m.
  (MonadNorm builtin m, TypedEvalScheme typedExpr builtin m) =>
  BoundEnv builtin ->
  Expr builtin ->
  m typedExpr
eval env expr = do
  showEntry env expr
  result <- case expr of
    Hole {} -> resolutionError currentPass "Hole"
    -- Always handlable
    BoundVar _ v -> forceBoundVar env v
    FreeVar _ v -> forceFreeVar v []
    Builtin _ b -> forceBuiltin b []
    Meta _ m -> forceMeta m []
    Let _ bound binder body -> forceLet env bound binder body
    RecordProj _ typ record field ->
      forceRecordAcc (Unforced env typ) (Unforced env record) field
    App fun args -> forceApplication (Unforced env fun) (fmap (Unforced env) <$> NonEmpty.toList args)
    -- Possibly handled
    Universe _ u -> case handleUniverse (Proxy @builtin) of
      Just handler -> handler u
      Nothing -> developerError "ill-typed Universe"
    Lam _ binder body -> case handleLam @typedExpr @builtin of
      Just handler -> handler (fmap (Unforced env) binder) (Closure env body)
      Nothing -> developerError "ill-typed Lam"
    Pi _ binder body -> case handlePi @typedExpr @builtin of
      Just handler -> handler (fmap (Unforced env) binder) (Closure env body)
      Nothing -> developerError "ill-typed Pi"
    Record _p recordType fields -> case handleRecord @typedExpr @builtin of
      Just handler -> handler (Unforced env recordType) $ OMap.fromList $ fmap (second (Unforced env)) fields
      Nothing -> developerError "ill-typed Record"

  showExit result
  return result

forceApplication ::
  (MonadNorm builtin m, TypedEvalScheme typedExpr builtin m) =>
  Thunk builtin ->
  [UnforcedArg builtin] ->
  m typedExpr
forceApplication fun [] = forceThunk fun
forceApplication fun args@(a : as) = do
  forcedFun <- forceThunk fun
  case forcedFun of
    VBuiltin b spine ->
      forceBuiltin b (spine <> args)
    VFreeVar v spine ->
      handleFreeVar v (spine <> args)
    VMeta v spine ->
      forceMeta v (spine <> args)
    VBoundVar v spine ->
      handleBoundVar v (spine <> args)
    VRecordAcc recordType record field spine ->
      handleRecordAcc recordType record field (spine <> args)
    VLam binder closure
      | not (visibilityMatches binder a) ->
          visibilityError fun a
      | otherwise -> do
          let body = extendClosure closure binder (argExpr a)
          when (isExplicit a) $
            logDebugM MaxDetail $ do
              fDoc <- prettyFriendlyInCtx forcedFun
              aDoc <- prettyFriendlyInCtx $ argExpr a
              bDoc <- prettyFriendlyInCtx body
              return $
                "applying " <+> squotes fDoc
                  <> line
                  <> "  to     " <+> squotes aDoc
                  <> line
                  <> "  getting" <+> squotes bDoc
          forceApplication body as
    VPi {} -> illTyped "VPi"
    VRecord {} -> illTyped "VRecord"
    VUniverse {} -> illTyped "VUniverse"
  where
    illTyped e = developerError $ "ill-typed function" <+> e

forceLet ::
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  BoundEnv builtin ->
  Expr builtin ->
  Binder builtin ->
  Expr builtin ->
  m typedExpr
forceLet env bound binder body = do
  let boundNormExpr = Unforced env bound
  let newBoundEnv = extendEnvWithDefined boundNormExpr binder env
  eval newBoundEnv body

forceRecordAcc ::
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  UnforcedType builtin ->
  Thunk builtin ->
  FieldName ->
  m typedExpr
forceRecordAcc recordType record field = do
  record' <- forceThunk record
  case record' of
    VRecord _ fields -> do
      let fieldValue = lookupRecordFieldS fields field
      forceThunk fieldValue
    _ -> handleRecordAcc recordType (Forced record') field []

forceBoundVar ::
  forall typedExpr builtin m.
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  BoundEnv builtin ->
  Ix ->
  m typedExpr
forceBoundVar env ix = forceThunk $ lookupIxInEnv env ix

forceFreeVar ::
  forall typedExpr builtin m.
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  Identifier ->
  UnforcedSpine builtin ->
  m typedExpr
forceFreeVar ident args = do
  decl <- getDeclEntry (Proxy @builtin) ident
  case decl of
    DefFunction _ _ _ _ value -> do
      logDebug MaxDetail $ "substitute" <+> quotePretty (nameOf ident) <+> "for" <+> squotes (prettyFriendlyEmptyCtx value)
      forceApplication (Unforced emptyBoundEnv value) args
    _ -> handleFreeVar ident args

forceBuiltin ::
  forall typedExpr builtin m.
  (TypedEvalScheme typedExpr builtin m, MonadNorm builtin m) =>
  builtin ->
  UnforcedSpine builtin ->
  m typedExpr
forceBuiltin b spine = case evalScheme b of
  Eval {} -> handleBuiltin b spine
  None -> handleBuiltin b spine
  Derived ident -> forceFreeVar ident spine
  TypeClassOp -> do
    (inst, remainingArgs) <- findInstanceArg b spine
    forceApplication inst remainingArgs

findInstanceArg :: (MonadLogger m, Show op) => op -> [GenericArg a] -> m (a, [GenericArg a])
findInstanceArg op = \case
  (InstanceArg _ inst : xs) -> return (inst, xs)
  (_ : xs) -> findInstanceArg op xs
  [] -> developerError $ "Malformed type class operation:" <+> pretty (show op)

-----------------------------------------------------------------------------
-- Specialised methods for when the normalised builtins is the same as the
-- unnormalised builtins and has the standard set of datatypes.

forceInEmptyEnv :: (MonadNorm builtin m) => Expr builtin -> m (ForcedValue builtin)
forceInEmptyEnv = eval emptyBoundEnv

-----------------------------------------------------------------------------
-- Other

currentPass :: Doc ()
currentPass = "normalisation by evaluation"

showEntry :: (MonadNorm builtin m) => BoundEnv builtin -> Expr builtin -> m ()
showEntry _ _ = return ()

showExit :: (MonadLogger m) => forcedExpr -> m ()
showExit _ = return ()

{-
showEntry :: (MonadNorm builtin m) => BoundEnv builtin -> Expr builtin -> m ()
showEntry _ctx boundEnv expr = do
  logDebug MaxDetail $ "nbe-entry" <+> prettyFriendly (WithContext expr (boundEnvToCtx boundEnv)) -- <+> "   (ctx =" <+> pretty ctx <> "," <+> "boundEnv =" <+> prettyFriendly (WithContext boundEnv ctx) <+> ")"
  -- logDebug MidDetail $ "nbe-entry" <+> prettyFriendly (WithContext expr (boundEnvToCtx boundEnv)) <+> "   { boundEnv =" <+> prettyFriendly boundEnv <+> "}"
  -- logDebug MidDetail $ "nbe-entry" <+> prettyVerbose expr <+> "   { boundEnv=" <+> prettyVerbose boundEnv <+> "}"
  incrCallDepth
  return ()

showExit :: (MonadNorm builtin m) => ForcedValue builtin -> m ()
showExit ctx result = do
  decrCallDepth
  -- logDebug MidDetail $ "nbe-exit" <+> prettyVerbose result
  logDebug MaxDetail $ "nbe-exit" <+> prettyFriendly (WithContext result ctx)
  return ()
-}
{-
showApp ::
  (MonadNorm builtin m) =>
  FunctionExpr builtin ->
  [UnforcedArg builtin] ->
  m ()
showApp _ _ = return ()
showAppExit :: (MonadLogger m) => m typedExpr -> m typedExpr
showAppExit = id

-}

visibilityError ::
  (HasCallStack, MonadNorm builtin m) =>
  Thunk builtin ->
  UnforcedArg builtin ->
  m b
visibilityError fun arg = do
  funDoc <- prettyFriendlyInCtx fun
  argsDoc <- prettyFriendlyInCtx (argExpr arg)
  let visDoc = pretty (visibilityOf arg)
  developerError $
    unexpectedExpr currentPass (visDoc <+> "arg" <+> squotes argsDoc) <+> "Does not match function's visibility:" <> line <> indent 2 funDoc
