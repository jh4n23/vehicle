module Vehicle.Compile.Descope
  ( descopeDecl,
    descopeExprNaively,
    descopeExprNamed,
    descopeValueNaively,
    descopeValueNamed,
    descopeForcedValueNaively,
    descopeForcedValueNamed,
  )
where

import Data.Map.Ordered qualified as OMap
import Data.Maybe (fromMaybe)
import Vehicle.Compile.Prelude
import Vehicle.Data.AST.Expr.Desugared qualified as S
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Name.Class
import Vehicle.Data.Variable.Bound.Context.Name.Core
import Vehicle.Data.Variable.Bound.Context.Name.Instance

--------------------------------------------------------------------------------
-- Interface

descopeDecl :: (PrintableBuiltin builtin) => Decl builtin -> S.Decl builtin
descopeDecl decl = do
  case decl of
    DefFunction p ident sort t e -> DefFunction p ident sort (descopeExprInEmptyCtx t) (descopeExprInEmptyCtx e)
    DefAbstract p ident sort t -> DefAbstract p ident sort (descopeExprInEmptyCtx t)
    DefRecord p ident sort t f -> do
      let (t', f') = descopeRecordTelescope t f
      DefRecord p ident sort t' f'

descopeRecordTelescope ::
  forall builtin.
  (PrintableBuiltin builtin) =>
  Telescope builtin ->
  RecordFields builtin ->
  (S.Telescope builtin, S.RecordFields builtin)
descopeRecordTelescope telescope fields =
  runFreshNameBoundContext (go telescope)
  where
    go :: (MonadNameContext m) => Telescope builtin -> m (S.Telescope builtin, S.RecordFields builtin)
    go = \case
      [] -> do
        fields' <- traverseRecordFields (genericDescopeExpr (ixToName Named)) fields
        return ([], fields')
      binder : binders -> do
        binder' <- traverse (genericDescopeExpr (ixToName Named)) binder
        (binders', fields') <- addNameToContext binder $ go binders
        return (binder' : binders', fields')

descopeExprInEmptyCtx :: (PrintableBuiltin builtin) => Expr builtin -> S.Expr builtin
descopeExprInEmptyCtx = descopeExprNamed mempty

descopeExprNamed :: (PrintableBuiltin builtin) => NamedBoundCtx -> Expr builtin -> S.Expr builtin
descopeExprNamed ctx e = runNameBoundContext ctx $ genericDescopeExpr (ixToName Named) e

descopeValueNamed :: (PrintableBuiltin builtin) => NamedBoundCtx -> Thunk builtin -> S.Expr builtin
descopeValueNamed ctx e = runNameBoundContext ctx $ descopeValue Named e

descopeForcedValueNamed :: (PrintableBuiltin builtin) => NamedBoundCtx -> Value builtin -> S.Expr builtin
descopeForcedValueNamed ctx e = runNameBoundContext ctx $ descopeForcedValue Named e

-- Naive descoping

descopeExprNaively :: (PrintableBuiltin builtin) => Expr builtin -> S.Expr builtin
descopeExprNaively e = runFreshNameBoundContext (genericDescopeExpr (ixToName Naive) e)

descopeValueNaively :: (PrintableBuiltin builtin) => Thunk builtin -> S.Expr builtin
descopeValueNaively e = runFreshNameBoundContext (descopeValue Naive e)

descopeForcedValueNaively :: (PrintableBuiltin builtin) => Value builtin -> S.Expr builtin
descopeForcedValueNaively e = runFreshNameBoundContext (descopeForcedValue Naive e)

--------------------------------------------------------------------------------
-- Variable conversion methods

type VarConversion var m = (MonadNameContext m) => Provenance -> var -> m Name

data VarStrategy = Named | Naive

ixToName :: VarStrategy -> VarConversion Ix m
ixToName s p ix = case s of
  Naive -> return $ layoutAsText $ pretty ix
  Named -> ixToProperName p ix

lvToName :: VarStrategy -> VarConversion Lv m
lvToName s p lv = case s of
  Naive -> return $ layoutAsText $ pretty lv
  Named -> lvToProperName p lv

--------------------------------------------------------------------------------
-- Expr

genericDescopeExpr :: (MonadNameContext m) => VarConversion Ix m -> Expr builtin -> m (S.Expr builtin)
genericDescopeExpr f e = showDescopeExit $ case showDescopeEntry e of
  Universe p _l -> return $ S.Universe p
  Hole p name -> return $ S.Hole p name
  Builtin p op -> return $ S.Builtin p op
  Meta p i -> return $ descopeMeta p i
  FreeVar p v -> return $ descopeFreeVar p v
  BoundVar p v -> S.Var p <$> f p v
  App fun args -> do
    fun' <- genericDescopeExpr f fun
    args' <- traverse (traverse (genericDescopeExpr f)) args
    return $ S.App fun' args'
  Let p bound binder body -> do
    bound' <- genericDescopeExpr f bound
    binder' <- traverse (genericDescopeExpr f) binder
    body' <- addNameToContext binder $ genericDescopeExpr f body
    return $ S.Let p bound' binder' body'
  Lam p binder body -> do
    binder' <- traverse (genericDescopeExpr f) binder
    body' <- addNameToContext binder $ genericDescopeExpr f body
    return $ S.Lam p binder' body'
  Pi p binder body -> do
    binder' <- traverse (genericDescopeExpr f) binder
    body' <- addNameToContext binder $ genericDescopeExpr f body
    return $ S.Pi p binder' body'
  Record p _recordType fields -> do
    fields' <- traverseRecordFields (genericDescopeExpr f) fields
    return $ S.Record p fields'
  RecordProj p _recordType record field -> do
    record' <- genericDescopeExpr f record
    return $ S.RecordAcc p record' field

--------------------------------------------------------------------------------
-- Thunk

descopeClosure ::
  forall m binder builtin.
  (PrintableBuiltin builtin, MonadNameContext m) =>
  VarStrategy ->
  GenericBinder binder ->
  Closure builtin ->
  m (S.Expr builtin)
descopeClosure f _binder (Closure env body) = do
  body' <- genericDescopeExpr (ixToName f) body
  env' <- traverse (descopeValue f) (cheatEnvToValues env) :: m [S.Expr builtin]
  let envExpr = S.normAppList (S.Var mempty "ENV") $ fmap (Arg Explicit Relevant) env'
  return $ S.App envExpr [explicit body']

descopeThunk ::
  forall m builtin.
  (PrintableBuiltin builtin, MonadNameContext m) =>
  VarStrategy ->
  UnevaluatedThunk builtin ->
  m (S.Expr builtin)
descopeThunk f (UnevaluatedThunk env body) = do
  body' <- genericDescopeExpr (ixToName f) body
  env' <- traverse (descopeValue f) (cheatEnvToValues env) :: m [S.Expr builtin]
  let envExpr = S.normAppList (S.Var mempty "ENV") $ fmap (Arg Explicit Relevant) env'
  return $ S.App envExpr [explicit body']

descopeValue ::
  (MonadNameContext m, PrintableBuiltin builtin) =>
  VarStrategy ->
  Thunk builtin ->
  m (S.Expr builtin)
descopeValue f = \case
  Forced value -> descopeForcedValue f value
  Unforced thunk -> descopeThunk f thunk

-- | This function is not meant to do anything sensible and is merely
-- used for printing `WHNF`s in a readable form.
descopeForcedValue ::
  (MonadNameContext m, PrintableBuiltin builtin) =>
  VarStrategy ->
  Value builtin ->
  m (S.Expr builtin)
descopeForcedValue f e = case e of
  VUniverse {} ->
    return $ S.Universe p
  VMeta m spine ->
    S.normAppList (descopeMeta p m) <$> descopeSpine f spine
  VFreeVar v spine ->
    S.normAppList (descopeFreeVar p v) <$> descopeSpine f spine
  VBuiltin b spine ->
    S.normAppList (S.Builtin p b) <$> descopeSpine f spine
  VBoundVar v spine -> do
    var <- S.Var p <$> lvToName f p v
    args <- descopeSpine f spine
    return $ S.normAppList var args
  VPi binder closure -> do
    binder' <- traverse (descopeThunk f) binder
    body' <- addNameToContext binder $ descopeClosure f binder closure
    return $ S.Pi p binder' body'
  VLam binder closure -> do
    binder' <- traverse (descopeThunk f) binder
    body' <- addNameToContext binder $ descopeClosure f binder closure
    return $ S.Lam p binder' body'
  VRecord _recordType fields -> do
    fields' <- traverseRecordFields (descopeValue f) $ OMap.assocs fields
    return $ S.Record p fields'
  VRecordAcc _recordType record field spine -> do
    record' <- descopeValue f record
    let recordAcc = S.RecordAcc p record' field
    args <- descopeSpine f spine
    return $ S.normAppList recordAcc args
  where
    p = mempty

-- | Converts an environment to set of values suitable for printing
cheatEnvToValues :: BoundEnv builtin -> GenericBoundCtx (Thunk builtin)
cheatEnvToValues (BoundEnv env) = fmap entryToValue env
  where
    entryToValue :: (GenericBinder (), EnvEntry builtin) -> Thunk builtin
    entryToValue (binder, entry) = do
      let ident = stdlibIdentifier (fromMaybe "_" (nameOf binder) <> " =")
      let arg = explicit $ case entry of
            Bound value -> Unforced value
            Unbound lv -> Forced $ VBoundVar lv []
      Forced $ VFreeVar ident [arg]

descopeSpine :: (MonadNameContext m, PrintableBuiltin builtin) => VarStrategy -> Spine builtin -> m [S.Arg builtin]
descopeSpine f = traverseArgs (descopeValue f)

descopeMeta :: Provenance -> MetaID -> S.Expr builtin
descopeMeta p m = S.Hole p (layoutAsText $ pretty m)

descopeFreeVar :: Provenance -> Identifier -> S.Expr builtin
descopeFreeVar p ident = S.Var p (nameOf ident)

--------------------------------------------------------------------------------
-- Logging and errors

showDescopeEntry :: Expr builtin -> Expr builtin
showDescopeEntry e = e

showDescopeExit :: (Monad m) => m (S.Expr builtin) -> m (S.Expr builtin)
showDescopeExit m = m

{-
showDescopeEntry :: Expr Builtin -> Expr Builtin
showDescopeEntry e = trace ("enter: " <> show e) e

showDescopeExit :: (Monad m) => m S.Expr -> m S.Expr
showDescopeExit m = do
  e <- m
  return $ trace ("exit: " <> show e) e
-}
