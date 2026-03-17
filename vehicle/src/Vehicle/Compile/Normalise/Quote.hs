module Vehicle.Compile.Normalise.Quote where

import Data.Map.Ordered qualified as OMap
import Vehicle.Data.AST.Expr.Scoped (Expr (..), Substitution, normAppList, substituteDB)
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Name.Class (MonadReadableNameContext, getBinderDepth)
import Vehicle.Data.Variable.Bound.Level (Lv, dbLevelToIndex)
import Vehicle.Prelude

-- | Converts from a normalised representation to an unnormalised representation.
-- Do not call except for logging and debug purposes, very expensive with nested
-- lambdas.
unnormalise :: forall a b. (Quote a b) => Lv -> a -> b
unnormalise = quote mempty

unnormaliseInCtx ::
  forall expr m.
  (MonadReadableNameContext m, Show expr) =>
  Value expr ->
  m (Expr expr)
unnormaliseInCtx e = do
  lv <- getBinderDepth
  return $ unnormalise lv e

-----------------------------------------------------------------------------
-- Quoting closures

quoteCtx :: Provenance -> Lv -> BoundEnv builtin -> Substitution (Expr builtin)
quoteCtx p level env i = Right (quote p level (lookupIxInEnv env i))

-----------------------------------------------------------------------------
-- Quoting expressions

class Quote a b where
  quote :: Provenance -> Lv -> a -> b

instance Quote (GenericBinder expr, Closure builtin) (Expr builtin) where
  quote p lv (binder, Closure env body) = do
    -- Here we deliberately avoid using the standard `quote . eval` approach below
    -- on the body of the lambda, in order to avoid the dependency cycles that
    -- prevent us from printing during NBE.
    --
    -- normBody <- runReaderT (eval (liftEnvOverBinder p env) body) mempty
    -- quotedBody <- quote (level + 1) normBody
    let newEnv = extendEnvWithBound lv binder env
    quote p (lv + 1) (Thunk newEnv body)

instance Quote (Thunk builtin) (Expr builtin) where
  quote p lv (Thunk env body) = do
    let subst = quoteCtx p lv env
    substituteDB 0 subst body

instance Quote (Value builtin) (Expr builtin) where
  quote p lv = \case
    Forced value -> quote p lv value
    Unforced env -> quote p lv env
    UnforcedApp fn args -> do
      let fn' = quote p lv fn
      let xs' = fmap (quote p lv) args
      normAppList fn' xs'

instance Quote (ForcedValue builtin) (Expr builtin) where
  quote p level = \case
    VUniverse u -> Universe p u
    VMeta m spine -> quoteApp level p (Meta p m) spine
    VFreeVar v spine -> quoteApp level p (FreeVar p v) spine
    VBoundVar v spine -> do
      let var = BoundVar p (dbLevelToIndex level v)
      quoteApp level p var spine
    VBuiltin b spine -> do
      quoteApp level p (Builtin p b) spine
    VPi binder closure -> do
      let quotedBinder = quote p level binder
      let quotedBody = quote p level (binder, closure)
      Pi p quotedBinder quotedBody
    VLam binder closure -> do
      let quotedBinder = quote p level binder
      let quotedBody = quote p level (binder, closure)
      Lam mempty quotedBinder quotedBody
    VRecord recordType fields -> do
      let quotedRecordType = quote p level recordType
      let quotedFields = mapRecordFields (quote p level) $ OMap.assocs fields
      Record p quotedRecordType quotedFields
    VRecordAcc recordType record field spine -> do
      let quotedRecordType = quote p level recordType
      let quotedRecord = quote p level record
      let quotedProj = RecordProj p quotedRecordType quotedRecord field
      quoteApp level p quotedProj spine

instance (Quote expr1 expr2) => Quote (GenericBinder expr1) (GenericBinder expr2) where
  quote p level = fmap (quote p level)

instance (Quote expr1 expr2) => Quote (GenericArg expr1) (GenericArg expr2) where
  quote p level = fmap (quote p level)

quoteApp :: (Quote a (Expr builtin)) => Lv -> Provenance -> Expr builtin -> [GenericArg a] -> Expr builtin
quoteApp l p fn spine = normAppList fn $ fmap (quote p l) spine
