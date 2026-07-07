module Vehicle.Data.Code.ForcedValue
  ( ForcedValue (..),
    Closure (..),
    extendClosure,
    extendClosureWithBound,
    Thunk (..),
    ForcedType,
    UnforcedType,
    UnforcedArg,
    UnforcedBinder,
    UnforcedTelescope,
    UnforcedRecordFields,
    UnforcedDims,
    UnforcedSpine,
    getNMeta,
    BoundEnv (..),
    lookupIxInEnv,
    extendEnvWithBound,
    extendEnvWithDefined,
    boundContextToEnv,
    namedBoundContextToEnv,
    cheatEnvToValues,
    boundEnvToCtx,
    traverseEnv,
    traverseEnv_,
    emptyBoundEnv,
    GluedExpr (..),
    GluedType,
    DimensionedTensorValue (..),
  )
where

import Control.Monad (void)
import Data.Bifunctor (Bifunctor (..))
import Data.Foldable (traverse_)
import Data.Map.Ordered (OMap)
import Data.Maybe (fromMaybe)
import GHC.Generics
import Vehicle.Data.AST.Expr.Scoped (Expr (..))
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Code.Interface
import Vehicle.Data.Universe (UniverseLevel)
import Vehicle.Data.Variable.Bound.Context.Core
import Vehicle.Data.Variable.Bound.Context.Generic.Core
import Vehicle.Data.Variable.Bound.Context.Name.Core
import Vehicle.Data.Variable.Bound.Index (Ix)
import Vehicle.Data.Variable.Bound.Level
import Vehicle.Prelude

-----------------------------------------------------------------------------
-- Thunks

-- | A thunk represents an expression that may not yet have been evaluated.
data Thunk builtin
  = Forced (ForcedValue builtin)
  | Unforced (BoundEnv builtin) (Expr builtin)
  deriving (Show, Generic, Eq, Ord)

-- | Closures for weak-head normal-form.
data Closure builtin = Closure (BoundEnv builtin) (Expr builtin)
  deriving (Show, Generic, Eq, Ord)

extendClosure :: Closure builtin -> UnforcedBinder builtin -> Thunk builtin -> Thunk builtin
extendClosure (Closure env expr) binder value = Unforced (extendEnvWithDefined value binder env) expr

extendClosureWithBound :: Closure builtin -> UnforcedBinder builtin -> Lv -> Thunk builtin
extendClosureWithBound (Closure env expr) binder lv = Unforced (extendEnvWithBound lv binder env) expr

-----------------------------------------------------------------------------
-- Normalised expressions

-- | A normalised expression. Internal invariant is that it should always be
-- well-typed.
data ForcedValue builtin
  = VUniverse !UniverseLevel
  | VMeta !MetaID !(UnforcedSpine builtin)
  | VFreeVar !Identifier !(UnforcedSpine builtin)
  | VBoundVar !Lv !(UnforcedSpine builtin)
  | VBuiltin !builtin !(UnforcedSpine builtin)
  | VLam !(UnforcedBinder builtin) !(Closure builtin)
  | VPi !(UnforcedBinder builtin) !(Closure builtin)
  | VRecord (Thunk builtin) !(UnforcedRecordFields builtin)
  | VRecordAcc !(Thunk builtin) !(Thunk builtin) !FieldName !(UnforcedSpine builtin)
  deriving (Show, Generic, Eq, Ord)

type ForcedType builtin = ForcedValue builtin

type UnforcedType builtin = Thunk builtin

type UnforcedArg builtin = GenericArg (Thunk builtin)

-- | A list of arguments for an application that cannot be normalised.
type UnforcedSpine builtin = [UnforcedArg builtin]

type UnforcedBinder builtin = GenericBinder (Thunk builtin)

type UnforcedTelescope builtin = GenericTelescope (Thunk builtin)

type UnforcedRecordFields builtin = OMap FieldName (Thunk builtin)

type UnforcedDims builtin = Thunk builtin

----------------------------------------------------------------------------
-- Bound environments

-- | The information stored for each variable in the environment. We choose
-- to store the binder as it's a convenient mechanism for passing through
-- name, relevance for pretty printing and debugging.
type EnvEntry builtin = Thunk builtin

unbound :: Lv -> EnvEntry builtin
unbound lv = Forced $ VBoundVar lv []

newtype BoundEnv builtin = BoundEnv
  { unBoundEnv :: GenericBoundCtx (GenericBinder (), EnvEntry builtin)
  }
  deriving (Show, Eq, Ord)

emptyBoundEnv :: BoundEnv builtin
emptyBoundEnv = BoundEnv mempty

lookupIxInEnv :: BoundEnv builtin -> Ix -> Thunk builtin
lookupIxInEnv (BoundEnv env) i = snd $ lookupIxInBoundCtx i env

-- | Note that the `ctxSize` must come from the current context and not a
-- bound environment as the environment that the term was originally normalised
-- in may not be the same size as the current context.
extendEnvWithBound ::
  Lv ->
  GenericBinder expr ->
  BoundEnv builtin ->
  BoundEnv builtin
extendEnvWithBound ctxSize binder (BoundEnv env) =
  BoundEnv $ (void binder, unbound ctxSize) : env

extendEnvWithDefined ::
  Thunk builtin ->
  GenericBinder expr ->
  BoundEnv builtin ->
  BoundEnv builtin
extendEnvWithDefined value binder (BoundEnv env) =
  BoundEnv $ (void binder, value) : env

boundContextToEnv :: BoundCtx expr -> BoundEnv builtin
boundContextToEnv ctx = BoundEnv $ do
  let numberedCtx = zip ctx (reverse [0 .. Lv (length ctx - 1)])
  fmap (bimap void unbound) numberedCtx

namedBoundContextToEnv :: NamedBoundCtx -> BoundEnv builtin
namedBoundContextToEnv ctx = BoundEnv $ do
  let numberedCtx = zip ctx (reverse [0 .. Lv (length ctx - 1)])
  fmap (bimap (\n -> mkExplicitBinder () (fmap (mempty,) n)) unbound) numberedCtx

boundEnvToCtx :: BoundEnv builtin -> NamedBoundCtx
boundEnvToCtx (BoundEnv env) = toNamedBoundCtx (fmap fst env)

-- | Converts an environment to set of values suitable for printing
cheatEnvToValues :: BoundEnv builtin -> GenericBoundCtx (ForcedValue builtin)
cheatEnvToValues (BoundEnv env) = fmap entryToValue env
  where
    entryToValue :: (GenericBinder (), EnvEntry builtin) -> ForcedValue builtin
    entryToValue (binder, value) = do
      let ident = stdlibIdentifier (fromMaybe "_" (nameOf binder) <> " =")
      let arg = explicit value
      VFreeVar ident [arg]

----------------------------------------------------------------------------
-- Free environments

traverseEnv_ :: (Monad m) => (Thunk builtin -> m ()) -> BoundEnv builtin -> m ()
traverseEnv_ f (BoundEnv env) = traverse_ (\(_, v) -> f v) env

traverseEnv :: (Monad m) => (Thunk builtin -> m (Thunk builtin)) -> BoundEnv builtin -> m (BoundEnv builtin)
traverseEnv f (BoundEnv env) = BoundEnv <$> traverse (\(u, v) -> (u,) <$> f v) env

-----------------------------------------------------------------------------
-- Patterns

getNMeta :: ForcedValue builtin -> Maybe MetaID
getNMeta (VMeta m _) = Just m
getNMeta _ = Nothing

-----------------------------------------------------------------------------
-- Glued expressions

-- | A pair of an unnormalised and normalised expression.
data GluedExpr builtin = Glued
  { unnormalised :: Expr builtin,
    normalised :: ForcedValue builtin
  }
  deriving (Show, Generic)

instance HasProvenance (GluedExpr builtin) where
  provenanceOf = provenanceOf . unnormalised

type GluedType builtin = GluedExpr builtin

-----------------------------------------------------------------------------
-- Dimensioned values

-- | Because there are no dependent types in Haskell, we cannot create
-- type-classes over tensor values with a given dimension. Hence we need
-- to wrap them in this ugly type-class that stores the dimensions internally.
data DimensionedTensorValue builtin = TensorValue
  { tensorValueDims :: UnforcedDims builtin,
    tensorValue :: Thunk builtin
  }
  deriving (Show, Eq, Ord)

-----------------------------------------------------------------------------
-- Instances

instance HasBuiltinConstructor ForcedValue Thunk where
  accessBuiltinC =
    Access
      { getExpr = \case
          VBuiltin b spine -> Just (b, spine)
          _ -> Nothing,
        mkExpr = uncurry VBuiltin
      }
  exprToThunk = Forced

instance HasLambdaConstructor ForcedValue Thunk Closure where
  accessForcedLamC =
    Access
      { getExpr = \case
          Forced (VLam binder closure) -> Just (binder, closure)
          Unforced env (Lam _p binder body) -> Just (fmap (Unforced env) binder, Closure env body)
          _ -> Nothing,
        mkExpr = \(binder, closure) -> Forced $ VLam binder closure
      }
  accessBoundVarC =
    Access
      { getExpr = \case
          VBoundVar lv spine -> Just (lv, spine)
          _ -> Nothing,
        mkExpr = uncurry VBoundVar
      }
