module Vehicle.Data.Code.Value
  ( BoundEnv (..),
    EnvEntry,
    lookupIxInEnv,
    boundContextToEnv,
    namedBoundContextToEnv,
    extendEnvWithDefined,
    extendEnvWithBound,
    boundEnvToCtx,
    emptyBoundEnv,
    Thunk (..),
    thunkifyExpr,
    thunkifyArg,
    thunkifyBinder,
    thunkifyArgs,
    Closure (..),
    extendClosure,
    Value (..),
    ForcedValue (..),
    VType,
    VArg,
    VBinder,
    VTelescope,
    VRecordFields,
    VDims,
    Spine,
    GluedExpr (..),
    GluedType,
    DimensionedTensorValue (..),
  )
where

import Control.Monad (void)
import Data.Bifunctor (Bifunctor (..))
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import GHC.Generics
import Vehicle.Data.AST.Expr.Scoped (Arg, Binder, Expr)
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Code.Interface
import Vehicle.Data.Universe (UniverseLevel)
import Vehicle.Data.Variable.Bound.Context.Core
import Vehicle.Data.Variable.Bound.Context.Generic.Core
import Vehicle.Data.Variable.Bound.Context.Name.Core
import Vehicle.Data.Variable.Bound.Index (Ix)
import Vehicle.Data.Variable.Bound.Level
import Vehicle.Prelude

----------------------------------------------------------------------------
-- Bound environments

-- | The information stored for each variable in the environment. We choose
-- to store the binder as it's a convenient mechanism for passing through
-- name, relevance for pretty printing and debugging.
type EnvEntry builtin = Value builtin

unbound :: Lv -> EnvEntry builtin
unbound lv = Forced $ VBoundVar lv []

newtype BoundEnv builtin = BoundEnv
  { unBoundEnv :: GenericBoundCtx (GenericBinder (), EnvEntry builtin)
  }
  deriving (Show, Eq, Ord)

emptyBoundEnv :: BoundEnv builtin
emptyBoundEnv = BoundEnv mempty

lookupIxInEnv :: BoundEnv builtin -> Ix -> Value builtin
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
  Value builtin ->
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

-----------------------------------------------------------------------------
-- Thunks

-- | Unevaluated expressions paired with the environment that it should
-- be evaluated in.
data Thunk builtin = Thunk (BoundEnv builtin) (Expr builtin)
  deriving (Show, Generic, Eq, Ord)

instance HasProvenance (Thunk builtin) where
  provenanceOf (Thunk _env expr) = provenanceOf expr

thunkifyExpr :: BoundEnv builtin -> Expr builtin -> Value builtin
thunkifyExpr env = Unforced . Thunk env

thunkifyBinder :: BoundEnv builtin -> Binder builtin -> VBinder builtin
thunkifyBinder env = fmap (Thunk env)

thunkifyArg :: BoundEnv builtin -> Arg builtin -> VArg builtin
thunkifyArg env = fmap (thunkifyExpr env)

thunkifyArgs :: BoundEnv builtin -> NonEmpty (Arg builtin) -> [VArg builtin]
thunkifyArgs env = fmap (thunkifyArg env) . NonEmpty.toList

-----------------------------------------------------------------------------
-- Closures

-- | A special type of `Thunk` that is used for binders. The environment
-- needs to be first extended with a value for the bound variable before
-- it can be normalised.
data Closure builtin = Closure (BoundEnv builtin) (Expr builtin)
  deriving (Show, Generic, Eq, Ord)

extendClosure :: Closure builtin -> VBinder builtin -> Value builtin -> Value builtin
extendClosure (Closure env expr) binder value =
  Unforced $ Thunk (extendEnvWithDefined value binder env) expr

-----------------------------------------------------------------------------
-- Normalised expressions

data Value builtin
  = Forced (ForcedValue builtin)
  | Unforced (Thunk builtin)
  | UnforcedApp (Value builtin) (Spine builtin)
  deriving (Show, Generic, Eq, Ord)

-- | A normalised expression. Internal invariant is that it should always be
-- well-typed.
data ForcedValue builtin
  = VUniverse !UniverseLevel
  | VMeta !MetaID !(Spine builtin)
  | VFreeVar !Identifier !(Spine builtin)
  | VBoundVar !Lv !(Spine builtin)
  | VBuiltin !builtin !(Spine builtin)
  | VLam !(VBinder builtin) !(Closure builtin)
  | VPi !(VBinder builtin) !(Closure builtin)
  | VRecord (VType builtin) !(VRecordFields builtin)
  | VRecordAcc !(VType builtin) !(Value builtin) !FieldName !(Spine builtin)
  deriving (Show, Generic, Eq, Ord)

type VType builtin = Value builtin

type VArg builtin = GenericArg (Value builtin)

type VBinder builtin = GenericBinder (Thunk builtin)

type VTelescope builtin = GenericTelescope (Value builtin)

type VRecordFields builtin = SearchableRecordFields (Value builtin)

type VDims builtin = Value builtin

-- | A list of arguments for an application that cannot be normalised.
type Spine builtin = [VArg builtin]

-----------------------------------------------------------------------------
-- Glued expressions

-- | A pair of an unnormalised and normalised expression.
data GluedExpr builtin = Glued
  { unnormalised :: Expr builtin,
    normalised :: Value builtin
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
  { tensorValueDims :: VDims builtin,
    tensorValue :: Value builtin
  }
  deriving (Show, Eq, Ord)

-----------------------------------------------------------------------------
-- Instances

instance (HasBuiltinConstructor ForcedValue Value) where
  accessBuiltinC =
    Access
      { getExpr = \case
          VBuiltin b spine -> Just (b, spine)
          _ -> Nothing,
        mkExpr = uncurry VBuiltin
      }
