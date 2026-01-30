module Vehicle.Compile.Type.Force where

-- import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Prelude
-- import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Universe

-----------------------------------------------------------------------------
-- Meta-variable forcing

type Env builtin = [ForcibleExpr builtin]

data Thunk builtin = Thunk (Env builtin) (Expr builtin)

data ForcibleExpr builtin
  = Forced (ForcedExpr builtin)
  | Unforced (Thunk builtin)

data ForcedExpr builtin
  = FUniverse Provenance !UniverseLevel
  | FMeta Provenance !MetaID !(ForcibleSpine builtin)
  | FFreeVar Provenance !Identifier !(ForcibleSpine builtin)
  | FBoundVar Provenance !Ix !(ForcibleSpine builtin)
  | FBuiltin Provenance !builtin !(ForcibleSpine builtin)
  | FLam Provenance !(ForcibleBinder builtin) !(Thunk builtin)
  | FPi Provenance !(ForcibleBinder builtin) !(Thunk builtin)
  | FRecord Provenance (Type builtin) !(SearchableRecordFields (Expr builtin))
  | FRecordAcc Provenance !(ForcibleExpr builtin) !(ForcibleExpr builtin) !FieldName !(ForcibleSpine builtin)

type ForcibleArg builtin = GenericArg (ForcibleExpr builtin)

type ForcibleBinder builtin = GenericBinder (ForcibleExpr builtin)

type ForcibleSpine builtin = [ForcibleArg builtin]
