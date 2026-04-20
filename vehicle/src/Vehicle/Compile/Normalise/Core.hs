module Vehicle.Compile.Normalise.Core where

import Data.Proxy (Proxy)
import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Interface.Print (PrintableBuiltin)
import Vehicle.Data.Code.Interface.Args
import Vehicle.Data.Code.Value
import Vehicle.Data.Universe
import Vehicle.Data.Variable.Bound.Context.Name.Class
import Vehicle.Data.Variable.Free.Context.Class

type MonadNormCore builtin m =
  ( MonadLogger m,
    NormalisableBuiltin builtin,
    PrintableBuiltin builtin
  )

type MonadNorm builtin m =
  ( MonadNormCore builtin m,
    MonadFreeContext builtin m,
    MonadReadableNameContext m
  )

type BlockingArgs arg builtin = [arg builtin]

data DetailedBuiltinEvaluationResult builtin
  = InsufficientArgs
  | DoesNotReduce
  | Blocked (BlockingArgs ForcedValue builtin)
  | EvaluationResult (Value builtin)

data BuiltinEvaluationResult expr arg builtin
  = Evaluated (expr builtin)
  | Unevaluated (BlockingArgs arg builtin)

type StandardBuiltinEvaluationScheme args builtin m =
  (IsArgs args) =>
  args (Value builtin) ->
  m (BuiltinEvaluationResult Value ForcedValue builtin)

data BuiltinEvaluationScheme builtin
  = forall args. (IsArgs args) => StandardEvaluation (forall m. (MonadNorm builtin m) => StandardBuiltinEvaluationScheme args builtin m)
  | DerivedEvaluation Identifier
  | -- The builtin is a type-class operation (should eventually be eliminated)
    TypeClassEvaluation
  | Unevaluable

type CastExprEvaluationScheme builtin m = Provenance -> [Arg builtin] -> m (Expr builtin)

-- | A type-class for builtins that can be normalised compositionally.
class (PrintableBuiltin builtin) => NormalisableBuiltin builtin where
  evaluationScheme :: builtin -> BuiltinEvaluationScheme builtin
  isCast :: builtin -> Bool
  isDerivedBuiltin :: builtin -> Maybe Identifier

class TypedEvalScheme expr builtin where
  handleUniverse :: Maybe (Proxy builtin -> UniverseLevel -> expr)
  handlePi :: Maybe (Binder builtin -> Expr builtin -> expr)
  handleLam :: Maybe (Binder builtin -> Expr builtin -> expr)
  handleRecord :: Maybe (Expr builtin -> RecordFields builtin -> expr)
  handleBoundVar :: Lv -> Args builtin -> expr
  handleFreeVar :: Identifier -> Args builtin -> expr
  handleBuiltin :: builtin -> Args builtin -> expr
  handleMeta :: MetaID -> Args builtin -> expr
  handleRecordAcc :: Type builtin -> RecordExpr builtin -> FieldName -> Args builtin -> expr

-------------------------------------------------------------------------------
-- Functions

data FunctionExpr builtin
  = VFunctionLam (Binder builtin) (Expr builtin)
  | VFunctionBuiltin builtin (Args builtin)
  | VFunctionFreeVar Identifier (Args builtin)
  | VFunctionMeta MetaID (Args builtin)
  | VFunctionBoundVar Lv (Args builtin)
  | VFunctionRecordAcc (Type builtin) (RecordExpr builtin) FieldName (Args builtin)

instance TypedEvalScheme (FunctionExpr builtin) builtin where
  handleUniverse = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleLam = Just VFunctionLam
  handleBoundVar = VFunctionBoundVar
  handleFreeVar = VFunctionFreeVar
  handleBuiltin = VFunctionBuiltin
  handleMeta = VFunctionMeta
  handleRecordAcc = VFunctionRecordAcc

-------------------------------------------------------------------------------
-- Records

data RecordExpr builtin
  = VRecordRecord (Type builtin) !(RecordFields builtin)
  | VRecordFreeVar Identifier (Args builtin)
  | VRecordMeta MetaID (Args builtin)
  | VRecordBuiltin builtin (Args builtin)
  | VRecordBoundVar Lv (Args builtin)
  | VRecordRecordAcc (Type builtin) (RecordExpr builtin) FieldName (Args builtin)

instance TypedEvalScheme (RecordExpr builtin) builtin where
  handleBoundVar = VRecordBoundVar
  handleFreeVar = VRecordFreeVar
  handleBuiltin = VRecordBuiltin
  handleMeta = VRecordMeta
  handleRecord = Just VRecordRecord
  handleRecordAcc = VRecordRecordAcc
  handlePi = Nothing
  handleUniverse = Nothing
  handleLam = Nothing
