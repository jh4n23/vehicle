module Vehicle.Compile.Normalise.Core where

import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Interface.Print (PrintableBuiltin)
import Vehicle.Data.Code.Interface.Args
import Vehicle.Data.Code.Value
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
