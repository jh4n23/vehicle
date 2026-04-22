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

class (Monad m) => TypedEvalScheme expr builtin m where
  forceBuiltin :: builtin -> Args builtin -> m expr
  forceMeta :: MetaID -> Args builtin -> m expr

  handleUniverse :: Proxy builtin -> Maybe (UniverseLevel -> m expr)
  handleBoundVar :: Lv -> Args builtin -> m expr
  handlePi :: Maybe (Binder builtin -> Closure builtin -> m expr)
  handleLam :: Maybe (Binder builtin -> Closure builtin -> m expr)
  handleRecord :: Maybe (Expr builtin -> RecordFields builtin -> m expr)
  handleFreeVar :: Identifier -> Args builtin -> m expr
  handleRecordAcc :: Type builtin -> RecordExpr builtin -> FieldName -> Args builtin -> m expr

-------------------------------------------------------------------------------
-- Functions

data FunctionExpr builtin
  = VFunctionLam (Binder builtin) (Closure builtin)
  | VFunctionBuiltin builtin (Args builtin)
  | VFunctionFreeVar Identifier (Args builtin)
  | VFunctionMeta MetaID (Args builtin)
  | VFunctionBoundVar Lv (Args builtin)
  | VFunctionRecordAcc (Type builtin) (RecordExpr builtin) FieldName (Args builtin)

instance TypedEvalScheme (FunctionExpr builtin) builtin m where
  forceBuiltin b args = return $ VFunctionBuiltin b args
  forceMeta m args = return $ VFunctionMeta m args
  handleUniverse _ = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleLam = Just VFunctionLam
  handleBoundVar = VFunctionBoundVar
  handleFreeVar = VFunctionFreeVar
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

instance TypedEvalScheme (RecordExpr builtin) builtin m where
  forceBuiltin b args = return $ VRecordBuiltin b args
  forceMeta m args = return $ VRecordMeta m args
  handleBoundVar = VRecordBoundVar
  handleFreeVar = VRecordFreeVar
  handleRecord = Just VRecordRecord
  handleRecordAcc = VRecordRecordAcc
  handlePi = Nothing
  handleUniverse _ = Nothing
  handleLam = Nothing
