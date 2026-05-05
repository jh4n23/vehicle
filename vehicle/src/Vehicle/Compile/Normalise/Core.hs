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
  | Blocked (BlockingArgs Value builtin)
  | EvaluationResult (Thunk builtin)

data BuiltinEvaluationResult expr arg builtin
  = Evaluated (expr builtin)
  | Unevaluated (BlockingArgs arg builtin)

type StandardBuiltinEvaluationScheme args builtin m =
  (IsArgs args) =>
  args (Thunk builtin) ->
  m (BuiltinEvaluationResult Thunk Value builtin)

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
  forceBuiltin :: builtin -> Spine builtin -> m expr
  forceMeta :: MetaID -> (Spine builtin) -> m expr

  handleUniverse :: Proxy builtin -> Maybe (UniverseLevel -> m expr)
  handleBoundVar :: Lv -> (Spine builtin) -> m expr
  handlePi :: Maybe (GenericBinder (Thunk builtin) -> Closure builtin -> m expr)
  handleLam :: Maybe (GenericBinder (Thunk builtin) -> Closure builtin -> m expr)
  handleRecord :: Maybe (Expr builtin -> RecordFields builtin -> m expr)
  handleFreeVar :: Identifier -> (Spine builtin) -> m expr
  handleRecordAcc :: Type builtin -> RecordExpr builtin -> FieldName -> (Spine builtin) -> m expr

-------------------------------------------------------------------------------
-- Functions

data FunctionExpr builtin
  = VFunctionLam (GenericBinder (Thunk builtin)) (Closure builtin)
  | VFunctionBuiltin builtin (Spine builtin)
  | VFunctionFreeVar Identifier (Spine builtin)
  | VFunctionMeta MetaID (Spine builtin)
  | VFunctionBoundVar Lv (Spine builtin)
  | VFunctionRecordAcc (Type builtin) (RecordExpr builtin) FieldName (Spine builtin)

instance (Monad m) => TypedEvalScheme (FunctionExpr builtin) builtin m where
  forceBuiltin b args = return $ VFunctionBuiltin b args
  forceMeta m args = return $ VFunctionMeta m args
  handleUniverse _ = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleLam = Just $ \binder closure -> return $ VFunctionLam binder closure
  handleBoundVar lv args = return $ VFunctionBoundVar lv args
  handleFreeVar ident args = return $ VFunctionFreeVar ident args
  handleRecordAcc typ record field args = return $ VFunctionRecordAcc typ record field args

-------------------------------------------------------------------------------
-- Records

data RecordExpr builtin
  = VRecordRecord (Type builtin) !(RecordFields builtin)
  | VRecordFreeVar Identifier (Spine builtin)
  | VRecordMeta MetaID (Spine builtin)
  | VRecordBuiltin builtin (Spine builtin)
  | VRecordBoundVar Lv (Spine builtin)
  | VRecordRecordAcc (Type builtin) (RecordExpr builtin) FieldName (Spine builtin)

instance (Monad m) => TypedEvalScheme (RecordExpr builtin) builtin m where
  forceBuiltin b args = return $ VRecordBuiltin b args
  forceMeta m args = return $ VRecordMeta m args
  handleBoundVar lv args = return $ VRecordBoundVar lv args
  handleFreeVar ident args = return $ VRecordFreeVar ident args
  handleRecord = Just $ \record fields -> return $ VRecordRecord record fields
  handleRecordAcc typ record field args = return $ VRecordRecordAcc typ record field args
  handlePi = Nothing
  handleUniverse _ = Nothing
  handleLam = Nothing
