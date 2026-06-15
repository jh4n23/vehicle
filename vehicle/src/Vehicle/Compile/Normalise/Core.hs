module Vehicle.Compile.Normalise.Core where

import Vehicle.Data.AST.Expr.Scoped
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Code.Interface
import Vehicle.Data.Tensor
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context
import Vehicle.Prelude
import Vehicle.Prelude.Logging.Class

type BlockingArgs expr builtin = [expr builtin]

data BuiltinEvaluationResult expr thunk builtin
  = -- The builtin was evaluated and was reduced to a simpler form.
    Evaluated (thunk builtin)
  | -- The builtin could not be evaluated.
    Unevaluable (BlockingArgs expr builtin)

data EvalScheme builtin m
  = forall args.
    Eval
      ( ( IsArgs args,
          MonadLogger m,
          MonadNameContext m,
          NormalisableExpr ForcedValue Thunk builtin m,
          HasBuiltinConstructor ForcedValue Thunk,
          HasLambdaConstructor ForcedValue Thunk Closure
        ) =>
        args (Thunk builtin) ->
        m (BuiltinEvaluationResult ForcedValue Thunk builtin)
      )
  | Derived Identifier
  | TypeClassOp
  | None

class (Monad m, HasBuiltinConstructor expr thunk) => NormalisableExpr expr thunk builtin m | thunk -> expr where
  force :: thunk builtin -> m (expr builtin)
  forceApp :: thunk builtin -> [GenericArg (thunk builtin)] -> m (expr builtin)

instance (Monad m) => NormalisableExpr Expr Expr builtin m where
  force = return
  forceApp fun args = return $ normAppList fun args

type TensorOpEvalData expr thunk args builtin =
  ( Accessor (expr builtin) (args (thunk builtin)),
    expr builtin -- The element type
  )

class HasLiftableTensorOperations expr thunk builtin where
  liftableTensorOp1s :: [TensorOpEvalData expr thunk TensorOp1Args builtin]
  liftableTensorOp2s :: [TensorOpEvalData expr thunk TensorOp2Args builtin]

data TensorLiteralAccessor expr builtin
  = forall a. (Eq a) => Wrapper (Accessor (expr builtin) (Tensor a))

class HasTensorLiterals expr builtin where
  tensorLiterals :: [TensorLiteralAccessor expr builtin]

-- | A type-class for builtins that can be normalised compositionally.
class (PrintableBuiltin builtin) => NormalisableBuiltin builtin where
  evalScheme :: builtin -> EvalScheme builtin m

type MonadNorm builtin m =
  ( MonadLogger m,
    NormalisableBuiltin builtin,
    MonadFreeContext builtin m,
    MonadReadableNameContext m
  )
