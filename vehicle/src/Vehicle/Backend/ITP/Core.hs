module Vehicle.Backend.ITP.Core where

import Vehicle.Compile.Prelude (developerError)
import Vehicle.Data.AST.Expr.Scoped
import Vehicle.Data.Builtin.Decidability (DecidabilityBuiltin)
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Code.Interface (IsArgs (..), tensorComparisonPointwiseDims, tensorComparisonReducedDims)
import Vehicle.Data.Code.Interface.Patterns

data ComparisonType
  = Reduced (Args DecidabilityBuiltin)
  | Pointwise (Args DecidabilityBuiltin)

comparisonType :: [Arg DecidabilityBuiltin] -> ComparisonType
comparisonType = \case
  (getExpr accessSpine -> Just args) ->
    case (tensorComparisonPointwiseDims args, tensorComparisonReducedDims args) of
      (ICons {}, INil {}) -> Pointwise
      (INil {}, _) -> Reduced
      _ -> developerError "mixed comparison"
  _ -> developerError "malformed comparison arguments"
