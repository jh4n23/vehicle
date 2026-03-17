module Vehicle.Data.Variable.Bound.Context.Tensor
  ( module Export,
    replaceTensorVariableWithStackedChildren,
  )
where

import Vehicle.Compile.TypedView
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Builtin.Standard.Normalise (mkDims)
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (HasShape (..))
import Vehicle.Data.Variable.Bound.Context.Name.Class as Export
import Vehicle.Data.Variable.Bound.Context.Name.Core as Export
import Vehicle.Data.Variable.Bound.Context.Name.Instance as Export
import Vehicle.Data.Variable.Bound.Context.Tensor.Class as Export
import Vehicle.Data.Variable.Bound.Context.Tensor.Core as Export
import Vehicle.Data.Variable.Bound.Context.Tensor.Instance as Export
import Vehicle.Data.Variable.Bound.Level
import Vehicle.Prelude (developerError)

-- | Given a variable `x`:
--   - if not a tensor variable errors
--   - if an element variable then returns `x`
--   - if not an element variable returns `[x!0, x!1, ..., x!n]
replaceTensorVariableWithStackedChildren ::
  (MonadReadableTensorBoundContext m) =>
  SliceVariable ->
  m (Value Builtin)
replaceTensorVariableWithStackedChildren var = do
  nestedVar <- lookupNestedSliceVariable var
  case (childVariablesOf nestedVar, shapeOf nestedVar) of
    (Nothing, []) -> return $ Forced $ VBoundVar (toLv var) []
    (Just childVars, d : ds) ->
      return $
        fromRatTensorValue $
          VRatStackTensor $
            StackTensorArgs
              { stackType = Forced IRatType,
                stackFirstDim = Forced $ INatLiteral d,
                stackRemainingDims = mkDims ds,
                stackElements = flip map childVars $ \v -> Forced $ VBoundVar (toLv v) []
              }
    _ -> developerError "mismatched children and shape"
