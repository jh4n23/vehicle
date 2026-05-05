module Vehicle.Compile.LiftIf
  ( unfoldIf,
  )
where

import Vehicle.Compile.Normalise.NBE (MonadNorm)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Builtin.Standard.Normalise
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Name

unfoldIf ::
  (MonadNorm Builtin m) =>
  IfArgs (Thunk Builtin) ->
  m (Thunk Builtin)
unfoldIf (IfArgs _ c x y) = do
  let dims = mkDims []
  let cAndX = Forced $ mkExpr accessAndTensor (TensorOp2Args dims c x)
  let notC = Forced $ mkExpr accessNotTensor (TensorOp1Args dims c)
  let notCAndY = Forced $ mkExpr accessAndTensor (TensorOp2Args dims notC y)
  let result = Forced $ mkExpr accessOrTensor (TensorOp2Args dims cAndX notCAndY)
  logDebugM MaxDetail $ do
    nameCtx <- getNameContext
    return $ "unfold-if" <+> prettyFriendly (WithContext result nameCtx)
  return result
