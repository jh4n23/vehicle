module Vehicle.Compile.LiftIf
  ( unfoldIf,
  )
where

import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Code.Interface
import Vehicle.Data.Variable.Bound.Context.Name

--------------------------------------------------------------------------------
-- If lifting

unfoldIf ::
  (MonadLogger m, MonadReadableNameContext m) =>
  IfArgs (Thunk Builtin) ->
  m (Thunk Builtin)
unfoldIf (IfArgs _ c x y) = do
  let dims = Forced $ mkDims []
  let cAndX = Forced $ mkExpr accessAndTensor (TensorOp2Args dims c x)
  let notC = Forced $ mkExpr accessNotTensor (TensorOp1Args dims c)
  let notCAndY = Forced $ mkExpr accessAndTensor (TensorOp2Args dims notC y)
  let result = Forced $ mkExpr accessOrTensor (TensorOp2Args dims cAndX notCAndY)
  logDebugM MaxDetail $ do
    nameCtx <- getNameContext
    return $ "unfold-if" <+> prettyFriendly (WithContext result nameCtx)
  return result
