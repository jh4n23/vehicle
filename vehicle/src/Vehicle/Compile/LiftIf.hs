module Vehicle.Compile.LiftIf
  ( unfoldIf,
    unfoldIfThunk,
  )
where

import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context (MonadFreeContext)

--------------------------------------------------------------------------------
-- If lifting

unfoldIf ::
  (Monad m, MonadReadableNameContext m, MonadFreeContext Builtin m) =>
  IfArgs (Value Builtin) ->
  m (Value Builtin)
unfoldIf (IfArgs _ c x y) = do
  let dims = mkDims []
  cAndX <- evalAnd (TensorOp2Args dims c x)
  notC <- evalNot (TensorOp1Args dims c)
  notCAndY <- evalAnd (TensorOp2Args dims notC y)
  result <- evalOr (TensorOp2Args dims cAndX notCAndY)
  logDebugM MaxDetail $ do
    nameCtx <- getNameContext
    return $ "unfold-if" <+> prettyFriendly (WithContext result nameCtx)
  return result

unfoldIfThunk ::
  (Monad m, MonadReadableNameContext m, MonadFreeContext Builtin m) =>
  IfArgs (Thunk Builtin) ->
  m (Thunk Builtin)
unfoldIfThunk (IfArgs _ c x y) = do
  let dims = Forced $ mkDims []
  let cAndX = Forced $ mkExpr accessAndTensor (TensorOp2Args dims c x)
  let notC = Forced $ mkExpr accessNotTensor (TensorOp1Args dims c)
  let notCAndY = Forced $ mkExpr accessAndTensor (TensorOp2Args dims notC y)
  let result = Forced $ mkExpr accessOrTensor (TensorOp2Args dims cAndX notCAndY)
  logDebugM MaxDetail $ do
    nameCtx <- getNameContext
    return $ "unfold-if" <+> prettyFriendly (WithContext result nameCtx)
  return result
