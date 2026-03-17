module Vehicle.Compile.LiftIf
  ( liftIf,
    liftIfValues,
    unfoldIf,
  )
where

import Vehicle.Compile.Normalise.NBE (MonadNorm, forceValue)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Builtin.Standard.Normalise
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Name

--------------------------------------------------------------------------------
-- If lifting

pattern IIf :: VArg Builtin -> VArg Builtin -> Value Builtin -> Value Builtin -> ForcedValue Builtin
pattern IIf t c x y <- VBuiltin (BuiltinFunction If) [t, c, argExpr -> x, argExpr -> y]
  where
    IIf t c x y = VBuiltin (BuiltinFunction If) [t, c, explicit x, explicit y]

liftIf ::
  (MonadNorm Builtin m) =>
  Value Builtin ->
  (Value Builtin -> m (Value Builtin)) ->
  m (Value Builtin)
liftIf e k = do
  forcedValue <- forceValue e
  case forcedValue of
    IIf t cond e1 e2 -> Forced <$> (IIf t cond <$> liftIf e1 k <*> liftIf e2 k)
    _ -> k e

liftIfValues ::
  (MonadNorm Builtin m) =>
  [Value Builtin] ->
  ([Value Builtin] -> m (Value Builtin)) ->
  m (Value Builtin)
liftIfValues [] k = k []
liftIfValues (x : xs) k = liftIf x (\a -> liftIfValues xs (\as -> k (a : as)))

unfoldIf ::
  (MonadNorm Builtin m) =>
  IfArgs (Value Builtin) ->
  m (Value Builtin)
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
