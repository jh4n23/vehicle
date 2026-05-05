module Vehicle.Compile.TypedView
  ( VectorValue (..),
    toVectorValue,
    etaReduceTensor,
    mkIndexInto,
    accessQuantifierLambda,
  )
where

import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Data.AST.Expr.Scoped
import Vehicle.Data.Builtin.Interface (Accessor (..), BuiltinHasIndexLiterals, BuiltinHasListLiterals, BuiltinHasNatLiterals, BuiltinHasNatType, BuiltinHasTensors (accessAtTensorBuiltin))
import Vehicle.Data.Builtin.Interface.Normalise (HasTensorLiterals, unforcedBuiltinApp)
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Builtin.Standard.Normalise (mkDims)
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor
import Vehicle.Data.Variable.Bound.Level
import Vehicle.Prelude

-------------------------------------------------------------------------------
-- Vector

-- | A view on all possible expressions that can have type `Nat`.
data VectorValue
  = VVectorBoundVar Lv (Spine Builtin)
  | VVectorDataset Identifier
  | VVectorLiteral (VecLitArgs (Thunk Builtin))
  | VVectorIf (IfArgs (Thunk Builtin))
  | VVectorForeach (ForeachVectorArgs (Thunk Builtin))

toVectorValue :: Value Builtin -> VectorValue
toVectorValue value = case value of
  VBoundVar v spine -> VVectorBoundVar v spine
  VFreeVar ident [] -> VVectorDataset ident
  (getExpr accessVecLit -> Just args) -> VVectorLiteral args
  (getExpr accessIf -> Just args) -> VVectorIf args
  (getExpr accessForeachVector -> Just args) -> VVectorForeach args
  _ -> developerError $ "ill-typed Vector expression:" <+> prettyVerbose value

-------------------------------------------------------------------------------
-- Bool

{-
toCompilableBoolValue :: (HasCallStack, MonadNorm Builtin m) => BoundEnv Builtin -> Expr Builtin -> m CompilableBoolTensorValue
toCompilableBoolValue env expr = case expr of
  -- Compilable
  (getExpr accessBoolTensorLiteral -> Just (ZeroDimTensor v)) -> return $ VBoolLiteral v
  (getExpr accessAndTensor -> Just args) -> return $ VAnd args
  (getExpr accessOrTensor -> Just args) -> return $ VOr args
  (getExpr accessNotTensor -> Just args) -> return $ VNot args
  (getExpr accessCompareRatTensorPointwise -> Just args) -> fromComparison $ Left args
  (getExpr accessCompareRatTensorReduced -> Just args) -> fromComparison $ Right args
  (getExpr accessCompareNat -> Just args) -> return $ VCompareNat args
  (getExpr accessCompareIndex -> Just args) -> return $ VCompareIndex args
  (getExpr accessQuantifyRatTensor -> Just args) -> VQuantifyRatTensor args
  (getExpr accessReduceAnd -> Just args) -> VReduceAndTensor args
  (getExpr accessReduceOr -> Just args) -> VReduceOrTensor args
  (getExpr accessAtTensor -> Just args) -> VBoolAt args
  (getExpr accessIf -> Just args) -> VBoolIf args
  _ -> developerError $ "ill-typed Bool expression:" <+> prettyVerbose expr

fromComparison ::
  Either
    (ComparisonOp, TensorOp2Args (Thunk Builtin))
    (ComparisonOp, TensorReduceComparisonArgs (Thunk Builtin)) ->
  CompilableBoolValue
fromComparison = \case
  Left (op, args) -> VCompareRatTensor (op, args)
  Right (op, TensorReduceComparisonArgs d ds e1 e2) ->
    VCompareRatTensor (op, TensorOp2Args (Forced $ ICons (Forced INatType) d ds) e1 e2)

toComparison :: (ComparisonOp, TensorOp2Args (Thunk Builtin)) -> Value Builtin
toComparison (op, TensorOp2Args dims e1 e2) = case matchDims dims of
  Nothing -> mkExpr accessCompareRatTensorPointwise (op, TensorOp2Args dims e1 e2)
  Just (d, ds) -> mkExpr accessCompareRatTensorReduced (op, TensorReduceComparisonArgs d ds e1 e2)
  where
    -- This is a giant hack. Need to rethink the whole comparison setup eventually.
    matchDims :: Thunk Builtin -> Maybe (Thunk Builtin, Thunk Builtin)
    matchDims = \case
      Forced forcedDims -> case toDimensionsValue forcedDims of
        VDimsNil -> Nothing
        VDimsCons d ds -> Just (d, ds)
        _ -> dimsError
      Unforced (UnevaluatedThunk env unforcedDims) -> case unforcedDims of
        INil {} -> Nothing
        ICons _ d ds -> Just (Unforced $ UnevaluatedThunk env d, Unforced $ UnevaluatedThunk env ds)
        _ -> dimsError
      _ -> dimsError

    dimsError = developerError "unexpected comparison dimensions"
-}
-------------------------------------------------------------------------------
-- Dim

-- | Takes a `X` and [i_1, ... i_n] and returns `X ! i_1 ! i_n`
mkIndexInto ::
  forall builtin.
  (HasTensorExpr Value Thunk builtin) =>
  Thunk builtin ->
  Thunk builtin ->
  TensorShape ->
  TensorIndices ->
  Thunk builtin
mkIndexInto elementType value shape indices = go value (zip shape indices)
  where
    go :: Thunk builtin -> [(TensorDimension, TensorIndex)] -> Thunk builtin
    go tensor = \case
      [] -> tensor
      (d, i) : xs -> do
        let result =
              Forced $
                mkExpr accessAtTensor $
                  AtTensorArgs
                    { atType = elementType,
                      atFirstDim = Forced $ INatLiteral d,
                      atRemainingDims = mkDims $ fmap fst xs,
                      atTensor = tensor,
                      atIndex = Forced $ IIndexLiteral i (Forced $ INatLiteral d)
                    }
        go result xs

-------------------------------------------------------------------------------
-- Utilities

-- | Reduces a tensor value `x` to `[x!0, x!1, ..., x!n]`
etaReduceTensor ::
  (BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasTensors builtin, HasTensorLiterals builtin, BuiltinHasListLiterals builtin, BuiltinHasNatType builtin) =>
  VType builtin ->
  Int ->
  Thunk builtin ->
  Thunk builtin ->
  [Thunk builtin]
etaReduceTensor typ dim dims tensor = do
  let mkAtArgs i =
        AtTensorArgs
          { atType = typ,
            atFirstDim = Forced $ INatLiteral dim,
            atRemainingDims = dims,
            atTensor = tensor,
            atIndex = Forced $ IIndexLiteral i (Forced $ INatLiteral dim)
          }
  let mkAt i = unforcedBuiltinApp accessAtTensorBuiltin (mkAtArgs i)
  fmap mkAt [0 .. (dim - 1)]

accessQuantifierLambda :: Thunk Builtin -> (VBinder Builtin, Closure Builtin)
accessQuantifierLambda = \case
  Forced (VLam binder closure) -> (binder, closure)
  Unforced (UnevaluatedThunk env (Lam _ binder body)) -> (thunkifyBinder env binder, Closure env body)
  fn -> developerError $ "Malformed quantifier function" <+> prettyVerbose fn
