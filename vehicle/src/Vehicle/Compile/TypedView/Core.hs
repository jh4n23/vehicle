module Vehicle.Compile.TypedView.Core where

import Data.List.NonEmpty qualified as NonEmpty
import GHC.Stack (HasCallStack)
import Vehicle.Compile.Normalise.NBE (MonadNorm)
import Vehicle.Compile.Prelude (Lv)
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Data.AST.Expr.Scoped
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor
import Vehicle.Prelude

data IfTree a
  = IfTree (Expr Builtin) (IfTree a) (IfTree a)
  | IfLeaf a

forIfTreeM :: (Monad m) => IfTree a -> (a -> m (IfTree b)) -> m (IfTree b)
forIfTreeM tree f = case tree of
  IfLeaf v -> f v
  IfTree c t1 t2 -> IfTree c <$> forIfTreeM t1 f <*> forIfTreeM t2 f

class TypedEvalScheme expr where
  handlePi :: Binder Builtin -> Expr Builtin -> expr
  handleBoundVar :: Lv -> Args Builtin -> expr
  handleFreeVar :: Identifier -> Args Builtin -> expr
  handleBuiltin :: Builtin -> Args Builtin -> expr

typedEval :: (TypedEvalScheme typedExpr, MonadNorm Builtin m) => BoundEnv Builtin -> Expr Builtin -> m typedExpr
typedEval env = \case
  Hole {} -> resolutionError currentPass "Hole"
  Meta {} -> resolutionError currentPass "Meta"
  Universe _ u -> return $ VUniverse u
  BoundVar _ v -> forceValue $ lookupIxInEnv env v
  FreeVar _ v -> forceValue =<< lookupIdentValue v
  Builtin _ b -> return $ VBuiltin b []
  Lam _ binder body -> return $ VLam (thunkifyBinder env binder) (Closure env body)
  Pi _ binder body -> handlePi binder body
  Let _ bound binder body -> do
    let boundNormExpr = thunkifyExpr env bound
    let newBoundEnv = extendEnvWithDefined boundNormExpr binder env
    typedEval newBoundEnv body
  App fun args ->
    typedEvalApp env fun (NonEmpty.toList args)
  Record _p recordType fields -> do
    let recordType' = thunkifyExpr env recordType
    let fields' = mapRecordFields (thunkifyExpr env) fields
    return $ VRecord recordType' $ OMap.fromList fields'
  RecordProj _p recordType record field -> do
    record' <- forceExpr env record
    case record' of
      VRecord _ fields -> do
        let fieldValue = lookupRecordFieldS fields field
        forceValue fieldValue
      _ -> do
        let recordType' = thunkifyExpr env recordType
        return $ VRecordAcc recordType' (Forced record') field []

typedEvalApp :: (MonadNorm Builtin m) => BoundEnv Builtin -> Expr Builtin -> Args Builtin -> m typedExpr
typedEvalApp env fn args = do
  forcedFun <- typedEval env fn
  case args of
    [] -> return _
    (a : as) -> do
      result <- case forcedFun of
        VFunctionBuiltin b spine -> handleBuiltin b (spine <> args)
        VFunctionFreeVar v spine -> handleFreeVar v (spine <> args)
        VFunctionLam binder closure
          | not (visibilityMatches binder a) ->
              visibilityError forcedFun a
          | otherwise -> do
              -- TODO force deeply?
              let body = extendClosure closure binder (argExpr a)
              forceApp body as
        VMeta v spine -> return $ VMeta v (spine <> args)
        VBoundVar v spine -> return $ VBoundVar v (spine <> args)
        VRecordAcc recordType record field spine -> return $ VRecordAcc recordType record field (spine <> args)
      showAppExit result
      return result
  where
    unexpected name = unexpectedExprError currentPass (name <+> prettyVerbose args)

-------------------------------------------------------------------------------
-- Functions

data FunctionExpr
  = VFunctionLam (Binder Builtin) (Expr Builtin)
  | VFunctionBuiltin Builtin (Args Builtin)
  | VFunctionFreeVar Identifier (Args Builtin)

instance TypedEvalScheme FunctionExpr

-------------------------------------------------------------------------------
-- Booleans

-- | A view on all possible expressions that can have type `Bool` that we know how to compile
-- to constraints.
data CompilableBoolTensorExpr
  = VBoolTensorLiteral (Tensor Bool)
  | VBoolStackTensor (StackTensorArgs (Expr Builtin))
  | VBoolConstTensor (ConstTensorArgs (Expr Builtin))
  | VBoolTensorAnd (TensorOp2Args (Expr Builtin))
  | VBoolTensorOr (TensorOp2Args (Expr Builtin))
  | VBoolTensorCompareRatReduced (ComparisonOp, TensorOp2Args (Expr Builtin))
  | VBoolTensorQuantifyRat (Quantifier, QuantifyRatTensorArgs (Expr Builtin))
  | VBoolTensorNot (TensorOp1Args (Expr Builtin))

-- | A view on all possible expressions that can have type `Bool`.
data BoolTensorExpr
  = VCompilableBoolTensorExpr CompilableBoolTensorExpr
  | VBoolTensorReduceAnd (TensorReductionArgs (Expr Builtin))
  | VBoolTensorReduceOr (TensorReductionArgs (Expr Builtin))
  | VBoolTensorCompareIndex (ComparisonOp, IndexComparisonArgs (Expr Builtin))
  | VBoolTensorCompareNat (ComparisonOp, Op2Args (Expr Builtin))
  | VBoolTensorAt (AtTensorArgs (Expr Builtin))
  | VBoolTensorForeach (ForeachTensorArgs (Expr Builtin))
  | VBoolTensorCompareRatPointwise (ComparisonOp, TensorOp2Args (Expr Builtin))
  | VBoolTensorIf (IfArgs (Expr Builtin))

instance TypedEvalScheme BoolTensorExpr where
  handlePi = _

  handleBoundVar = _

  handleFreeVar = _

  handleBuiltin b spine = case normAppList (Builtin mempty b) spine of
    (getExpr accessBoolTensorLiteral -> Just t) -> VCompilableBoolTensorExpr $ VBoolTensorLiteral t
    (getExpr accessConstTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolConstTensor args
    (getExpr accessStackTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolStackTensor args
    (getExpr accessAndTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorAnd args
    (getExpr accessOrTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorOr args
    (getExpr accessNotTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorNot args
    (getExpr accessCompareRatTensorPointwise -> Just args) -> VBoolTensorCompareRatPointwise args
    (getExpr accessQuantifyRatTensor -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorQuantifyRat args
    (getExpr accessCompareRatTensorReduced -> Just args) -> VCompilableBoolTensorExpr $ VBoolTensorCompareRatReduced args
    (getExpr accessCompareNat -> Just args) -> VBoolTensorCompareNat args
    (getExpr accessCompareIndex -> Just args) -> VBoolTensorCompareIndex args
    (getExpr accessReduceAnd -> Just args) -> VBoolTensorReduceAnd args
    (getExpr accessReduceOr -> Just args) -> VBoolTensorReduceOr args
    (getExpr accessAtTensor -> Just args) -> VBoolTensorAt args
    (getExpr accessForeachTensor -> Just args) -> VBoolTensorForeach args
    (getExpr accessIf -> Just args) -> VBoolTensorIf args
    _ -> developerError $ "ill-typed BoolTensor expression:" <+> pretty b <+> prettyVerbose spine

toBoolTensorExpr :: (HasCallStack) => BoundEnv Builtin -> Expr Builtin -> m BoolTensorExpr
toBoolTensorExpr env expr = typedEval _ _

-------------------------------------------------------------------------------
-- Naturals

newtype CompilableNatExpr
  = VNatLiteral Int

-- | A view on all possible expressions that can have type `Nat`.
data NatExpr
  = VCompilableNat CompilableNatExpr
  | VNatBoundVar Lv (Spine Builtin)
  | VNatIf (IfArgs (Expr Builtin))
  | VNatAdd (Op2Args (Expr Builtin))
  | VNatMul (Op2Args (Expr Builtin))
  | VNatParameter Identifier

toNatValue :: (HasCallStack) => BoundEnv Builtin -> Expr Builtin -> m NatExpr
toNatValue env expr = case expr of
  (getExpr accessNatLiteral -> Just i) -> return $ VCompilableNat $ VNatLiteral i
  (getExpr accessIf -> Just args) -> return $ VNatIf args
  (getExpr accessAddNat -> Just args) -> return $ VNatAdd args
  (getExpr accessMulNat -> Just args) -> return $ VNatMul args
  BoundVar p lv -> return $ VNatBoundVar v spine
  FreeVar ident [] -> return $ VNatParameter ident
  _ -> developerError $ "ill-typed Nat expression:" <+> prettyVerbose expr

-------------------------------------------------------------------------------
-- Index

-- | A view on all possible expressions that can have type `Index n`.
newtype CompilableIndexValue
  = VIndexLiteral Int

data IndexExpr
  = VCompilableIndexValue CompilableIndexValue
  | VIndexBoundVar Lv (Args Builtin)
  | VIndexIf (IfArgs (Expr Builtin))

toIndexValue :: (HasCallStack) => BoundEnv Builtin -> Expr Builtin -> m IndexExpr
toIndexValue e = case e of
  VBoundVar v spine -> VIndexBoundVar v spine
  (getExpr accessIndexLiteral -> Just i) -> VIndexLiteral i
  (getExpr accessIf -> Just args) -> VIndexIf args
  _ -> developerError $ "ill-typed index expression" <+> pretty (show e)

-------------------------------------------------------------------------------
-- Dimensions

-- | A view on all possible expressions that can have type `List Int`.
data CompilableDimensionsExpr
  = VDimsNil
  | VDimsCons (Value Builtin) (Value Builtin)

data DimensionsExpr
  = VCompilableDimensionsExpr CompilableDimensionsExpr
  | VDimsIf (IfArgs (Expr Builtin))
  | VDimsBoundVar Lv (Spine Builtin)

toDimensionsExpr :: (HasCallStack) => BoundEnv Builtin -> Expr Builtin -> m DimensionsExpr
toDimensionsExpr e = case e of
  VBoundVar lv spine -> VDimsBoundVar lv spine
  (getExpr accessNil -> Just (NilArgs {})) -> VDimsNil
  (getExpr accessCons -> Just (ConsArgs _ x xs)) -> VDimsCons x xs
  (getExpr accessIf -> Just args) -> VDimsIf args
  _ -> developerError $ "ill-typed Dimensions expression" <+> prettyVerbose e

-------------------------------------------------------------------------------
-- Rational Tensors

-- | A view on all possible compilable expressions that can have type `Tensor Rat`.
data CompilableRatTensorValue
  = VRatTensorLiteral (Tensor Rational)
  | VRatConstTensor (ConstTensorArgs (Expr Builtin))
  | VRatStackTensor (StackTensorArgs (Expr Builtin))

-- | A view on all possible expressions that can have type `Tensor Rat`.
data RatTensorValue
  = VCompilableRatTensorValue CompilableRatTensorValue
  | VReduceAddRatTensor (TensorReductionArgs (Expr Builtin))
  | VReduceMulRatTensor (TensorReductionArgs (Expr Builtin))
  | VReduceMinRatTensor (TensorReductionArgs (Expr Builtin))
  | VReduceMaxRatTensor (TensorReductionArgs (Expr Builtin))
  | VNegRatTensor (TensorOp1Args (Expr Builtin))
  | VAddRatTensor (TensorOp2Args (Expr Builtin))
  | VSubRatTensor (TensorOp2Args (Expr Builtin))
  | VMulRatTensor (TensorOp2Args (Expr Builtin))
  | VDivRatTensor (TensorOp2Args (Expr Builtin))
  | VMinRatTensor (TensorOp2Args (Expr Builtin))
  | VMaxRatTensor (TensorOp2Args (Expr Builtin))
  | VRatAt (AtTensorArgs (Expr Builtin))
  | VRatForeach (ForeachTensorArgs (Expr Builtin))
  | VIfRatTensor (IfArgs (Expr Builtin))
  | VNetworkApplication Identifier (NetworkAppArgs (Expr Builtin))
  | VParameterOrDataset Identifier
  | VRatTensorBoundVar Lv

toRatTensorValue :: (HasCallStack) => BoundEnv Builtin -> Expr Builtin -> m RatTensorValue
toRatTensorValue env expr = case expr of
  -- Compilable builtins
  (getExpr accessRatTensorLiteral -> Just t) -> return $ VCompilableRatTensorValue $ VRatTensorLiteral t
  (getExpr accessConstTensor -> Just args) -> return $ VCompilableRatTensorValue $ VRatConstTensor args
  (getExpr accessStackTensor -> Just args) -> return $ VCompilableRatTensorValue $ VRatStackTensor args
  -- Non-compilable builtins
  (getExpr accessReduceAddRat -> Just args) -> return $ VReduceAddRatTensor args
  (getExpr accessReduceMulRat -> Just args) -> return $ VReduceMulRatTensor args
  (getExpr accessReduceMinRat -> Just args) -> return $ VReduceMinRatTensor args
  (getExpr accessReduceMaxRat -> Just args) -> return $ VReduceMaxRatTensor args
  (getExpr accessNegRatTensor -> Just args) -> return $ VNegRatTensor args
  (getExpr accessAddRatTensor -> Just args) -> return $ VAddRatTensor args
  (getExpr accessSubRatTensor -> Just args) -> return $ VSubRatTensor args
  (getExpr accessMulRatTensor -> Just args) -> return $ VMulRatTensor args
  (getExpr accessDivRatTensor -> Just args) -> return $ VDivRatTensor args
  (getExpr accessMinRatTensor -> Just args) -> return $ VMinRatTensor args
  (getExpr accessMaxRatTensor -> Just args) -> return $ VMaxRatTensor args
  (getExpr accessIf -> Just args) -> return $ VIfRatTensor args
  (getExpr accessAtTensor -> Just args) -> return $ VRatAt args
  (getExpr accessForeachTensor -> Just args) -> return $ VRatForeach args
  -- Others
  BoundVar lv [] -> return $ VCompilableRatTensorValue $ VRatTensorBoundVar lv
  FreeVar p ident -> VRatTensorFreeVar n spine
  {-
  case getExpr accessSpine spine of
      Just args -> unblock status =<< unblockNetworkApp n args
      -- Parameters and other scalar free vars may appear in constraints used
      -- for quantifier-domain extraction, e.g. `-epsilon < x ! 0 < epsilon`.
      _ -> return expr
      -}
  _ -> illTyped
  where
    illTyped = developerError $ "ill-typed RatTensor expression:" <+> pretty (show expr) -- rettyVerbose expr
