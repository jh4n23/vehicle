module Vehicle.Compile.Normalise.TypedValueForced where

import Data.Data (Proxy (..))
import GHC.Stack (HasCallStack)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Code.Interface
import Vehicle.Data.Tensor
import Vehicle.Data.Universe (UniverseLevel)

-----------------------------------------------------------------------------
-- Abstracting over the return type

class (Monad m) => TypedEvalScheme expr builtin m | expr -> builtin where
  handleBuiltin :: builtin -> UnforcedSpine builtin -> m expr
  forceMeta :: MetaID -> UnforcedSpine builtin -> m expr

  handleUniverse :: Proxy builtin -> Maybe (UniverseLevel -> m expr)
  handleBoundVar :: Lv -> UnforcedSpine builtin -> m expr
  handlePi :: Maybe (GenericBinder (Thunk builtin) -> Closure builtin -> m expr)
  handleLam :: Maybe (GenericBinder (Thunk builtin) -> Closure builtin -> m expr)
  handleRecord :: Maybe (Thunk builtin -> UnforcedRecordFields builtin -> m expr)
  handleFreeVar :: Identifier -> UnforcedSpine builtin -> m expr
  handleRecordAcc :: Thunk builtin -> Thunk builtin -> FieldName -> UnforcedSpine builtin -> m expr

  patternMatch :: ForcedValue builtin -> m expr

instance (Monad m) => TypedEvalScheme (ForcedValue builtin) builtin m where
  handleBuiltin b args = return $ VBuiltin b args
  forceMeta m args = return $ VMeta m args
  handleUniverse _ = Just $ return . VUniverse
  handleRecord = Just (\typ fields -> return $ VRecord typ fields)
  handlePi = Just (\binder closure -> return $ VPi binder closure)
  handleLam = Just $ \binder closure -> return $ VLam binder closure
  handleBoundVar lv args = return $ VBoundVar lv args
  handleFreeVar ident args = return $ VFreeVar ident args
  handleRecordAcc typ record field args = return $ VRecordAcc typ record field args
  patternMatch = return

-------------------------------------------------------------------------------
-- Records

data RecordValue builtin
  = VRecordRecord (Thunk builtin) !(UnforcedRecordFields builtin)
  | VRecordFreeVar Identifier (UnforcedSpine builtin)
  | VRecordMeta MetaID (UnforcedSpine builtin)
  | VRecordBuiltin builtin (UnforcedSpine builtin)
  | VRecordBoundVar Lv (UnforcedSpine builtin)
  | VRecordRecordAcc (Thunk builtin) (Thunk builtin) FieldName (UnforcedSpine builtin)

toRecordValue :: ForcedValue builtin -> RecordValue builtin
toRecordValue = \case
  VRecord typ fields -> VRecordRecord typ fields
  VBuiltin b spine -> VRecordBuiltin b spine
  VFreeVar ident spine -> VRecordFreeVar ident spine
  VMeta m spine -> VRecordMeta m spine
  VBoundVar v spine -> VRecordBoundVar v spine
  VRecordAcc typ record field spine -> VRecordRecordAcc typ record field spine
  VPi {} -> illTyped "VPi"
  VLam {} -> illTyped "VLam"
  VUniverse {} -> illTyped "VUniverse"
  where
    illTyped e = developerError $ "ill-typed function" <+> e

fromRecordValue :: RecordValue builtin -> ForcedValue builtin
fromRecordValue = \case
  VRecordRecord typ fields -> VRecord typ fields
  VRecordBuiltin b spine -> VBuiltin b spine
  VRecordFreeVar ident spine -> VFreeVar ident spine
  VRecordMeta m spine -> VMeta m spine
  VRecordBoundVar v spine -> VBoundVar v spine
  VRecordRecordAcc typ record field spine -> VRecordAcc typ record field spine

instance (Monad m) => TypedEvalScheme (RecordValue builtin) builtin m where
  handleBuiltin b args = return $ VRecordBuiltin b args
  forceMeta m args = return $ VRecordMeta m args
  handleBoundVar lv args = return $ VRecordBoundVar lv args
  handleFreeVar ident args = return $ VRecordFreeVar ident args
  handleRecord = Just $ \record fields -> return $ VRecordRecord record fields
  handleRecordAcc typ record field args = return $ VRecordRecordAcc typ record field args
  handlePi = Nothing
  handleUniverse _ = Nothing
  handleLam = Nothing
  patternMatch = return . toRecordValue

-------------------------------------------------------------------------------
-- Types

-- | A view on all possible expressions that can have type `Type`.
data TypeValue
  = VUnitType
  | VBoolType
  | VIndexType (Thunk Builtin)
  | VNatType
  | VRatType
  | VTensorType (Thunk Builtin) (Thunk Builtin)
  | VListType (Thunk Builtin)
  | VVectorType (Thunk Builtin) (Thunk Builtin)
  | VPiType (UnforcedBinder Builtin) (Closure Builtin)
  | VTypeBoundVar Lv (UnforcedSpine Builtin)
  | VTypeFreeVar Identifier (UnforcedSpine Builtin)

builtinToTypeValue :: Builtin -> UnforcedSpine Builtin -> TypeValue
builtinToTypeValue b spine = case (b, spine) of
  (BuiltinType UnitType, []) -> VUnitType
  (BuiltinType BoolType, []) -> VBoolType
  (BuiltinType RatType, []) -> VRatType
  (BuiltinType IndexType, [n]) -> VIndexType (argExpr n)
  (BuiltinType NatType, []) -> VNatType
  (BuiltinType ListType, [tElem]) -> VListType (argExpr tElem)
  (BuiltinType TensorType, [tElem, ds]) -> VTensorType (argExpr tElem) (argExpr ds)
  (BuiltinType VectorType, [tElem, dim]) -> VVectorType (argExpr tElem) (argExpr dim)
  _ -> developerError $ "ill-typed type" <+> pretty b

toTypeValue :: (HasCallStack) => ForcedValue Builtin -> TypeValue
toTypeValue = \case
  VPi binder body -> VPiType binder body
  VFreeVar ident spine -> VTypeFreeVar ident spine
  VBuiltin b spine -> builtinToTypeValue b spine
  VBoundVar v spine -> VTypeBoundVar v spine
  VMeta {} -> illTyped "VMeta"
  VRecordAcc {} -> illTyped "VRecord"
  VRecord {} -> illTyped "VRecord"
  VLam {} -> illTyped "VLam"
  VUniverse {} -> illTyped "VUniverse"
  where
    illTyped e = developerError $ "ill-typed type" <+> e

instance (Monad m) => TypedEvalScheme TypeValue Builtin m where
  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Just $ \binder closure -> return $ VPiType binder closure
  handleBoundVar lv args = return $ VTypeBoundVar lv args
  handleFreeVar ident args = return $ VTypeFreeVar ident args
  handleRecordAcc = caseTypeError "RecordAcc" "BoolExpr"

  forceMeta = caseTypeError "MetaVar" "BoolExpr"
  handleBuiltin b spine = return $ builtinToTypeValue b spine
  patternMatch = return . toTypeValue

-------------------------------------------------------------------------------
-- Booleans

-- | A view on all possible expressions that can have type `Tensor Bool`.
data BoolValue
  = VBoolLiteral Bool
  | VNot (TensorOp1Args (Thunk Builtin))
  | VAnd (TensorOp2Args (Thunk Builtin))
  | VOr (TensorOp2Args (Thunk Builtin))
  | VImplies (TensorOp2Args (Thunk Builtin))
  | VCompareIndex (ComparisonOp, IndexComparisonArgs (Thunk Builtin))
  | VCompareNat (ComparisonOp, Op2Args (Thunk Builtin))
  | VCompareRatTensor (ComparisonOp, TensorOp2Args (Thunk Builtin))
  | VReduceAndTensor (TensorReductionArgs (Thunk Builtin))
  | VReduceOrTensor (TensorReductionArgs (Thunk Builtin))
  | VQuantifyRatTensor (Quantifier, QuantifyRatTensorArgs (Thunk Builtin) (Closure Builtin))
  | VQuantifyRecord (Quantifier, QuantifyRecordArgs (Thunk Builtin) (Closure Builtin))
  | VBoolIf (IfArgs (Thunk Builtin))
  | VBoolTensorAt (AtTensorArgs (Thunk Builtin))
  | VBoolVectorAt (AtVectorArgs (Thunk Builtin))

builtinToBoolValue :: Builtin -> UnforcedSpine Builtin -> BoolValue
builtinToBoolValue b spine = case VBuiltin b spine of
  (getExpr accessBoolTensorLiteral -> Just (ZeroDimTensor v)) -> VBoolLiteral v
  (getExpr accessAndTensor -> Just args) -> VAnd args
  (getExpr accessOrTensor -> Just args) -> VOr args
  (getExpr accessNotTensor -> Just args) -> VNot args
  (getExpr accessImpliesTensor -> Just args) -> VImplies args
  (getExpr accessCompareRatTensorPointwise -> Just args) -> fromComparison $ Left args
  (getExpr accessCompareRatTensorReduced -> Just args) -> fromComparison $ Right args
  (getExpr accessCompareNat -> Just args) -> VCompareNat args
  (getExpr accessCompareIndex -> Just args) -> VCompareIndex args
  (getExpr accessQuantifyRatTensor -> Just args) -> VQuantifyRatTensor args
  (getExpr accessQuantifyRecord -> Just args) -> VQuantifyRecord args
  (getExpr accessReduceAnd -> Just args) -> VReduceAndTensor args
  (getExpr accessReduceOr -> Just args) -> VReduceOrTensor args
  (getExpr accessAtTensor -> Just args) -> VBoolTensorAt args
  (getExpr accessIf -> Just args) -> VBoolIf args
  _ -> developerError $ "ill-typed Bool builtin:" <+> pretty b

toBoolValue :: (HasCallStack) => ForcedValue Builtin -> BoolValue
toBoolValue expr = case expr of
  VBuiltin b spine -> builtinToBoolValue b spine
  _ -> developerError $ "ill-typed Bool expression:" <+> prettyVerbose expr

{-
fromBoolValue :: BoolValue -> Thunk Builtin
fromBoolValue = \case
  VBoolLiteral y -> mkExpr accessBoolTensorLiteral (ZeroDimTensor y)
  VAnd args -> mkExpr accessAndTensor args
  VOr args -> mkExpr accessOrTensor args
  VNot args -> mkExpr accessNotTensor args
  VCompareNat args -> mkExpr accessCompareNat args
  VCompareIndex args -> mkExpr accessCompareIndex args
  VCompareRatTensor args -> toComparison args
  VQuantifyRatTensor args -> mkExpr accessQuantifyRatTensor args
  VQuantifyRecord _args -> undefined
  VReduceAndTensor args -> mkExpr accessReduceAnd args
  VReduceOrTensor args -> mkExpr accessReduceOr args
  VBoolIf args -> mkExpr accessIf args
  VBoolAt args -> mkExpr accessAtTensor args
-}
fromComparison ::
  Either
    (ComparisonOp, TensorOp2Args (Thunk Builtin))
    (ComparisonOp, TensorReduceComparisonArgs (Thunk Builtin)) ->
  BoolValue
fromComparison = \case
  Left (op, args) -> VCompareRatTensor (op, args)
  Right (op, TensorReduceComparisonArgs d ds e1 e2) ->
    VCompareRatTensor (op, TensorOp2Args (Forced $ IDimCons d ds) e1 e2)

{-
evalCompareRatTensor :: (MonadNormBuiltin m, MonadFreeContext Builtin m, MonadReadableNameContext m) => ComparisonOp -> EvalSimple Value Value TensorOp2Args Builtin m
evalCompareRatTensor op args@(TensorOp2Args dims e1 e2) = case toDimensionsValue dims of
  VDimsNil -> evalCompareRatTensorPointwise op args
  VDimsCons d ds -> do
    let reduceArgs = TensorReduceComparisonArgs d ds e1 e2
    namedCtx <- getNameContext
    evalBuiltin namedCtx (DerivedFunction (CompareRatTensorReduced op)) (mkExpr accessSpine reduceArgs)
  _ -> developerError "Unexpected tensorOp2Args for comparison"
-}

instance (Monad m) => TypedEvalScheme BoolValue Builtin m where
  handleBuiltin b spine = return $ builtinToBoolValue b spine
  forceMeta = caseTypeError "MetaVar" "BoolExpr"

  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar = caseTypeError "BoundVar" "BoolExpr"
  handleFreeVar = caseTypeError "FreeVar" "BoolExpr"
  handleRecordAcc = caseTypeError "RecordAcc" "BoolExpr"
  patternMatch = return . toBoolValue

-------------------------------------------------------------------------------
-- Boolean tensors

-- | A view on all possible expressions that can have type `Tensor Bool ds`.
data BoolTensorValue
  = VBoolTensorLiteral (Tensor Bool)
  | VBoolStackTensor (StackTensorArgs (Thunk Builtin))
  | VBoolConstTensor (ConstTensorArgs (Thunk Builtin))
  | VBoolTensorAnd (TensorOp2Args (Thunk Builtin))
  | VBoolTensorOr (TensorOp2Args (Thunk Builtin))
  | VBoolTensorImplies (TensorOp2Args (Thunk Builtin))
  | VBoolTensorCompareRatPointwise (ComparisonOp, TensorOp2Args (Thunk Builtin))
  | VBoolTensorCompareRatReduced (ComparisonOp, TensorReduceComparisonArgs (Thunk Builtin))
  | VBoolTensorQuantifyRat (Quantifier, QuantifyRatTensorArgs (Thunk Builtin) (Closure Builtin))
  | VBoolTensorQuantifyRecord (Quantifier, QuantifyRecordArgs (Thunk Builtin) (Closure Builtin))
  | VBoolTensorNot (TensorOp1Args (Thunk Builtin))
  | VBoolTensorReduceAnd (TensorReductionArgs (Thunk Builtin))
  | VBoolTensorReduceOr (TensorReductionArgs (Thunk Builtin))
  | VBoolTensorCompareIndex (ComparisonOp, IndexComparisonArgs (Thunk Builtin))
  | VBoolTensorCompareNat (ComparisonOp, Op2Args (Thunk Builtin))
  | VBoolTensorTensorAt (AtTensorArgs (Thunk Builtin))
  | VBoolTensorVectorAt (AtVectorArgs (Thunk Builtin))
  | VBoolTensorForeach (ForeachTensorArgs (Thunk Builtin))
  | VBoolTensorIf (IfArgs (Thunk Builtin))

builtinToBoolTensorValue :: Builtin -> UnforcedSpine Builtin -> BoolTensorValue
builtinToBoolTensorValue b spine = case VBuiltin b spine of
  (getExpr accessBoolTensorLiteral -> Just t) -> VBoolTensorLiteral t
  (getExpr accessConstTensor -> Just args) -> VBoolConstTensor args
  (getExpr accessStackTensor -> Just args) -> VBoolStackTensor args
  (getExpr accessAndTensor -> Just args) -> VBoolTensorAnd args
  (getExpr accessOrTensor -> Just args) -> VBoolTensorOr args
  (getExpr accessNotTensor -> Just args) -> VBoolTensorNot args
  (getExpr accessImpliesTensor -> Just args) -> VBoolTensorImplies args
  (getExpr accessQuantifyRatTensor -> Just args) -> VBoolTensorQuantifyRat args
  (getExpr accessQuantifyRecord -> Just args) -> VBoolTensorQuantifyRecord args
  (getExpr accessCompareRatTensorPointwise -> Just args) -> VBoolTensorCompareRatPointwise args
  (getExpr accessCompareRatTensorReduced -> Just args) -> VBoolTensorCompareRatReduced args
  (getExpr accessCompareNat -> Just args) -> VBoolTensorCompareNat args
  (getExpr accessCompareIndex -> Just args) -> VBoolTensorCompareIndex args
  (getExpr accessReduceAnd -> Just args) -> VBoolTensorReduceAnd args
  (getExpr accessReduceOr -> Just args) -> VBoolTensorReduceOr args
  (getExpr accessAtTensor -> Just args) -> VBoolTensorTensorAt args
  (getExpr accessForeachTensor -> Just args) -> VBoolTensorForeach args
  (getExpr accessIf -> Just args) -> VBoolTensorIf args
  _ -> developerError $ "ill-typed BoolTensor expression:" <+> pretty b <+> prettyVerbose spine

toBoolTensorValue :: ForcedValue Builtin -> BoolTensorValue
toBoolTensorValue = \case
  VBuiltin b spine -> builtinToBoolTensorValue b spine
  VMeta {} -> illTyped "VMeta"
  VBoundVar {} -> illTyped "VBoundVar"
  VFreeVar {} -> illTyped "VFreeVar"
  VRecordAcc {} -> illTyped "VRecordAcc"
  VPi {} -> illTyped "VPi"
  VLam {} -> illTyped "VLam"
  VRecord {} -> illTyped "VRecord"
  VUniverse {} -> illTyped "VUniverse"
  where
    illTyped e = developerError $ "ill-typed BoolTensor expression:" <+> e

instance (Monad m) => TypedEvalScheme BoolTensorValue Builtin m where
  handleBuiltin b spine = return $ builtinToBoolTensorValue b spine
  forceMeta = caseTypeError "MetaVar" "BoolExpr"

  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar = caseTypeError "BoundVar" "BoolExpr"
  handleFreeVar = caseTypeError "FreeVar" "BoolExpr"
  handleRecordAcc = caseTypeError "RecordAcc" "BoolExpr"
  patternMatch = return . toBoolTensorValue

{-
fromComparisonTensor ::
  Either
    (ComparisonOp, TensorOp2Args (Thunk Builtin))
    (ComparisonOp, TensorReduceComparisonArgs (Thunk Builtin)) ->
  BoolTensorValue
fromComparisonTensor = \case
  Left (op, args) -> VBoolTensorCompareRat (op, args)
  Right (op, TensorReduceComparisonArgs d ds e1 e2) ->
    VBoolTensorCompareRat (op, TensorOp2Args (Forced $ IDimCons d ds) e1 e2)

toComparisonTensor :: (ComparisonOp, TensorOp2Args (Thunk Builtin)) -> ForcedValue Builtin
toComparisonTensor (op, TensorOp2Args dims e1 e2) = case dims of
  Unforced {} -> developerError "Unexpected unforced dims for comparison"
  Forced vDims -> case toDimensionsValue vDims of
    VDimsNil -> mkExpr accessCompareRatTensorPointwise (op, TensorOp2Args dims e1 e2)
    VDimsCons d ds -> mkExpr accessCompareRatTensorReduced (op, TensorReduceComparisonArgs d ds e1 e2)
    _ -> developerError "Unexpected tensorOp2Args for comparison"
-}
-------------------------------------------------------------------------------
-- Naturals

-- | A view on all possible expressions that can have type `Nat`.
data NatValue
  = VNatLiteral Int
  | VNatBoundVar Lv (UnforcedSpine Builtin)
  | VNatIf (IfArgs (Thunk Builtin))
  | VNatAdd (Op2Args (Thunk Builtin))
  | VNatMul (Op2Args (Thunk Builtin))
  | VNatParameter Identifier

builtinToNatValue :: Builtin -> UnforcedSpine Builtin -> NatValue
builtinToNatValue b spine = case VBuiltin b spine of
  (getExpr accessNatLiteral -> Just i) -> VNatLiteral i
  (getExpr accessIf -> Just args) -> VNatIf args
  (getExpr accessAddNat -> Just args) -> VNatAdd args
  (getExpr accessMulNat -> Just args) -> VNatMul args
  _ -> developerError $ "ill-typed Nat expression:" <+> pretty b <+> prettyVerbose spine

toNatValue :: ForcedValue Builtin -> NatValue
toNatValue = \case
  VBuiltin b spine -> builtinToNatValue b spine
  VBoundVar lv spine -> VNatBoundVar lv spine
  VFreeVar ident spine -> case spine of
    [] -> VNatParameter ident
    _ -> illTyped "VFreeVar"
  VMeta {} -> illTyped "VMeta"
  VRecordAcc {} -> illTyped "VRecordAcc"
  VPi {} -> illTyped "VPi"
  VLam {} -> illTyped "VLam"
  VRecord {} -> illTyped "VRecord"
  VUniverse {} -> illTyped "VUniverse"
  where
    illTyped e = developerError $ "ill-typed Nat expression:" <+> e

instance (Monad m) => TypedEvalScheme NatValue Builtin m where
  handleBuiltin b spine = return $ builtinToNatValue b spine
  forceMeta = caseTypeError "MetaVar" "NatValue"

  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar lv args = return $ VNatBoundVar lv args
  handleFreeVar ident spine = return $ case spine of
    [] -> VNatParameter ident
    _ -> caseTypeError "FreeVar" "NatValue"
  handleRecordAcc = caseTypeError "RecordAcc" "NatValue"
  patternMatch = return . toNatValue

-------------------------------------------------------------------------------
-- Index

-- | A view on all possible expressions that can have type `Index n`.
data IndexValue
  = VIndexLiteral Int (Thunk Builtin)
  | VIndexBoundVar Lv (UnforcedSpine Builtin)
  | VIndexIf (IfArgs (Thunk Builtin))
  | VIndexRecordAcc (Thunk Builtin) (Thunk Builtin) FieldName (UnforcedSpine Builtin)
  | VIndexParameter Identifier
  | VIndexAtVector (AtVectorArgs (Thunk Builtin))

builtinToIndexValue :: Builtin -> UnforcedSpine Builtin -> IndexValue
builtinToIndexValue b spine = case VBuiltin b spine of
  (getExpr accessIndexLiteral -> Just (i, args)) -> VIndexLiteral i (indexLiteralDim args)
  (getExpr accessIf -> Just args) -> VIndexIf args
  (getExpr accessAtVector -> Just args) -> VIndexAtVector args
  _ -> developerError $ "ill-typed Index expression:" <+> pretty b <+> prettyVerbose spine

toIndexValue :: ForcedValue Builtin -> IndexValue
toIndexValue = \case
  VBuiltin b spine -> builtinToIndexValue b spine
  VBoundVar lv spine -> VIndexBoundVar lv spine
  VRecordAcc typ record field spine -> VIndexRecordAcc typ record field spine
  VFreeVar ident spine -> case spine of
    [] -> VIndexParameter ident
    _ -> illTyped "VFreeVar"
  VMeta {} -> illTyped "VMeta"
  VPi {} -> illTyped "VPi"
  VLam {} -> illTyped "VLam"
  VRecord {} -> illTyped "VRecord"
  VUniverse {} -> illTyped "VUniverse"
  where
    illTyped e = developerError $ "ill-typed Index expression:" <+> e

instance (Monad m) => TypedEvalScheme IndexValue Builtin m where
  handleBuiltin b spine = return $ builtinToIndexValue b spine
  forceMeta = caseTypeError "MetaVar" "IndexValue"

  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar lv spine = return $ VIndexBoundVar lv spine
  handleFreeVar = caseTypeError "FreeVar" "IndexExpr"
  handleRecordAcc typ record field spine = return $ VIndexRecordAcc typ record field spine
  patternMatch = return . toIndexValue

-------------------------------------------------------------------------------
-- Dimensions

-- | A view on all possible expressions that can have type `List Int`.
data DimensionsValue
  = VDimsNil
  | VDimsCons (Thunk Builtin) (Thunk Builtin)
  | VDimsIf (IfArgs (Thunk Builtin))
  | VDimsBoundVar Lv (UnforcedSpine Builtin)
  | VDimsRecordAcc (Thunk Builtin) (Thunk Builtin) FieldName (UnforcedSpine Builtin)

builtinToDimensionsValue :: Builtin -> UnforcedSpine Builtin -> DimensionsValue
builtinToDimensionsValue b spine = case VBuiltin b spine of
  (getExpr accessNil -> Just (NilArgs {})) -> VDimsNil
  (getExpr accessCons -> Just (ConsArgs _ x xs)) -> VDimsCons x xs
  (getExpr accessIf -> Just args) -> VDimsIf args
  _ -> developerError $ "ill-typed Dimensions expression:" <+> pretty b

toDimensionsValue :: (HasCallStack) => ForcedValue Builtin -> DimensionsValue
toDimensionsValue = \case
  VBuiltin b spine -> builtinToDimensionsValue b spine
  VRecordAcc typ record field spine -> VDimsRecordAcc typ record field spine
  VMeta {} -> illTyped "VMeta"
  VBoundVar {} -> illTyped "VBoundVar"
  VFreeVar {} -> illTyped "VFreeVar"
  VPi {} -> illTyped "VPi"
  VLam {} -> illTyped "VLam"
  VRecord {} -> illTyped "VRecord"
  VUniverse {} -> illTyped "VUniverse"
  where
    illTyped e = developerError $ "ill-typed Dimensions expression:" <+> e

instance (Monad m) => TypedEvalScheme DimensionsValue Builtin m where
  handleUniverse _ = Nothing
  handlePi = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handleBoundVar = caseTypeError "BoundVar" "RatTensorValue"
  handleFreeVar = caseTypeError "FreeVar" "RatTensorValue"
  handleRecordAcc typ record field spine = return $ VDimsRecordAcc typ record field spine

  handleBuiltin b spine = return $ builtinToDimensionsValue b spine
  forceMeta = caseTypeError "Meta" "RatTensorValue"
  patternMatch = return . toDimensionsValue

-------------------------------------------------------------------------------
-- Vector

-- | A view on all possible expressions that can have type `Nat`.
data VectorValue
  = VVectorBoundVar Lv (UnforcedSpine Builtin)
  | VVectorDataset Identifier
  | VVectorLiteral (VectorLitArgs (Thunk Builtin))
  | VVectorIf (IfArgs (Thunk Builtin))
  | VVectorForeach (ForeachVectorArgs (Thunk Builtin))
  | VVectorRecordAcc (Thunk Builtin) (Thunk Builtin) FieldName (UnforcedSpine Builtin)

builtinToVectorValue :: Builtin -> UnforcedSpine Builtin -> VectorValue
builtinToVectorValue b spine = case VBuiltin b spine of
  (getExpr accessVecLit -> Just args) -> VVectorLiteral args
  (getExpr accessIf -> Just args) -> VVectorIf args
  (getExpr accessForeachVector -> Just args) -> VVectorForeach args
  _ -> developerError $ "ill-typed Vector expression:" <+> pretty b

toVectorValue :: ForcedValue Builtin -> VectorValue
toVectorValue value = case value of
  VBoundVar v spine -> VVectorBoundVar v spine
  VFreeVar ident [] -> VVectorDataset ident
  VBuiltin b spine -> builtinToVectorValue b spine
  VRecordAcc typ record field spine -> VVectorRecordAcc typ record field spine
  _ -> developerError $ "ill-typed Vector expression:" <+> prettyVerbose value

instance (Monad m) => TypedEvalScheme VectorValue Builtin m where
  handleBuiltin b spine = return $ builtinToVectorValue b spine
  forceMeta = caseTypeError "MetaVar" "IndexValue"

  handleUniverse _ = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handlePi = Nothing
  handleBoundVar lv spine = return $ VVectorBoundVar lv spine
  handleFreeVar = caseTypeError "FreeVar" "IndexExpr"
  handleRecordAcc typ record field spine = return $ VVectorRecordAcc typ record field spine
  patternMatch = return . toVectorValue

-------------------------------------------------------------------------------
-- Rational Tensors

-- | A view on all possible expressions that can have type `Tensor Rat`.
data RatTensorValue
  = VRatTensorLiteral ExtendedRatTensor
  | VRatConstTensor (ConstTensorArgs (Thunk Builtin))
  | VRatStackTensor (StackTensorArgs (Thunk Builtin))
  | VReduceAddRatTensor (TensorReductionArgs (Thunk Builtin))
  | VReduceMulRatTensor (TensorReductionArgs (Thunk Builtin))
  | VReduceMinRatTensor (TensorReductionArgs (Thunk Builtin))
  | VReduceMaxRatTensor (TensorReductionArgs (Thunk Builtin))
  | VNegRatTensor (TensorOp1Args (Thunk Builtin))
  | VLogRatTensor (TensorOp1Args (Thunk Builtin))
  | VExpRatTensor (TensorOp1Args (Thunk Builtin))
  | VAddRatTensor (TensorOp2Args (Thunk Builtin))
  | VSubRatTensor (TensorOp2Args (Thunk Builtin))
  | VMulRatTensor (TensorOp2Args (Thunk Builtin))
  | VDivRatTensor (TensorOp2Args (Thunk Builtin))
  | VMinRatTensor (TensorOp2Args (Thunk Builtin))
  | VMaxRatTensor (TensorOp2Args (Thunk Builtin))
  | VPowRatTensor (TensorOp2Args (Thunk Builtin))
  | VRatAtTensor (AtTensorArgs (Thunk Builtin))
  | VRatAtVector (AtVectorArgs (Thunk Builtin))
  | VRatForeach (ForeachTensorArgs (Thunk Builtin))
  | VIfRatTensor (IfArgs (Thunk Builtin))
  | VNetworkApplication Identifier (NetworkAppArgs (Thunk Builtin))
  | VParameterOrDataset Identifier
  | VRatTensorBoundVar Lv
  | VRatTensorRecordAcc (Thunk Builtin) (Thunk Builtin) FieldName (UnforcedSpine Builtin)

toRatTensorValueFromBuiltin ::
  Builtin ->
  UnforcedSpine Builtin ->
  RatTensorValue
toRatTensorValueFromBuiltin b spine = case VBuiltin b spine of
  -- Compilable builtins
  (getExpr accessRatTensorLiteral -> Just t) -> VRatTensorLiteral t
  (getExpr accessConstTensor -> Just args) -> VRatConstTensor args
  (getExpr accessStackTensor -> Just args) -> VRatStackTensor args
  -- Non-compilable builtins
  (getExpr accessReduceAddRat -> Just args) -> VReduceAddRatTensor args
  (getExpr accessReduceMulRat -> Just args) -> VReduceMulRatTensor args
  (getExpr accessReduceMinRat -> Just args) -> VReduceMinRatTensor args
  (getExpr accessReduceMaxRat -> Just args) -> VReduceMaxRatTensor args
  (getExpr accessNegRatTensor -> Just args) -> VNegRatTensor args
  (getExpr accessLogRatTensor -> Just args) -> VLogRatTensor args
  (getExpr accessExpRatTensor -> Just args) -> VExpRatTensor args
  (getExpr accessAddRatTensor -> Just args) -> VAddRatTensor args
  (getExpr accessSubRatTensor -> Just args) -> VSubRatTensor args
  (getExpr accessMulRatTensor -> Just args) -> VMulRatTensor args
  (getExpr accessDivRatTensor -> Just args) -> VDivRatTensor args
  (getExpr accessMinRatTensor -> Just args) -> VMinRatTensor args
  (getExpr accessMaxRatTensor -> Just args) -> VMaxRatTensor args
  (getExpr accessPowRatTensor -> Just args) -> VPowRatTensor args
  (getExpr accessIf -> Just args) -> VIfRatTensor args
  (getExpr accessAtTensor -> Just args) -> VRatAtTensor args
  (getExpr accessAtVector -> Just args) -> VRatAtVector args
  (getExpr accessForeachTensor -> Just args) -> VRatForeach args
  _ -> developerError $ "ill-typed RatTensor builtin:" <+> pretty b

toRatTensorValue :: ForcedValue Builtin -> RatTensorValue
toRatTensorValue = \case
  VBuiltin b spine -> toRatTensorValueFromBuiltin b spine
  VBoundVar lv spine -> case spine of
    [] -> VRatTensorBoundVar lv
    _ -> illTyped "VBoundVar"
  VFreeVar ident spine -> case spine of
    (getExpr accessSpine -> Just args) -> VNetworkApplication ident args
    [] -> VParameterOrDataset ident
    _ -> illTyped "VFreeVar"
  VRecordAcc typ record field spine -> VRatTensorRecordAcc typ record field spine
  VMeta {} -> illTyped "VMeta"
  VPi {} -> illTyped "VPi"
  VLam {} -> illTyped "VLam"
  VRecord {} -> illTyped "VRecord"
  VUniverse {} -> illTyped "VUniverse"
  where
    illTyped e = developerError $ "ill-typed RatTensor expression:" <+> e

instance (Monad m) => TypedEvalScheme RatTensorValue Builtin m where
  handleUniverse _ = Nothing
  handlePi = Nothing
  handleLam = Nothing
  handleRecord = Nothing
  handleBoundVar lv spine = return $ case spine of
    [] -> VRatTensorBoundVar lv
    _ -> caseTypeError "BoundVar" "RatTensorValue"
  handleFreeVar ident spine = return $ case spine of
    (getExpr accessSpine -> Just args) -> VNetworkApplication ident args
    [] -> VParameterOrDataset ident
    _ -> caseTypeError "FreeVar" "RatTensorValue"
  handleRecordAcc typ record field spine = return $ VRatTensorRecordAcc typ record field spine

  forceMeta = caseTypeError "Meta" "RatTensorValue"
  handleBuiltin b spine = return $ toRatTensorValueFromBuiltin b spine
  patternMatch = return . toRatTensorValue

caseTypeError :: Doc a -> Doc a -> v
caseTypeError op exprType = developerError $ "not expecting" <+> squotes op <+> "in expression of type" <+> exprType

-- | Reduces a tensor value `x` to `[x!0, x!1, ..., x!n]`
etaReduceTensor ::
  (BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasTensors builtin, BuiltinHasListLiterals builtin, BuiltinHasNatType builtin) =>
  UnforcedType builtin ->
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
  let mkAt i = Forced $ mkExpr accessAtTensor (mkAtArgs i)
  fmap mkAt [0 .. (dim - 1)]
