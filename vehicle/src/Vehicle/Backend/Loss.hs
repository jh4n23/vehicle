module Vehicle.Backend.Loss
  ( convertToLossTensors,
  )
where

import Data.Maybe (maybeToList)
import Data.Proxy (Proxy (..))
import Vehicle.Backend.Loss.Core
import Vehicle.Backend.Loss.Domain (compileQuantifier)
import Vehicle.Backend.Loss.LogicCompilation (findAndCompileLogic)
import Vehicle.Backend.Loss.LossCompilation
import Vehicle.Backend.Loss.LossCompilation qualified as Loss ()
import Vehicle.Backend.Prelude (DifferentiableLogicID)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.NBE (forceValue)
import Vehicle.Compile.Normalise.Quote (unnormalise)
import Vehicle.Compile.Prelude
import Vehicle.Compile.TypedView
import Vehicle.Data.Builtin.Loss (LossBuiltin)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Builtin.Standard.Normalise ()
import Vehicle.Data.Code.Interface.Patterns
import Vehicle.Data.Code.Value
import Vehicle.Data.DifferentiableLogic
import Vehicle.Data.Variable.Free.Context (MonadFreeContext, addDeclEntryToContext, runFreshFreeContextT)

convertToLossTensors ::
  (MonadCompile m) =>
  DifferentiableLogicID ->
  Prog Builtin ->
  m (Prog LossBuiltin)
convertToLossTensors logicID prog@(Main ds) =
  logCompilerSection2 MinDetail currentPass $ do
    logic <- findAndCompileLogic logicID prog
    runFreshFreeContextT (Proxy @Builtin) $ do
      Main <$> convertDecls logicID logic ds

--------------------------------------------------------------------------------
-- Program conversion

convertDecls ::
  (MonadCompile m, MonadFreeContext Builtin m) =>
  DifferentiableLogicID ->
  DifferentiableLogicImplementation ->
  [Decl Builtin] ->
  m [Decl LossBuiltin]
convertDecls logicID logic = \case
  [] -> return []
  decl : decls -> do
    maybeLossDecl <- convertDecl logicID logic decl
    decls' <- addDeclEntryToContext decl $ convertDecls logicID logic decls
    return $ maybeToList maybeLossDecl ++ decls'

convertDecl ::
  (MonadCompile m, MonadFreeContext Builtin m) =>
  DifferentiableLogicID ->
  DifferentiableLogicImplementation ->
  Decl Builtin ->
  m (Maybe (Decl LossBuiltin))
convertDecl logicID logic decl = do
  logCompilerSection2 MinDetail ("declaration" <+> quotePretty (identifierOf decl)) $ do
    runMonadLogicT logicID logic decl $ do
      case decl of
        DefAbstract p ident sort typ
          | isExternalResourceDecl decl -> do
              let typeValue = thunkifyExpr emptyBoundEnv typ
              Just <$> convertResourceDecl p ident sort typeValue
          | otherwise -> return Nothing
        DefFunction p ident ann typ expr
          | isPropertyDecl decl -> do
              let typeValue = thunkifyExpr emptyBoundEnv typ
              let exprValue = thunkifyExpr emptyBoundEnv expr
              Just <$> convertPropertyDecl p ident ann typeValue exprValue
          | otherwise -> return Nothing
        DefRecord {} -> return Nothing

convertResourceDecl ::
  (MonadLogic m) =>
  Provenance ->
  Identifier ->
  DefAbstractSort ->
  VType Builtin ->
  m (Decl LossBuiltin)
convertResourceDecl p ident sort typ = do
  -- Keep resource declarations, converting their type appropriately.
  -- TODO what about boolean parameters?
  typ' <- convertDeclType typ
  return $ DefAbstract p ident sort typ'

convertPropertyDecl ::
  (MonadLogic m) =>
  Provenance ->
  Identifier ->
  DefFunctionSort ->
  VType Builtin ->
  Thunk Builtin ->
  m (Decl LossBuiltin)
convertPropertyDecl p ident ann typ value = do
  lossType <- convertDeclType typ
  lossValue <- convertMultiProperty typ value
  let lossExpr = unnormalise 0 lossValue
  let lossTensorDecl = DefFunction p ident ann lossType lossExpr
  return lossTensorDecl

convertDeclType :: (MonadLogic m) => VType Builtin -> m (Type LossBuiltin)
convertDeclType typ = unnormalise 0 <$> convertType typ

convertMultiProperty :: (MonadLogic m) => VType Builtin -> Thunk Builtin -> m (Thunk LossBuiltin)
convertMultiProperty typ value = do
  forcedType <- forceValue typ
  case toTypeValue forcedType of
    VTensorType _ _ds -> convertTensorProperty value
    VVectorType tElem _d -> convertVectorProperty tElem value
    _ -> unexpectedExprError currentPass "Impossible property type"

convertVectorProperty :: (MonadLogic m) => VType Builtin -> Thunk Builtin -> m (Thunk LossBuiltin)
convertVectorProperty typ value = do
  dims <- getVectorDims typ
  forcedValue <- forceValue value
  case toVectorValue forcedValue of
    VVectorBoundVar lv spine -> convertBoundVar lv spine
    VVectorDataset ident -> return $ Forced $ VFreeVar ident []
    VVectorLiteral args -> convertVecLiteralArgs (convertMultiProperty typ) (Forced IBoolType, dims) args
    VVectorIf args -> convertIf args
    VVectorForeach args -> convertVecForeachArgs (convertMultiProperty typ) (Forced IBoolType, dims) args

convertTensorProperty :: (MonadLogic m) => Thunk Builtin -> m (Thunk LossBuiltin)
convertTensorProperty value = do
  forcedValue <- forceValue value
  case toBoolTensorValue forcedValue of
    VBoolTensorLiteral bs -> convertBoolTensorLiteral bs
    VBoolConstTensor args -> convertConstTensor convertTensorProperty args
    VBoolStackTensor args -> convertStackTensor convertTensorProperty args
    VBoolTensorAnd args -> convertAnd =<< convertTensorOp2 convertTensorProperty args
    VBoolTensorOr args -> convertOr =<< convertTensorOp2 convertTensorProperty args
    VBoolTensorNot args -> convertNot =<< convertTensorOp1 convertTensorProperty args
    VBoolTensorCompareNat args -> convertNatComparison args
    VBoolTensorCompareIndex args -> convertIndexComparison args
    VBoolTensorCompareRatPointwise args -> convertRatTensorPointwiseComparison args
    VBoolTensorCompareRatReduced args -> convertRatTensorReducedComparison args
    VBoolTensorQuantifyRat args -> compileQuantifier args
    VBoolTensorReduceAnd args -> convertReduceAnd =<< convertTensorReduction convertTensorProperty args
    VBoolTensorReduceOr args -> convertReduceOr =<< convertTensorReduction convertTensorProperty args
    VBoolTensorBoolIf args -> convertIf args
    VBoolTensorAt args -> convertAtTensor convertTensorProperty args
    VBoolTensorForeach args -> convertForeachTensor convertTensorProperty args

getVectorDims :: (MonadLogic m) => VType Builtin -> m (VDims Builtin)
getVectorDims typ = do
  forcedType <- forceValue typ
  case toTypeValue forcedType of
    VTensorType _ ds -> return ds
    VVectorType t d -> Forced . ICons (Forced INatType) d <$> getVectorDims t
    _ -> developerError "Impossible property type"
