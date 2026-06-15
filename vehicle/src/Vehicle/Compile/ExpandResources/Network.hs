module Vehicle.Compile.ExpandResources.Network
  ( checkNetwork,
    getTensorRecordShape,
  )
where

import Control.Monad.Except (MonadError (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map qualified as Map
import Vehicle.Compile.Error
import Vehicle.Compile.ExpandResources.Core
import Vehicle.Compile.Normalise.NBE (evalInEmptyEnv, normaliseClosureInCtx)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Resource
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.TypedView (DimensionsValue (..), TypeValue (..), toTypeValue, toDimensionsValue)
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (TensorShape)
import Vehicle.Data.Variable.Free.Context (MonadFreeContext, getRecordFieldNames, getRecordFields)
import Vehicle.Verify.Core (NetworkContextInfo (..))
import Vehicle.Data.Builtin.Interface.Normalise (getDims)

--------------------------------------------------------------------------------
-- Network typing

checkNetwork ::
  forall m.
  (MonadExpandResources m) =>
  DeclProvenance ->
  GluedType Builtin ->
  FilePath ->
  m NetworkContextInfo
checkNetwork decl networkType filePath = do
  typ <- getNetworkType decl networkType
  return $ NetworkContextInfo filePath typ

-- | Decomposes the Pi types in a network type signature, checking that the
--  binders are explicit and their types are equal.
getNetworkType ::
  forall m.
  (MonadExpandResources m) =>
  DeclProvenance ->
  GluedType Builtin ->
  m NetworkType
getNetworkType decl networkType = case normalised networkType of
  VPi binder closure
    | visibilityOf binder /= Explicit -> typingError
    | otherwise -> do
        inputDetails <- tensorType Input (typeOf binder)
        resultType <- normaliseClosureInCtx mempty binder closure
        outputDetails <- tensorType Output resultType
        let networkDetails = NetworkType inputDetails outputDetails
        return networkDetails
  _ -> compilerDeveloperError "Should have caught the fact that the network type is not a function during type-checking"
  where
    tensorType :: InputOrOutput -> VType Builtin -> m NetworkIOType
    tensorType io t = case toTypeValue t of
      VRatTensorType dims -> do
        shape <- tensorDimensions io dims
        return $ UniModal (TensorIOType $ NetworkTensorType NetworkRatType shape)
      VFreeTypeVar ident _spine -> do
        fieldNames <- getRecordFieldNames ident
        fields <- getRecordFields ident
        shape <- getTensorRecordShape fields
        return $ UniModal (RecordIOType $ NetworkRecordType NetworkRatType ident shape $ NonEmpty.toList fieldNames)
      _ -> typingError

    tensorDimensions :: InputOrOutput -> VType Builtin -> m TensorShape
    tensorDimensions io dims = case toDimensionsValue dims of
      VDimsNil -> return []
      VDimsCons d ds -> (:) <$> tensorDimension io d <*> tensorDimensions io ds
      _ -> throwError $ NetworkTypeHasVariableSizeTensor decl networkType dims io

    tensorDimension :: InputOrOutput -> VType Builtin -> m Int
    tensorDimension io dim = case dim of
      INatLiteral n -> return n
      VFreeVar varIdent _ -> do
        implicitParameters <- getInferableParameterContext
        case Map.lookup varIdent implicitParameters of
          Just (_, _, Nothing) -> throwError $ NetworkTypeHasImplicitSizeTensor decl networkType varIdent io
          Just (_, _, Just (_, _, d)) -> return d
          Nothing -> do
            explicitParameters <- getExplicitParameterContext
            case Map.lookup varIdent explicitParameters of
              Nothing -> throwError $ NetworkTypeHasVariableSizeTensor decl networkType dim io
              Just value -> tensorDimension io value
      _ -> throwError $ NetworkTypeHasVariableSizeTensor decl networkType dim io

    typingError :: m a
    typingError =
      compilerDeveloperError $
        "Invalid network type"
          <+> squotes (prettyVerbose $ normalised networkType)
          <+> "should have been caught during type-checking"

getTensorRecordShape ::
  (MonadFreeContext Builtin m) =>
  GenericRecordFields (Expr Builtin) ->
  m TensorShape
getTensorRecordShape [] = developerError "@tensor record should not have empty fields"
getTensorRecordShape fields@((_n, typ) : _fs) = do
  value <- evalInEmptyEnv typ
  return $ case toTypeValue value of
    VRatTensorType dims -> do
      case getDims dims of
        Just d -> length fields : d
        Nothing -> [length fields]
    _ -> [length fields]
