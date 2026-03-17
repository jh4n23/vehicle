module Vehicle.Compile.ExpandResources.Network
  ( checkNetwork,
  )
where

import Control.Monad.Except (MonadError (..))
import Data.Map qualified as Map
import Vehicle.Compile.Error
import Vehicle.Compile.ExpandResources.Core
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Resource
import Vehicle.Compile.TypedView (DimensionsValue (..), TypeValue (..), toDimensionsValue, toTypeValue)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (TensorShape)
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Verify.Core (NetworkContextInfo (..))

--------------------------------------------------------------------------------
-- Network typing

checkNetwork ::
  forall m.
  (MonadExpandResources m) =>
  DeclProvenance ->
  Type Builtin ->
  FilePath ->
  m NetworkContextInfo
checkNetwork decl typ filePath = do
  networkType <- getNetworkType decl typ
  return $ NetworkContextInfo filePath networkType

-- | Decomposes the Pi types in a network type signature, checking that the
--  binders are explicit and their types are equal.
getNetworkType ::
  forall m.
  (MonadExpandResources m, MonadNameContext m) =>
  DeclProvenance ->
  Type Builtin ->
  m NetworkType
getNetworkType decl networkType = do
  forcedNetworkType <- forceExpr emptyBoundEnv networkType
  case forcedNetworkType of
    VPi binder closure
      | visibilityOf binder /= Explicit -> typingError
      | otherwise -> do
          inputDetails <- tensorType Input (Unforced $ typeOf binder)
          outputType <- extendClosureWithBound binder closure
          outputDetails <- addNameToContext binder $ tensorType Output outputType
          let networkDetails = NetworkType inputDetails outputDetails
          return networkDetails
    _ -> compilerDeveloperError "Should have caught the fact that the network type is not a function during type-checking"
  where
    tensorType :: InputOrOutput -> VType Builtin -> m NetworkTensorType
    tensorType io t = do
      forcedType <- forceValue t
      case toTypeValue forcedType of
        VTensorType _ dims -> do
          shape <- tensorDimensions io dims
          return $ NetworkTensorType NetworkRatType shape
        _ -> typingError

    tensorDimensions :: InputOrOutput -> VType Builtin -> m TensorShape
    tensorDimensions io dims = do
      forcedDims <- forceValue dims
      case toDimensionsValue forcedDims of
        VDimsNil -> return []
        VDimsCons d ds -> (:) <$> tensorDimension io d <*> tensorDimensions io ds
        _ -> throwError $ NetworkTypeHasVariableSizeTensor decl networkType dims io

    tensorDimension :: InputOrOutput -> VType Builtin -> m Int
    tensorDimension io dim = do
      forcedDim <- forceValue dim
      case forcedDim of
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
          <+> squotes (prettyVerbose networkType)
          <+> "should have been caught during type-checking"
