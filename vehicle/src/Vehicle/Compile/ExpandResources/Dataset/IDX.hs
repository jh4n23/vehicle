module Vehicle.Compile.ExpandResources.Dataset.IDX
  ( readIDX,
  )
where

import Control.Exception (try)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.IO.Class (MonadIO (..))
import Data.IDX
  ( IDXData,
    decodeIDXFile,
    idxDimensions,
    idxDoubleContent,
    idxIntContent,
    isIDXIntegral,
  )
import Data.Map qualified as Map
import Data.Vector.Generic qualified as V
import Data.Vector.Unboxed (Vector)
import Data.Vector.Unboxed qualified as Vector
import Vehicle.Compile.Error
import Vehicle.Compile.ExpandResources.Core
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.TypedView
import Vehicle.Data.Builtin.Interface.Normalise (forceDimsExprs)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Builtin.Standard.Normalise
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor as Tensor (Tensor, TensorShape, fromVector, mapTensor)

-- The current dimension in the dataset being parsed
type CurrentDimension = Int

-- | Reads the IDX dataset from the provided file, checking that the user type
-- matches the type of the stored data.
readIDX ::
  (MonadExpandResources m, MonadIO m) =>
  FilePath ->
  DeclProvenance ->
  Type Builtin ->
  m (Value Builtin)
readIDX file decl expectedType = do
  contents <- readIDXFile decl file
  case contents of
    Nothing -> throwError $ UnableToParseResource decl Dataset file
    Just idxData -> do
      let actualDimensions = Vector.toList $ idxDimensions idxData
      if isIDXIntegral idxData
        then do
          let elems = idxIntContent idxData
          let parser = intElemParser decl expectedType file
          let ctx = (decl, file, expectedType, actualDimensions, parser)
          parseIDX ctx elems
        else do
          let elems = idxDoubleContent idxData
          let parser = doubleElemParser decl expectedType file
          let ctx = (decl, file, expectedType, actualDimensions, parser)
          parseIDX ctx elems

readIDXFile ::
  (MonadCompile m, MonadIO m) =>
  DeclProvenance ->
  FilePath ->
  m (Maybe IDXData)
readIDXFile decl file = do
  result <- liftIO $ try (decodeIDXFile file)
  case result of
    Right idxData -> return idxData
    Left ioExcept -> do
      throwError $ ResourceIOError decl Dataset ioExcept

-- WARNING: There appears to be a pernicious bug with the
-- current version of the HLS (VSCode plugin v2.2.0, HLS v1.7.0)
-- where the below function causes the IDE to start spinning forever shortly
-- after changing things in this file. Can't currently find a workaround.
parseIDX ::
  (MonadExpandResources m, Vector.Unbox a) =>
  ParseContext m a ->
  Vector a ->
  m (Value Builtin)
parseIDX ctx@(_, _, expectedDatasetType, actualDatasetDims, _) elems =
  parseContainer ctx 0 actualDatasetDims elems (thunkifyExpr emptyBoundEnv expectedDatasetType)

parseContainer ::
  (MonadExpandResources m, Vector.Unbox a) =>
  ParseContext m a ->
  CurrentDimension ->
  TensorShape ->
  Vector a ->
  VType Builtin ->
  m (Value Builtin)
parseContainer ctx currentDim actualDims elems expectedType = do
  forcedExpectedType <- forceValue expectedType
  case toTypeValue forcedExpectedType of
    VListType expectedElemType -> parseList ctx currentDim expectedElemType actualDims elems
    VVectorType expectedElemType dim -> parseVector ctx currentDim expectedElemType dim actualDims elems
    VTensorType tElem expectedDims -> parseTensor ctx currentDim actualDims elems tElem expectedDims
    _
      | currentDim == 0 -> typingError ctx
      | otherwise -> parseElements ctx actualDims elems expectedType

parseTensor ::
  (MonadExpandResources m, Vector.Unbox a) =>
  ParseContext m a ->
  CurrentDimension ->
  TensorShape ->
  Vector a ->
  VType Builtin ->
  Value Builtin ->
  m (Value Builtin)
parseTensor ctx currentDim actualDims elems expectedElemType expectedDims = do
  checkTensorDimensions ctx currentDim expectedDims actualDims
  parseElements ctx actualDims elems expectedElemType

checkTensorDimensions ::
  (MonadExpandResources m) =>
  ParseContext m a ->
  CurrentDimension ->
  VType Builtin ->
  TensorShape ->
  m ()
checkTensorDimensions ctx dimNo expectedShape actualShape = do
  forcedExpectedShape <- forceValue expectedShape
  case (toDimensionsValue forcedExpectedShape, actualShape) of
    (VDimsNil, []) -> return ()
    (VDimsCons dim dims, d : ds) -> do
      checkDimension ctx dimNo dim d
      checkTensorDimensions ctx (dimNo + 1) dims ds
    _ -> dimensionMismatchError ctx

checkDimension ::
  (MonadExpandResources m) =>
  ParseContext m a ->
  CurrentDimension ->
  VType Builtin ->
  Int ->
  m ()
checkDimension ctx@(decl, file, _, _, _) currentDim expectedDimValue actualDim = do
  forcedExpectedDimValue <- forceValue expectedDimValue
  case toNatValue forcedExpectedDimValue of
    VNatLiteral expectedDim
      | expectedDim == actualDim -> return ()
      | otherwise -> do
          throwError $ DatasetDimensionSizeMismatch decl file expectedDim actualDim currentDim
    VNatParameter dimIdent -> do
      implicitParams <- getInferableParameterContext
      let newEntry = (decl, Dataset, actualDim)
      case Map.lookup dimIdent implicitParams of
        Nothing -> variableSizeError ctx expectedDimValue
        Just (p, declType, entry) -> case entry of
          Nothing -> addPossibleInferableParameterSolution dimIdent p declType newEntry
          Just existingEntry@(_, _, value)
            | value == actualDim -> return ()
            | otherwise -> throwError $ InferableParameterContradictory dimIdent existingEntry newEntry
    _ -> variableSizeError ctx expectedDimValue

parseList ::
  (MonadExpandResources m, Vector.Unbox a) =>
  ParseContext m a ->
  CurrentDimension ->
  VType Builtin ->
  TensorShape ->
  Vector a ->
  m (Value Builtin)
parseList ctx currentDim expectedElemType actualDims actualElems =
  case actualDims of
    [] -> dimensionMismatchError ctx
    d : ds -> do
      let splitElems = partitionData d ds actualElems
      exprs <- traverse (\es -> parseContainer ctx (currentDim + 1) ds es expectedElemType) splitElems
      return $ mkListExpr expectedElemType exprs

parseVector ::
  (MonadExpandResources m, Vector.Unbox a) =>
  ParseContext m a ->
  CurrentDimension ->
  VType Builtin ->
  Value Builtin ->
  TensorShape ->
  Vector a ->
  m (Value Builtin)
parseVector ctx currentDim expectedElemType expectedDim actualDims actualElems =
  case actualDims of
    [] -> dimensionMismatchError ctx
    d : ds -> do
      checkDimension ctx currentDim expectedDim d
      let splitElems = partitionData d ds actualElems
      exprs <- traverse (\es -> parseContainer ctx (currentDim + 1) ds es expectedElemType) splitElems
      return $ Forced $ IVecLiteral expectedElemType expectedDim exprs

parseElements ::
  (MonadExpandResources m, Vector.Unbox a) =>
  ParseContext m a ->
  TensorShape ->
  Vector a ->
  VType Builtin ->
  m (Value Builtin)
parseElements (_, _, _, _, elemParser) = elemParser

type ParseContext m a =
  ( DeclProvenance, -- The provenance of the dataset declaration
    FilePath, -- The path of the dataset
    Type Builtin, -- The overall dataset type
    TensorShape, -- Actual dimensions of dataset
    ElemParser m a
  )

type ElemParser m a = TensorShape -> Vector a -> VType Builtin -> m (Value Builtin)

doubleElemParser ::
  (MonadExpandResources m) =>
  DeclProvenance ->
  Type Builtin ->
  FilePath ->
  ElemParser m Double
doubleElemParser decl datasetType file dims values expectedElementType = do
  forcedExpectedElementType <- forceValue expectedElementType
  case toTypeValue forcedExpectedElementType of
    VRatType {} -> do
      return $ Forced $ IRatTensor (mapTensor toRational (toTensor dims values))
    _ -> do
      throwError $ DatasetTypeMismatch decl file datasetType expectedElementType "Rat"

intElemParser ::
  (MonadExpandResources m) =>
  DeclProvenance ->
  Type Builtin ->
  FilePath ->
  ElemParser m Int
intElemParser decl datasetType file dims values expectedElementType = do
  forcedExpectedElementType <- forceValue expectedElementType
  case toTypeValue forcedExpectedElementType of
    VIndexType dim -> do
      forcedExpectedDim <- forceValue dim
      case (forcedExpectedDim, dims, Vector.toList values) of
        (INatLiteral n, [], [value]) -> do
          if 0 <= value && value < n
            then return $ Forced $ IIndexLiteral value dim
            else throwError $ DatasetInvalidIndex decl file value n
        _ -> developerError "Should not be parsing tensors of indices"
    VNatType {} -> do
      let invalid = Vector.filter (< 0) values
      if Vector.null invalid
        then return $ Forced $ INatTensor (toTensor dims values)
        else throwError $ DatasetInvalidNat decl file (Vector.head invalid)
    _ ->
      throwError $ DatasetTypeMismatch decl file datasetType expectedElementType "Int"

-- | Split data by the first dimension of the C-Array.
partitionData :: (Vector.Unbox a) => Int -> TensorShape -> Vector a -> [Vector a]
partitionData dim dims content = do
  let entrySize = product dims
  i <- [0 .. dim - 1]
  return $ Vector.slice (i * entrySize) entrySize content

toTensor :: (Eq a, Vector.Unbox a) => TensorShape -> Vector a -> Tensor a
toTensor shape values = Tensor.fromVector shape (V.convert values)

variableSizeError :: (MonadCompile m) => ParseContext m a -> Value Builtin -> m b
variableSizeError (decl, _, expectedDatasetType, _, _) dim =
  throwError $ DatasetVariableSizeTensor decl expectedDatasetType dim

dimensionMismatchError :: forall m a b. (MonadExpandResources m) => ParseContext m a -> m b
dimensionMismatchError (decl, file, expectedDatasetType, actualDatasetDims, _) = do
  expectedDimensions <- dimensionsOf $ thunkifyExpr emptyBoundEnv expectedDatasetType
  throwError $ DatasetDimensionsMismatch decl file expectedDimensions actualDatasetDims
  where
    dimensionsOf :: VType Builtin -> m (Maybe Int)
    dimensionsOf typ = do
      forcedType <- forceValue typ
      case toTypeValue forcedType of
        VTensorType _ dims -> dimLength dims
        VListType tElem -> fmap (+ 1) <$> dimensionsOf tElem
        VVectorType tElem _dims -> fmap (+ 1) <$> dimensionsOf tElem
        _ -> return $ Just 0

    dimLength :: Value Builtin -> m (Maybe Int)
    dimLength dimsValue = do
      maybeForcedDims <- forceDimsExprs dimsValue
      return $ case maybeForcedDims of
        Left {} -> Nothing
        Right dims -> Just $ length dims

typingError :: (MonadCompile m) => ParseContext m a -> m b
typingError (_, _, expectedDatasetType, _, _) =
  compilerDeveloperError $
    "Invalid dataset type"
      <+> squotes (prettyVerbose expectedDatasetType)
      <+> "should have been caught during type-checking"
