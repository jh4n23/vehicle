module Vehicle.Compile.Property
  ( traverseMultiProperty,
  )
where

import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.State (MonadTrans (..))
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.NBE (forceValue)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print.Warning ()
import Vehicle.Compile.TypedView
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Builtin.Interface.Normalise (forceDim, forceDims)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (TensorIndices, TensorShape, unstack)
import Vehicle.Data.Variable.Bound.Context.Name (runFreshNameBoundContextT)
import Vehicle.Data.Variable.Free.Context (MonadFreeContext)
import Vehicle.Verify.Core
import Vehicle.Verify.Specification

-- TODO move somewhere else more reusable?
traverseMultiProperty ::
  forall m a.
  (MonadFreeContext Builtin m) =>
  (PropertyAddress -> Value Builtin -> m a) ->
  PropertyID ->
  Name ->
  Value Builtin ->
  Value Builtin ->
  m (Either MultiPropertyTraveralError (MultiProperty a))
traverseMultiProperty compileProp propertyID propertyName declType declBody = runExceptT (go declType mempty declBody)
  where
    go :: VType Builtin -> TensorIndices -> Value Builtin -> ExceptT MultiPropertyTraveralError m (MultiProperty a)
    go typ indices body = do
      forcedType <- runFreshNameBoundContextT $ forceValue typ
      case toTypeValue forcedType of
        VVectorType elemType dimValue -> do
          maybeDim <- runFreshNameBoundContextT $ forceDim dimValue
          case maybeDim of
            Nothing -> throwError $ UnsupportedVectorDimension dimValue
            Just dim -> goVector elemType dim indices body
        VTensorType _ dimsValue -> do
          maybeDims <- runFreshNameBoundContextT $ forceDims dimsValue
          case maybeDims of
            Nothing -> throwError $ UnsupportedTensorDimensions dimsValue
            Just dims -> goTensor dims indices body
        _ -> throwError $ UnreducableType typ

    goVector :: VType Builtin -> Int -> TensorIndices -> Value Builtin -> ExceptT MultiPropertyTraveralError m (MultiProperty a)
    goVector typ _dim indices value = do
      forcedValue <- runFreshNameBoundContextT $ forceValue value
      case forcedValue of
        -- TODO refactor in terms of a VectorValue class to `TypedValue` module
        (getExpr accessVecLit -> Just args) -> do
          let es' = zip [0 :: Int ..] $ vecLitElements args
          MultiProperty <$> traverse (\(i, e) -> go typ (i : indices) e) es'
        _ -> throwError $ UnsupportedVectorValue value

    goTensor :: TensorShape -> TensorIndices -> Value Builtin -> ExceptT MultiPropertyTraveralError m (MultiProperty a)
    goTensor dims indices value = case dims of
      [] -> do
        let address = PropertyAddress propertyID propertyName indices
        SingleProperty <$> lift (compileProp address value)
      _d : ds -> do
        forcedValue <- runFreshNameBoundContextT $ forceValue value
        case toBoolTensorValue forcedValue of
          VBoolTensorLiteral bs -> do
            let es' = zip [0 :: Int ..] (fromBoolTensorValue . VBoolTensorLiteral <$> unstack bs)
            MultiProperty <$> traverse (\(i, e) -> goTensor ds (i : indices) e) es'
          VBoolStackTensor args -> do
            let es' = zip [0 :: Int ..] $ stackElements args
            MultiProperty <$> traverse (\(i, e) -> goTensor ds (i : indices) e) es'
          _ -> throwError $ UnreducableTensorValue value
