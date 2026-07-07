module Vehicle.Compile.Property
  ( traverseMultiProperty,
  )
where

import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.State (MonadTrans (..))
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.BuiltinForced (getDim, getDims)
import Vehicle.Compile.Normalise.NBEForced
import Vehicle.Compile.Normalise.TypedValueForced
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print.Warning ()
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.ForcedValue
import Vehicle.Data.Code.Interface
import Vehicle.Data.Tensor (TensorIndices, TensorShape, unstack)
import Vehicle.Data.Variable.Bound.Context.Name.Instance (runFreshNameBoundContextT)
import Vehicle.Data.Variable.Free.Context (MonadFreeContext)
import Vehicle.Verify.Core
import Vehicle.Verify.Specification

-- TODO move somewhere else more reusable?
traverseMultiProperty ::
  forall m a.
  (MonadFreeContext Builtin m) =>
  (PropertyAddress -> Thunk Builtin -> m a) ->
  Name ->
  Thunk Builtin ->
  Thunk Builtin ->
  m (Either MultiPropertyTraveralError (MultiProperty a))
traverseMultiProperty compileProp propertyName declType declBody =
  runExceptT (go declType mempty declBody)
  where
    go :: UnforcedType Builtin -> TensorIndices -> Thunk Builtin -> ExceptT MultiPropertyTraveralError m (MultiProperty a)
    go typ indices body = do
      forcedType <- runFreshNameBoundContextT $ forceThunk typ
      case forcedType of
        VVectorType elemType dimValue -> do
          maybeDim <- runFreshNameBoundContextT $ getDim dimValue
          case maybeDim of
            Nothing -> throwError $ UnsupportedVectorDimension dimValue
            Just dim -> goVector elemType dim indices body
        VTensorType _elemType dimsValue -> do
          maybeDims <- runFreshNameBoundContextT $ getDims dimsValue
          case maybeDims of
            Nothing -> throwError $ UnsupportedTensorDimensions dimsValue
            Just dims -> goTensor dims indices body
        _ -> throwError $ UnreducableType typ

    goVector :: UnforcedType Builtin -> Int -> TensorIndices -> Thunk Builtin -> ExceptT MultiPropertyTraveralError m (MultiProperty a)
    goVector typ _dim indices value = do
      forcedValue <- runFreshNameBoundContextT $ forceThunk value
      case toVectorValue forcedValue of
        -- TODO refactor in terms of a VectorValue class to `TypedValue` module
        VVectorLiteral args -> do
          let es' = zip [0 :: Int ..] $ vecLitElements args
          MultiProperty <$> traverse (\(i, e) -> go typ (i : indices) e) es'
        _ -> throwError $ UnsupportedVectorValue forcedValue

    goTensor :: TensorShape -> TensorIndices -> Thunk Builtin -> ExceptT MultiPropertyTraveralError m (MultiProperty a)
    goTensor dims indices value = case dims of
      [] -> do
        let address = PropertyAddress propertyName indices
        SingleProperty <$> lift (compileProp address value)
      _d : ds -> do
        forcedValue <- runFreshNameBoundContextT $ forceThunk value
        case toBoolTensorValue forcedValue of
          VBoolTensorLiteral bs -> do
            let es' = zip [0 :: Int ..] (Forced . IBoolTensorLiteral <$> unstack bs)
            MultiProperty <$> traverse (\(i, e) -> goTensor ds (i : indices) e) es'
          VBoolStackTensor args -> do
            let es' = zip [0 :: Int ..] $ stackElements args
            MultiProperty <$> traverse (\(i, e) -> goTensor ds (i : indices) e) es'
          _ -> throwError $ UnreducableTensorValue forcedValue
