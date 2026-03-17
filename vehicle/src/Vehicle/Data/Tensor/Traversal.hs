module Vehicle.Data.Tensor.Traversal where

import Control.Monad.Reader (MonadReader (..), Reader, ReaderT (..), asks, runReader)
import Data.Bifunctor (Bifunctor (..))
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (TensorIndices, TensorShape)

--------------------------------------------------------------------------------
-- PartiallyKnownTensorShape

-- | Represents the dimensions of a tensor where we know the leading dimensions
-- but the trailing dimensions are still unknown (i.e. depends on external
-- resources, see MNIST robustness specification for an example)
data PartiallyKnownTensorShape = PartiallyKnownTensorShape
  { knownPrefix :: TensorShape,
    unknownSuffix :: ForcedValue Builtin
  }

toPartialShape :: TensorShape -> PartiallyKnownTensorShape
toPartialShape knownDims =
  PartiallyKnownTensorShape
    { knownPrefix = knownDims,
      unknownSuffix = INil $ Forced INatType
    }

emptyPartialShape :: PartiallyKnownTensorShape
emptyPartialShape = toPartialShape []

--------------------------------------------------------------------------------
-- Tensor traversal

type MonadTraverseTensor m =
  (MonadReader (PartiallyKnownTensorShape, TensorIndices) m)

traverseTensorRows :: (MonadTraverseTensor m) => (a -> m b) -> [a] -> m [b]
traverseTensorRows f rows = do
  let fLocal (i, v) = local (second (i :)) (f v)
  traverse fLocal (zip [0 ..] rows)

currentIndices :: (MonadTraverseTensor m) => m TensorIndices
currentIndices = asks (reverse . snd)

runTraverseTensorT ::
  (Monad m) =>
  PartiallyKnownTensorShape ->
  ReaderT (PartiallyKnownTensorShape, TensorIndices) m a ->
  m a
runTraverseTensorT shape action = runReaderT action (shape, mempty)

runTraverseTensor :: PartiallyKnownTensorShape -> Reader (PartiallyKnownTensorShape, TensorIndices) a -> a
runTraverseTensor shape action = runReader action (shape, mempty)
