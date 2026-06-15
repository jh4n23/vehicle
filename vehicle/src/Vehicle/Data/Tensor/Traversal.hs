module Vehicle.Data.Tensor.Traversal where

import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks)
import Data.Maybe (fromMaybe)
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (TensorIndices, TensorShape)

--------------------------------------------------------------------------------
-- PartiallyKnownTensorShape

-- | We may not be able to calculate the exact dimensions a tensor, but this
-- value represents the prefix that of the shape that is known, e.g.
-- [1,2,n] would have a prefix of [1,2]
type KnownPrefixOfTensorShape = TensorShape

-- | Represents the dimensions of a tensor where we know the leading dimensions
-- but the trailing dimensions are still unknown (i.e. depends on external
-- resources, see MNIST robustness specification for an example)
data PartiallyKnownTensorShape = PartiallyKnownTensorShape
  { knownPrefix :: KnownPrefixOfTensorShape,
    unknownSuffix :: Value Builtin
  }

toPartialShape :: TensorShape -> Maybe (Value Builtin) -> PartiallyKnownTensorShape
toPartialShape knownDims maybeUnknownDims =
  PartiallyKnownTensorShape
    { knownPrefix = knownDims,
      unknownSuffix = fromMaybe IDimNil maybeUnknownDims
    }

--------------------------------------------------------------------------------
-- Tensor traversal

type MonadTraverseTensor m = MonadReader TensorIndices m

traverseTensorRows :: (MonadTraverseTensor m) => (a -> m b) -> [a] -> m [b]
traverseTensorRows f rows = do
  let fLocal (i, v) = local (i :) (f v)
  traverse fLocal (zip [0 ..] rows)

currentIndices :: (MonadTraverseTensor m) => m TensorIndices
currentIndices = asks reverse

runTraverseTensorT ::
  (Monad m) =>
  ReaderT TensorIndices m a ->
  m a
runTraverseTensorT action = runReaderT action mempty
