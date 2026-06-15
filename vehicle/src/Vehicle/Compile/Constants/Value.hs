{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Compile.Constants.Value where

import Control.Monad.Identity (Identity (..))
import Vehicle.Data.Assertion
import Vehicle.Data.Builtin.Interface.Normalise
import Vehicle.Data.Builtin.Loss
import Vehicle.Data.Code.BooleanExpr
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.LinearExpr
import Vehicle.Data.Code.TypedView (etaReduceTensor)
import Vehicle.Data.Code.Value
import Vehicle.Data.Real
import Vehicle.Data.Tensor
import Vehicle.Data.Variable.Bound.Level
import Vehicle.Prelude
import Vehicle.Prelude.Logging

--------------------------------------------------------------------------------
-- Tensors of values

type HasRatTensors builtin =
  ( HasRatExpr Value Value builtin,
    HasRatType Value Value builtin,
    HasTensorLiterals Value builtin
  )

type TensorValueLinearExpr builtin = LinearExpr SliceVariable (DimensionedTensorValue builtin)

type UserVariableConstraint builtin = Assertion (TensorValueLinearExpr builtin)

-- | An `AssertionTree` represents a boolean expression with assertions at
-- each terminal leaf.
type UserVariableConstraintTree = BooleanExpr (UserVariableConstraint LossBuiltin)

constantDimensionedValue :: (HasRatTensors builtin) => VDims builtin -> ExtendedRational -> DimensionedTensorValue builtin
constantDimensionedValue dims constant =
  TensorValue dims $
    runSilentLogger $
      evalConstTensor $
        ConstTensorArgs
          { constType = IRatType,
            constValue = IRatLiteral constant,
            constDims = dims
          }

addDimensionedValue ::
  (HasRatTensors builtin) =>
  DimensionedTensorValue builtin ->
  DimensionedTensorValue builtin ->
  DimensionedTensorValue builtin
addDimensionedValue (TensorValue dims1 e1) (TensorValue _dims2 e2) = do
  TensorValue dims1 $
    runSilentLogger $
      evalAddRatTensor $
        TensorOp2Args dims1 e1 e2

scaleDimensionedValue ::
  (HasRatTensors builtin) =>
  Coefficient ->
  DimensionedTensorValue builtin ->
  DimensionedTensorValue builtin
scaleDimensionedValue c (TensorValue dims e) = do
  let constant = tensorValue $ constantDimensionedValue dims (Finite c)
  let e' = runSilentLogger $ evalMulRatTensor $ TensorOp2Args dims constant e
  TensorValue dims e'

addDimensionedConstants ::
  (HasRatTensors builtin) =>
  Coefficient ->
  Coefficient ->
  DimensionedTensorValue builtin ->
  DimensionedTensorValue builtin ->
  DimensionedTensorValue builtin
addDimensionedConstants c1 c2 v1 v2 = do
  let cv1 = scaleDimensionedValue c1 v1
  let cv2 = scaleDimensionedValue c2 v2
  addDimensionedValue cv1 cv2

dimensionedValueToRatTensor ::
  (HasRatTensors builtin) =>
  DimensionedTensorValue builtin ->
  Maybe RatTensor
dimensionedValueToRatTensor (TensorValue _ e1) = case e1 of
  IRatTensor (toFiniteRatTensor -> Just t) -> Just t
  _ -> Nothing

minTensorValues ::
  (HasRatTensors builtin) =>
  DimensionedTensorValue builtin ->
  DimensionedTensorValue builtin ->
  DimensionedTensorValue builtin
minTensorValues (TensorValue dims v1) (TensorValue _ v2) =
  TensorValue dims $
    runSilentLogger $
      evalMinRatTensor $
        TensorOp2Args
          { tensorOp2Dims = dims,
            tensorOp2Arg1 = v1,
            tensorOp2Arg2 = v2
          }

maxTensorValues ::
  (HasRatTensors builtin) =>
  DimensionedTensorValue builtin ->
  DimensionedTensorValue builtin ->
  DimensionedTensorValue builtin
maxTensorValues (TensorValue dims v1) (TensorValue _ v2) =
  TensorValue dims $
    runSilentLogger $
      evalMaxRatTensor $
        TensorOp2Args
          { tensorOp2Dims = dims,
            tensorOp2Arg1 = v1,
            tensorOp2Arg2 = v2
          }

stackTensorValues :: (HasRatTensors builtin) => [DimensionedTensorValue builtin] -> DimensionedTensorValue builtin
stackTensorValues = \case
  [] -> developerError "Cannot stack zero tensors"
  elements@(TensorValue dims _ : _) -> do
    let newDim = INatLiteral (length elements)
    let newDims = IDimCons newDim dims
    TensorValue newDims $
      runSilentLogger $
        evalStackTensor $
          StackTensorArgs
            { stackType = IRatType,
              stackFirstDim = newDim,
              stackRemainingDims = dims,
              stackElements = fmap tensorValue elements
            }

unstackTensorValues :: (HasRatTensors builtin) => DimensionedTensorValue builtin -> [DimensionedTensorValue builtin]
unstackTensorValues (TensorValue dims value) = case dims of
  IDimCons (INatLiteral d) ds -> do
    let values = runSilentLogger $ etaReduceTensor IRatType d ds value
    fmap (TensorValue ds) values
  _ -> developerError "Cannot unstack tensor with unknown dimensions"

instance (HasRatTensors builtin, Monad m) => ConstantLike (DimensionedTensorValue builtin) m where
  addConstants a b xs ys = return $ addDimensionedConstants a b xs ys
  scaleConstant a xs = return $ scaleDimensionedValue a xs
  toRatTensor x = return $ dimensionedValueToRatTensor x
  minConstants xs ys = return $ minTensorValues xs ys
  maxConstants xs ys = return $ maxTensorValues xs ys
  stackConstants xss = return $ stackTensorValues xss
  unstackConstants xs = return $ unstackTensorValues xs

tensorLinearExprToExpr :: (HasRatTensors builtin) => VDims builtin -> TensorValueLinearExpr builtin -> Value builtin
tensorLinearExprToExpr dims linexp = tensorValue $ runIdentity $ linearExprToExpr id fromVar addParts linexp
  where
    fromVar (v, c) = return $ scaleDimensionedValue c (TensorValue dims (VBoundVar (toLv v) []))
    addParts x y = return $ addDimensionedValue x y
