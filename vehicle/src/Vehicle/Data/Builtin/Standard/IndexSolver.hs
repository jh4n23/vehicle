module Vehicle.Data.Builtin.Standard.IndexSolver
  ( solveIndexConstraint,
    solveDefaultIndexConstraints,
  )
where

import Control.Monad (forM)
import Control.Monad.Except (MonadError (..))
import Data.Maybe (mapMaybe)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Value (forceValue)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Type.Constraint.Core
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Meta (MetaSet)
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet
import Vehicle.Compile.Type.Monad.Class
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Type (TypableBuiltin)
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Generic (namedBoundCtxOf)
import Vehicle.Data.Variable.Bound.Context.Name (MonadReadableNameContext (getNameContext), runNameBoundContextT)

--------------------------------------------------------------------------------
-- Solve index constraints

solveIndexConstraint ::
  (MonadTypeChecker Builtin m, TypableBuiltin Builtin) =>
  WithContext (InstanceConstraint Builtin) ->
  m ()
solveIndexConstraint constraint = do
  let args = mapMaybe getExplicitArg $ goalSpine $ instanceGoal $ objectIn constraint
  progress <- runNameBoundContextT (namedBoundCtxOf $ contextOf constraint) $ solveInDomain args
  case progress of
    Success -> do
      let solution = Builtin mempty (BuiltinConstructor UnitLiteral)
      instantiateInstanceConstraintSolution constraint solution
    Failure blockingMetas
      | MetaSet.null blockingMetas -> malformedConstraintError constraint
      | otherwise -> do
          let blockedConstraint = blockConstraintOn constraint blockingMetas
          addAuxiliaryInstanceConstraints [blockedConstraint]

data IndexSolverResult = Success | Failure BlockingMetas

-- | Function signature for constraints solved by type class resolution.
-- This should eventually be refactored out so all are solved by instance
-- search.
solveInDomain ::
  forall m.
  (MonadTypeChecker Builtin m, MonadReadableNameContext m, TypableBuiltin Builtin) =>
  [VType Builtin] ->
  m IndexSolverResult
solveInDomain [value, domain] = do
  (forcedDomain, blockingMetas) <- forceValue domain
  case forcedDomain of
    (getExpr accessNatType -> Just ()) -> solveInNat value
    (getExpr accessTensorType -> Just args) -> solveInTensor args value
    (getExpr accessIndexType -> Just args) -> solveInIndex args value
    _ -> return $ Failure blockingMetas
solveInDomain _ = return $ Failure mempty

solveInNat :: Thunk builtin -> m IndexSolverResult
solveInNat _value = return Success

solveInTensor :: TensorTypeArgs (Thunk Builtin) -> Thunk Builtin -> m IndexSolverResult
solveInTensor (TensorTypeArgs tElem dims) _value = do
  (forcedElem, elemBlockingMetas) <- forceValue tElem
  (forcedDims, dimsBlockingMetas) <- forceValue dims
  case (forcedElem, forcedDims) of
    (IRatType, INil _) -> return Success
    (_, _) -> return $ Failure $ elemBlockingMetas <> dimsBlockingMetas

solveInIndex :: IndexTypeArgs (Thunk Builtin) -> Thunk Builtin -> m IndexSolverResult
solveInIndex (IndexTypeArgs size) value = do
  (forcedValue, valueBlockingMetas) <- forceValue value
  case forcedValue of
    INatLiteral n -> do
      (sizeBlockingMetas, sizeLowerBound) <- findLowerBound value size
      if n < sizeLowerBound
        then return Success
        else
          if not (MetaSet.null sizeBlockingMetas)
            then return $ Failure sizeBlockingMetas
            else do
              ctx <- getNameContext
              throwError $ TypingError $ FailedIndexConstraintTooBig ctx n sizeLowerBound
    _ -> return $ Failure valueBlockingMetas

findLowerBound ::
  forall m.
  (MonadTypeChecker Builtin m, MonadReadableNameContext m, TypableBuiltin Builtin) =>
  VType Builtin ->
  VType Builtin ->
  m (BlockingMetas, Int)
findLowerBound value indexSize = go indexSize
  where
    go :: VType Builtin -> m (MetaSet, Int)
    go size = do
      (forcedSize, blockingMetas) <- forceValue size
      case forcedSize of
        VMeta m _ ->
          return (MetaSet.singleton m, 0)
        INatLiteral n ->
          return (mempty, n)
        VFreeVar {} ->
          return (mempty, 0)
        VBuiltin (BuiltinFunction (Add AddNat)) [argExpr -> e1, argExpr -> e2] -> do
          (m1, b1) <- go e1
          (m2, b2) <- go e2
          return (m1 <> m2, b1 + b2)
        _ -> throwError $ TypingError $ FailedIndexConstraintUnknown ctx value indexSize

--------------------------------------------------------------------------------
-- Default index constraints

solveDefaultIndexConstraints ::
  (MonadTypeChecker Builtin m) =>
  [WithContext (InstanceConstraint Builtin)] ->
  m Bool
solveDefaultIndexConstraints defaultableConstraints = do
  results <- forM defaultableConstraints solveDefaultIndexConstraint
  return $ or results

solveDefaultIndexConstraint ::
  (MonadTypeChecker Builtin m) =>
  WithContext (InstanceConstraint Builtin) ->
  m Bool
solveDefaultIndexConstraint (WithContext constraint ctx) = do
  case instanceGoal constraint of
    (InstanceGoal [] (Right NatInDomainConstraint) [argExpr -> value, argExpr -> typ]) -> do
      (forcedType, _) <- runNameBoundContextT (namedBoundCtxOf ctx) $ forceValue typ
      case forcedType of
        IIndexType size -> do
          let succN = Forced $ mkExpr accessAddNat (Op2Args value (Forced $ INatLiteral 1))

          let constraintInfo = (ctx, instanceOrigin constraint)
          newSizeConstraint <- createInstanceUnification constraintInfo size succN
          addUnificationConstraints [newSizeConstraint]
          return True
        _ -> return False
    _ -> return False
