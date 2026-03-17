module Vehicle.Data.Builtin.Standard.IndexSolver
  ( solveIndexConstraint,
    solveDefaultIndexConstraints,
  )
where

import Control.Monad (forM)
import Control.Monad.Except (MonadError (..))
import Data.Maybe (mapMaybe)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Prelude
import Vehicle.Compile.Type.Constraint.Core
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Meta (MetaSet)
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet
import Vehicle.Compile.Type.Monad.Class
import Vehicle.Compile.TypedView
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Type (TypableBuiltin)
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Generic (namedBoundCtxOf)
import Vehicle.Data.Variable.Bound.Context.Name (MonadReadableNameContext, runNameBoundContextT)

--------------------------------------------------------------------------------
-- Solve index constraints

solveIndexConstraint ::
  (MonadTypeChecker Builtin m, TypableBuiltin Builtin) =>
  WithContext (InstanceConstraint Builtin) ->
  m ()
solveIndexConstraint constraint = do
  let args = mapMaybe getExplicitArg $ goalSpine $ instanceGoal $ objectIn constraint
  progress <- runNameBoundContextT (namedBoundCtxOf $ contextOf constraint) $ solveInDomain constraint args
  case progress of
    Nothing -> do
      let solution = Builtin mempty (BuiltinConstructor UnitLiteral)
      instantiateInstanceConstraintSolution constraint solution
    Just metas -> do
      let blockedConstraint = blockConstraintOn constraint metas
      addAuxiliaryInstanceConstraints [blockedConstraint]

-- | Function signature for constraints solved by type class resolution.
-- This should eventually be refactored out so all are solved by instance
-- search.
solveInDomain ::
  forall m.
  (MonadTypeChecker Builtin m, MonadReadableNameContext m, TypableBuiltin Builtin) =>
  WithContext (InstanceConstraint Builtin) ->
  [VType Builtin] ->
  m (Maybe MetaSet)
solveInDomain c [value, domain] = do
  forcedDomain <- forceValue domain
  case forcedDomain of
    VMeta {} -> return $ blockOnMetas [forcedDomain]
    _ -> case toTypeValue forcedDomain of
      VNatType {} -> return Nothing
      VTensorType tElem dims -> do
        forcedElem <- forceValue tElem
        forcedDims <- forceValue dims
        case (forcedElem, forcedDims) of
          (IRatType, INil _) -> return Nothing
          (_, _) -> malformedConstraintError c
      VIndexType size -> do
        forcedValue <- forceValue value
        case forcedValue of
          VMeta {} -> return $ blockOnMetas [forcedValue]
          INatLiteral n -> do
            (sizeBlockingMetas, sizeLowerBound) <- findLowerBound ctx value size
            if n < sizeLowerBound
              then return Nothing
              else
                if not (MetaSet.null sizeBlockingMetas)
                  then return $ Just sizeBlockingMetas
                  else throwError $ TypingError $ FailedIndexConstraintTooBig ctx n sizeLowerBound
          _ -> malformedConstraintError c
      _ -> malformedConstraintError c
  where
    ctx = contextOf c
solveInDomain c _ = malformedConstraintError c

blockOnMetas :: [ForcedValue Builtin] -> Maybe MetaSet
blockOnMetas args = do
  let metas = mapMaybe getNMeta args
  if null metas
    then Nothing
    else Just (MetaSet.fromList metas)
  where
    getNMeta :: ForcedValue Builtin -> Maybe MetaID
    getNMeta = \case
      VMeta m _ -> Just m
      _ -> Nothing

findLowerBound ::
  forall m.
  (MonadTypeChecker Builtin m, MonadReadableNameContext m, TypableBuiltin Builtin) =>
  ConstraintContext Builtin ->
  VType Builtin ->
  VType Builtin ->
  m (MetaSet, Int)
findLowerBound ctx value indexSize = go indexSize
  where
    go :: VType Builtin -> m (MetaSet, Int)
    go size = do
      forcedSize <- forceValue size
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
      forcedType <- runNameBoundContextT (namedBoundCtxOf ctx) $ forceValue typ
      case forcedType of
        IIndexType size -> do
          let succN = Forced $ mkExpr accessAddNat (Op2Args value (Forced $ INatLiteral 1))

          let constraintInfo = (ctx, instanceOrigin constraint)
          newSizeConstraint <- createInstanceUnification constraintInfo size succN
          addUnificationConstraints [newSizeConstraint]
          return True
        _ -> return False
    _ -> return False
