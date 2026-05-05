module Vehicle.Data.Builtin.Polarity.Solver
  ( solvePolarityConstraint,
  )
where

import Control.Monad.Except (MonadError (..))
import Data.Maybe (mapMaybe)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Value (forceValue)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Compile.Type.Constraint.Core
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.System
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Interface.Type
import Vehicle.Data.Builtin.Polarity
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Generic
import Vehicle.Data.Variable.Bound.Context.Name (MonadReadableNameContext, extendClosureWithBound, runNameBoundContextT)

solvePolarityConstraint ::
  (MonadTypeChecker PolarityBuiltin m, TypableBuiltin PolarityBuiltin) =>
  WithContext (InstanceConstraint PolarityBuiltin) ->
  m ()
solvePolarityConstraint (WithContext constraint@(Resolve origin _ _ _ goal) ctx) = do
  logDebugM MaxDetail $ do
    let forcedExpr = forcedGoalValue $ instanceGoal constraint
    let boundCtx = namedBoundCtxOf ctx
    return $ "forced goal:" <+> prettyFriendly (WithContext forcedExpr boundCtx)

  (tc, spine) <- getTypeClass goal
  progress <-
    runNameBoundContextT (namedBoundCtxOf ctx) $
      solve tc (ctx, origin) (mapMaybe getExplicitArg spine)
  let solution = VBuiltin (PolarityConstructor UnitLiteral) []
  handleAuxiliaryConstraintProgress solution (WithContext constraint ctx) progress

--------------------------------------------------------------------------------
-- Constraint solving

pattern FPolarityExpr :: Polarity -> Value PolarityBuiltin
pattern FPolarityExpr l <- VBuiltin (Polarity l) []
  where
    FPolarityExpr l = VBuiltin (Polarity l) []

type MonadPolaritySolver m =
  ( MonadTypeChecker PolarityBuiltin m,
    TypableBuiltin PolarityBuiltin,
    MonadReadableNameContext m
  )

type PolaritySolver =
  forall m.
  (MonadPolaritySolver m) =>
  InstanceConstraintInfo PolarityBuiltin ->
  [Thunk PolarityBuiltin] ->
  m (AuxiliaryConstraintProgress PolarityBuiltin)

solve :: PolarityRelation -> PolaritySolver
solve = \case
  NegPolarity -> solveNegPolarity
  QuantifierPolarity q -> solveQuantifierPolarity q
  AddPolarity p q -> solveAddPolarityOp p q
  ImpliesPolarity -> solveImplPolarity
  MaxPolarity -> solveMaxPolarityOp
  FunctionPolarity position -> solveFunctionPolarity position
  IfPolarity -> solveIfCondPolarity

solveNegPolarity :: PolaritySolver
solveNegPolarity info@(ctx, _) [inputPol, outputPol] = do
  (forcedArg, blockingMetas) <- forceValue inputPol
  case forcedArg of
    FPolarityExpr pol -> do
      let resPol = Forced $ FPolarityExpr $ negatePolarity (provenanceOf ctx) pol
      resEq <- createInstanceUnification info outputPol resPol
      return $ Progress [resEq] []
    _ -> return $ Stuck blockingMetas
solveNegPolarity _ _ = developerError "Malformed NegPolarity"

solveQuantifierPolarity :: Quantifier -> PolaritySolver
solveQuantifierPolarity q info [fn, res] = do
  (forcedFn, blockingMetas) <- forceValue fn
  case forcedFn of
    VPi binder resPol -> do
      let (_, p) = getNamedBinderInfo binder
      let unquantifiedPol = Forced $ FPolarityExpr Unquantified
      closedResPol <- extendClosureWithBound binder resPol
      binderEq <- createInstanceUnification info (typeOf binder) unquantifiedPol
      addConstraint <- createDerivedPolarityInstanceConstraint info (AddPolarity p q) [closedResPol, res]
      return $ Progress [binderEq] [addConstraint]
    _ -> return $ Stuck blockingMetas
solveQuantifierPolarity _ _ _ = developerError "Malformed QuantifierPolarity"

solveAddPolarityOp :: Provenance -> Quantifier -> PolaritySolver
solveAddPolarityOp p q info [arg, res] = do
  (forcedArg, blockingMetas) <- forceValue arg
  case forcedArg of
    FPolarityExpr inputPol -> do
      let resPol = Forced $ FPolarityExpr $ addPolarityOp p q inputPol
      domEq <- createInstanceUnification info res resPol
      return $ Progress [domEq] []
    _ -> return $ Stuck blockingMetas
solveAddPolarityOp _ _ _ _ = developerError "Malformed AddPolarity"

solveMaxPolarityOp :: PolaritySolver
solveMaxPolarityOp info [arg1, arg2, res] = do
  (forcedArg1, blockingMetas1) <- forceValue arg1
  (forcedArg2, blockingMetas2) <- forceValue arg2
  case (forcedArg1, forcedArg2) of
    (FPolarityExpr pol1, FPolarityExpr pol2) -> do
      let pol3 = Forced $ FPolarityExpr $ maxPolarityOp pol1 pol2
      resEq <- createInstanceUnification info res pol3
      return $ Progress [resEq] []
    (_, FPolarityExpr Unquantified) -> do
      resEq <- createInstanceUnification info arg1 res
      return $ Progress [resEq] []
    (FPolarityExpr Unquantified, _) -> do
      resEq <- createInstanceUnification info arg2 res
      return $ Progress [resEq] []
    _ -> return $ Stuck $ blockingMetas1 <> blockingMetas2
solveMaxPolarityOp _ _ = developerError "Malformed MaxPolarity"

solveImplPolarity :: PolaritySolver
solveImplPolarity info@(ctx, _) [arg1, arg2, res] = do
  (forcedArg1, blockingMetas1) <- forceValue arg1
  (forcedArg2, blockingMetas2) <- forceValue arg2
  case (forcedArg1, forcedArg2) of
    (FPolarityExpr pol1, FPolarityExpr pol2) -> do
      let pol3 = Forced $ FPolarityExpr $ implPolarityOp (provenanceOf ctx) pol1 pol2
      resEq <- createInstanceUnification info res pol3
      return $ Progress [resEq] []
    _ -> return $ Stuck $ blockingMetas1 <> blockingMetas2
solveImplPolarity _ _ = developerError "Malformed ImplPolarity"

solveFunctionPolarity :: FunctionPosition -> PolaritySolver
solveFunctionPolarity functionPosition info@(ctx, _) [arg, res] = do
  (forcedArg, blockingMetas1) <- forceValue arg
  (forcedRes, blockingMetas2) <- forceValue res
  case (forcedArg, forcedRes) of
    (FPolarityExpr pol, _) -> do
      let addFuncProv pp = PolFunctionProvenance (provenanceOf ctx) pp functionPosition
      let pol3 = Forced $ FPolarityExpr $ mapPolarityProvenance addFuncProv pol
      resEq <- createInstanceUnification info res pol3
      return $ Progress [resEq] []
    (VPi binder1 body1, VPi binder2 body2) -> do
      let tc = FunctionPolarity functionPosition
      binderConstraint <- createDerivedPolarityInstanceConstraint info tc [typeOf binder1, typeOf binder2]
      closedBody1 <- extendClosureWithBound binder1 body1
      closedBody2 <- extendClosureWithBound binder2 body2
      bodyConstraint <- createDerivedPolarityInstanceConstraint info tc [closedBody1, closedBody2]
      return $ Progress [] [binderConstraint, bodyConstraint]
    _ -> return $ Stuck $ blockingMetas1 <> blockingMetas2
solveFunctionPolarity _ _ _ = developerError "Malformed FunctionPolarity"

solveIfCondPolarity :: PolaritySolver
solveIfCondPolarity info@(ctx, _) [pCond, pArg1, pArg2, pRes] = do
  (forcedCondition, blockingMetas) <- forceValue pCond
  case forcedCondition of
    FPolarityExpr pol -> case pol of
      Unquantified -> solveMaxPolarityOp info [pArg1, pArg2, pRes]
      _ -> throwError $ QuantifiedIfCondition ctx
    _ -> return $ Stuck blockingMetas
solveIfCondPolarity _ _ = developerError "Malformed IfCondPolarity"

--------------------------------------------------------------------------------
-- Operations over polarities

negPolarityOp ::
  (PolarityProvenance -> PolarityProvenance) ->
  Polarity ->
  Polarity
negPolarityOp modProv pol =
  case pol of
    Unquantified -> Unquantified
    Quantified q pp -> Quantified (neg q) (modProv pp)
    MixedParallel pp1 pp2 -> MixedParallel (modProv pp2) (modProv pp1)
    -- We don't negate a mixed sequential polarity as its the top of the polarity
    -- lattice and we want to give as meaningful and localised error messages
    -- as possible.
    MixedSequential {} -> pol

negatePolarity ::
  Provenance ->
  Polarity ->
  Polarity
negatePolarity p = negPolarityOp (NegateProvenance p)

addPolarityOp :: Provenance -> Quantifier -> Polarity -> Polarity
addPolarityOp p q pol = case pol of
  Unquantified -> Quantified q (QuantifierProvenance p)
  Quantified q' pp -> if q == q' then pol else MixedSequential q p pp
  MixedParallel pp1 pp2 -> MixedSequential q p (if q == Forall then pp2 else pp1)
  MixedSequential {} -> pol

maxPolarityOp :: Polarity -> Polarity -> Polarity
maxPolarityOp pol1 pol2 = case (pol1, pol2) of
  (Unquantified, _) -> pol2
  (_, Unquantified) -> pol1
  (Quantified q1 pp1, Quantified q2 pp2)
    | q1 == q2 -> pol1
    | q1 == Forall -> MixedParallel pp1 pp2
    | otherwise -> MixedParallel pp2 pp1
  (Quantified {}, MixedParallel {}) -> pol2
  (MixedParallel {}, Quantified {}) -> pol1
  (MixedParallel {}, MixedParallel {}) -> pol1
  (MixedSequential {}, _) -> pol1
  (_, MixedSequential {}) -> pol2

implPolarityOp ::
  Provenance ->
  Polarity ->
  Polarity ->
  Polarity
implPolarityOp p pol1 pol2 =
  let negPol = negPolarityOp (LHSImpliesProvenance p)
   in -- `a => b` = not a or b
      maxPolarityOp (negPol pol1) pol2

--------------------------------------------------------------------------------
-- Other

createDerivedPolarityInstanceConstraint ::
  (MonadPolaritySolver m) =>
  (ConstraintContext PolarityBuiltin, InstanceConstraintOrigin PolarityBuiltin) ->
  PolarityRelation ->
  [Thunk PolarityBuiltin] ->
  m (WithContext (InstanceConstraint PolarityBuiltin))
createDerivedPolarityInstanceConstraint info rel args = do
  let instanceType = Forced $ VBuiltin (PolarityRelation rel) (explicit <$> args)
  res <- createDerivedInstanceConstraint info Irrelevant instanceType
  return $ snd res

getTypeClass :: (MonadCompile m) => InstanceGoal PolarityBuiltin -> m (PolarityRelation, Spine PolarityBuiltin)
getTypeClass = \case
  (InstanceGoal _ (Right (PolarityRelation tc)) args) -> return (tc, args)
  _ -> compilerDeveloperError "Unexpected non-type-class instance argument found."
