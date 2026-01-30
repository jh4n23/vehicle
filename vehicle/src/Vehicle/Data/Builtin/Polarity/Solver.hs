module Vehicle.Data.Builtin.Polarity.Solver
  ( solvePolarityConstraint,
  )
where

import Control.Monad.Except (MonadError (..))
import Data.Maybe (mapMaybe)
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Compile.Type.Constraint.Core
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Force
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.System
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Interface.Type
import Vehicle.Data.Builtin.Polarity
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Generic

solvePolarityConstraint ::
  (MonadPolaritySolver m) =>
  WithContext (InstanceConstraint PolarityBuiltin) ->
  m ()
solvePolarityConstraint constraintWithCtx = do
  normConstraintWithCtx@(WithContext normConstraint@(Resolve origin _ _ _ goal) ctx) <- substMetaVariables constraintWithCtx
  logDebugM MaxDetail $ do
    let forcedExpr = goalExpr $ instanceGoal $ objectIn normConstraintWithCtx
    let boundCtx = namedBoundCtxOf $ contextOf normConstraintWithCtx
    return $ "forced goal:" <+> prettyFriendly (WithContext forcedExpr boundCtx)

  (tc, spine) <- getTypeClass goal
  let maybeProgress = solve tc (ctx, origin) (mapMaybe getExplicitArg spine)
  let nConstraint = WithContext normConstraint ctx
  case maybeProgress of
    Nothing -> malformedConstraintError nConstraint
    Just progress -> do
      let solution = VBuiltin (PolarityConstructor UnitLiteral) []
      handleAuxiliaryConstraintProgress solution nConstraint =<< progress

--------------------------------------------------------------------------------
-- Constraint solving

pattern FPolarityExpr :: Polarity -> ForcedExpr PolarityBuiltin
pattern FPolarityExpr l <- FBuiltin _ (Polarity l) []

type MonadPolaritySolver m =
  ( MonadTypeChecker PolarityBuiltin m,
    TypableBuiltin PolarityBuiltin
  )

type PolaritySolver =
  forall m.
  (MonadPolaritySolver m) =>
  InstanceConstraintInfo PolarityBuiltin ->
  [Type PolarityBuiltin] ->
  Maybe (m (AuxiliaryConstraintProgress PolarityBuiltin))

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
solveNegPolarity info@(ctx, _) [arg, res] = Just $ do
  (forcedArg, blockingMetas) <- forceHead (namedBoundCtxOf ctx) arg
  case forcedArg of
    FPolarityExpr pol -> do
      let resPol = Builtin mempty $ Polarity $ negatePolarity (provenanceOf ctx) pol
      resEq <- createInstanceUnification info res resPol
      return $ Progress [resEq] []
    _ -> return $ Stuck blockingMetas
solveNegPolarity _ _ = Nothing

solveQuantifierPolarity :: Quantifier -> PolaritySolver
solveQuantifierPolarity q info@(ctx, _) [fn, res] = Just $ do
  (forcedFn, blockingMetas) <- forceHead (namedBoundCtxOf ctx) fn
  case forcedFn of
    FPi _ binder resPol -> do
      let (_, p) = getNamedBinderInfo binder
      binderEq <- createInstanceUnification info (typeOf binder) (Builtin mempty $ Polarity Unquantified)
      let tc = PolarityRelation $ AddPolarity p q
      (_, addConstraint) <- createDerivedInstanceConstraint info Irrelevant (normAppList (Builtin mempty tc) (explicit <$> [resPol, res]))
      return $ Progress [binderEq] [addConstraint]
    _ -> return $ Stuck blockingMetas
solveQuantifierPolarity _ _c _ = Nothing

solveAddPolarityOp :: Provenance -> Quantifier -> PolaritySolver
solveAddPolarityOp p q info@(ctx, _) [arg, res] = Just $ do
  (forcedArg, blockingMetas) <- forceHead (namedBoundCtxOf ctx) arg
  case forcedArg of
    FPolarityExpr inputPol -> do
      let resPol = Builtin mempty $ Polarity $ addPolarityOp p q inputPol
      domEq <- createInstanceUnification info res resPol
      return $ Progress [domEq] []
    _ -> return $ Stuck blockingMetas
solveAddPolarityOp _ _ _ _ = Nothing

solveMaxPolarityOp :: PolaritySolver
solveMaxPolarityOp info@(ctx, _) [arg1, arg2, res] = Just $ do
  (forcedArg1, blockingMetas1) <- forceHead (namedBoundCtxOf ctx) arg1
  (forcedArg2, blockingMetas2) <- forceHead (namedBoundCtxOf ctx) arg2
  case (forcedArg1, forcedArg2) of
    (FPolarityExpr pol1, FPolarityExpr pol2) -> do
      let pol3 = Builtin mempty $ Polarity $ maxPolarityOp pol1 pol2
      resEq <- createInstanceUnification info res pol3
      return $ Progress [resEq] []
    (_, FPolarityExpr Unquantified) -> do
      resEq <- createInstanceUnification info arg1 res
      return $ Progress [resEq] []
    (FPolarityExpr Unquantified, _) -> do
      resEq <- createInstanceUnification info arg2 res
      return $ Progress [resEq] []
    _ -> return $ Stuck $ blockingMetas1 <> blockingMetas2
solveMaxPolarityOp _ _ = Nothing

solveImplPolarity :: PolaritySolver
solveImplPolarity info@(ctx, _) [arg1, arg2, res] = Just $ do
  (forcedArg1, blockingMetas1) <- forceHead (namedBoundCtxOf ctx) arg1
  (forcedArg2, blockingMetas2) <- forceHead (namedBoundCtxOf ctx) arg2
  case (forcedArg1, forcedArg2) of
    (FPolarityExpr pol1, FPolarityExpr pol2) -> do
      let pol3 = Builtin mempty $ Polarity $ implPolarityOp (provenanceOf ctx) pol1 pol2
      resEq <- createInstanceUnification info res pol3
      return $ Progress [resEq] []
    _ -> return $ Stuck $ blockingMetas1 <> blockingMetas2
solveImplPolarity _ _ = Nothing

solveFunctionPolarity :: FunctionPosition -> PolaritySolver
solveFunctionPolarity functionPosition info@(ctx, _) [arg, res] = Just $ do
  (forcedArg, blockingMetas1) <- forceHead (namedBoundCtxOf ctx) arg
  (forcedRes, blockingMetas2) <- forceHead (namedBoundCtxOf ctx) res
  case (forcedArg, forcedRes) of
    (FPolarityExpr pol, _) -> do
      let p = provenanceOf ctx
      let addFuncProv pp = PolFunctionProvenance p pp functionPosition
      let pol3 = Builtin mempty $ Polarity $ mapPolarityProvenance addFuncProv pol
      resEq <- createInstanceUnification info res pol3
      return $ Progress [resEq] []
    (FPi _ binder1 body1, FPi _ binder2 body2) -> do
      let tc = PolarityRelation $ FunctionPolarity functionPosition
      (_, binderConstraint) <- createDerivedInstanceConstraint info Irrelevant (normAppList (Builtin mempty tc) (explicit <$> [typeOf binder1, typeOf binder2]))
      (_, bodyConstraint) <- createDerivedInstanceConstraint info Irrelevant (normAppList (Builtin mempty tc) (explicit <$> [body1, body2]))
      return $ Progress [] [binderConstraint, bodyConstraint]
    _ -> return $ Stuck $ blockingMetas1 <> blockingMetas2
solveFunctionPolarity _ _ _ = Nothing

solveIfCondPolarity :: PolaritySolver
solveIfCondPolarity info@(ctx, _) [pCond, pArg1, pArg2, pRes] = Just $ do
  (forcedCondition, blockingMetas) <- forceHead (namedBoundCtxOf ctx) pCond
  case forcedCondition of
    FPolarityExpr pol -> case pol of
      Unquantified -> solveMaxPolarityOp info [pArg1, pArg2, pRes]
      _ -> throwError $ QuantifiedIfCondition ctx
    _ -> return $ Stuck blockingMetas
solveIfCondPolarity _ _ = Nothing

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

getTypeClass :: (MonadCompile m) => InstanceGoal PolarityBuiltin -> m (PolarityRelation, Args PolarityBuiltin)
getTypeClass = \case
  (InstanceGoal _ (Right (PolarityRelation tc)) args) -> return (tc, args)
  _ -> compilerDeveloperError "Unexpected non-type-class instance argument found."
