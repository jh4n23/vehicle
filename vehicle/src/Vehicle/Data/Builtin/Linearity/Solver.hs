module Vehicle.Data.Builtin.Linearity.Solver
  ( solveLinearityConstraint,
  )
where

import Data.Maybe (mapMaybe)
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Type.Constraint.Core
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Monad (MonadTypeChecker)
import Vehicle.Compile.Type.System
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Interface.Type (TypableBuiltin)
import Vehicle.Data.Builtin.Linearity
import Vehicle.Data.Code.Value
import Vehicle.Data.Variable.Bound.Context.Generic.Core (namedBoundCtxOf)
import Vehicle.Data.Variable.Bound.Context.Name (MonadReadableNameContext, extendClosureWithBound, runNameBoundContextT)

solveLinearityConstraint ::
  (MonadTypeChecker LinearityBuiltin m, TypableBuiltin LinearityBuiltin) =>
  WithContext (InstanceConstraint LinearityBuiltin) ->
  m ()
solveLinearityConstraint (WithContext normConstraint@(Resolve origin _ _ _ goal) ctx) = do
  (tc, spine) <- getTypeClass goal
  let nConstraint = WithContext normConstraint ctx
  progress <-
    runNameBoundContextT (namedBoundCtxOf ctx) $
      solve tc (ctx, origin) (mapMaybe getExplicitArg spine)
  let solution = VBuiltin (LinearityConstructor UnitLiteral) []
  handleAuxiliaryConstraintProgress solution nConstraint progress

--------------------------------------------------------------------------------
-- Constraint solving

pattern FLinearityExpr :: Linearity -> ForcedValue LinearityBuiltin
pattern FLinearityExpr l <- VBuiltin (Linearity l) []
  where
    FLinearityExpr l = VBuiltin (Linearity l) []

type MonadLinearitySolver m =
  ( MonadTypeChecker LinearityBuiltin m,
    MonadReadableNameContext m,
    TypableBuiltin LinearityBuiltin
  )

type LinearitySolver =
  forall m.
  (MonadLinearitySolver m) =>
  InstanceConstraintInfo LinearityBuiltin ->
  [VType LinearityBuiltin] ->
  m (AuxiliaryConstraintProgress LinearityBuiltin)

solve :: LinearityRelation -> LinearitySolver
solve = \case
  MaxLinearity -> solveOp2Linearity True True maxLinearityOp
  MulLinearity p -> solveOp2Linearity True True (mulLinearityOp p)
  DivLinearity p -> solveOp2Linearity False True (divLinearityOp p)
  PowLinearity p -> solveOp2Linearity False False (powLinearityOp p)
  FunctionLinearity position -> solveFunctionLinearity position
  QuantifierLinearity q -> solveQuantifierLinearity q

solveQuantifierLinearity :: Quantifier -> LinearitySolver
solveQuantifierLinearity _ info [fn, res] = do
  (forcedFn, blockingMetas) <- deepForceValue fn
  case forcedFn of
    VPi binder body -> do
      let (varName, p) = getNamedBinderInfo binder
      let domainLin = Forced $ FLinearityExpr $ Linear (QuantifiedVariableProvenance p varName)
      closedBody <- extendClosureWithBound binder body
      domEq <- createInstanceUnification info (Unforced $ typeOf binder) domainLin
      resEq <- createInstanceUnification info res closedBody
      return $ Progress [domEq, resEq] []
    _ -> return $ Stuck blockingMetas
solveQuantifierLinearity _ _ _ = developerError "Malformed QuantifierLinearity"

solveOp2Linearity ::
  Bool ->
  Bool ->
  (Linearity -> Linearity -> Linearity) ->
  LinearitySolver
solveOp2Linearity shortCircuitLHS shortCircuitRHS combine info [lin1, lin2, res] =
  do
    (flin1, blockingMetas1) <- deepForceValue lin1
    (flin2, blockingMetas2) <- deepForceValue lin2
    case (flin1, flin2) of
      (FLinearityExpr l1, FLinearityExpr l2) -> do
        let linRes = Forced $ FLinearityExpr (combine l1 l2)
        resEq <- createInstanceUnification info res linRes
        return $ Progress [resEq] []
      (FLinearityExpr Constant, _)
        | shortCircuitLHS -> do
            resEq <- createInstanceUnification info lin2 res
            return $ Progress [resEq] []
      (_, FLinearityExpr Constant)
        | shortCircuitRHS -> do
            resEq <- createInstanceUnification info lin1 res
            return $ Progress [resEq] []
      _ -> return $ Stuck $ blockingMetas1 <> blockingMetas2
solveOp2Linearity _ _ _ _ _ = developerError "Malformed Op2Linearity"

solveFunctionLinearity :: FunctionPosition -> LinearitySolver
solveFunctionLinearity functionPosition info@(ctx, _) [arg, res] = do
  (forcedArg, blockingMetas) <- deepForceValue arg
  case forcedArg of
    FLinearityExpr lin -> do
      let p = provenanceOf ctx
      let addFuncProv pp = LinFunctionProvenance p pp functionPosition
      let resLin = Forced $ FLinearityExpr $ mapLinearityProvenance addFuncProv lin
      resEq <- createInstanceUnification info res resLin
      return $ Progress [resEq] []
    _ -> return $ Stuck blockingMetas
solveFunctionLinearity _ _ _ = developerError "Malformed FunctionLinearity"

--------------------------------------------------------------------------------
-- Operations over linearities

maxLinearityOp :: Linearity -> Linearity -> Linearity
maxLinearityOp l1 l2 = case (l1, l2) of
  (Constant, _) -> l2
  (_, Constant) -> l1
  -- Note it's actually important that we return the left one here, as it ensures we print network output over network input.
  (Linear {}, Linear {}) -> l1
  (NonLinear {}, _) -> l1
  (_, NonLinear {}) -> l2

mulLinearityOp :: Provenance -> Linearity -> Linearity -> Linearity
mulLinearityOp p l1 l2 = case (l1, l2) of
  (Constant, _) -> l2
  (_, Constant) -> l1
  (Linear p1, Linear p2) -> NonLinear (LinearTimesLinear p p1 p2)
  (NonLinear {}, _) -> l1
  (_, NonLinear {}) -> l2

divLinearityOp :: Provenance -> Linearity -> Linearity -> Linearity
divLinearityOp p l1 l2 = case (l1, l2) of
  (_, Constant) -> l1
  (_, Linear p2) -> NonLinear (DivideByLinear p p2)
  (_, NonLinear {}) -> l2

powLinearityOp :: Provenance -> Linearity -> Linearity -> Linearity
powLinearityOp p l1 l2 = case (l1, l2) of
  (Constant, Constant) -> Constant
  (Linear p1, _) -> NonLinear (PowLinearBase p p1)
  (_, Linear p2) -> NonLinear (PowLinearExponent p p2)
  (NonLinear {}, _) -> l1
  (_, NonLinear {}) -> l2

--------------------------------------------------------------------------------
-- Other

getTypeClass :: (MonadCompile m) => InstanceGoal LinearityBuiltin -> m (LinearityRelation, Spine LinearityBuiltin)
getTypeClass = \case
  (InstanceGoal [] (Right (LinearityRelation tc)) args) -> return (tc, args)
  _ -> compilerDeveloperError "Unexpected non-type-class instance argument found."
