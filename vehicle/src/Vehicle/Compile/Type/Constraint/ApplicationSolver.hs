{- HLINT ignore "Use fewer imports" -}
module Vehicle.Compile.Type.Constraint.ApplicationSolver
  ( runApplicationSolver,
    solveArgInsertionProblem,
  )
where

import Control.Monad.Except (MonadError (..))
import Data.Data (Proxy (..))
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Quote (unnormalise)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Meta (MetaSet)
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.Monad.Class
import Vehicle.Compile.Type.System
import Vehicle.Data.Code.Value (Closure, ForcedValue (..), VBinder, VType, Value (..), boundContextToEnv, extendClosure, thunkifyExpr)
import Vehicle.Data.Variable.Bound.Context.Generic
import Vehicle.Data.Variable.Bound.Context.Name (NamedBoundCtx)
import Prelude hiding (pi)

-------------------------------------------------------------------------------
-- Solver

-- | Attempts to solve as many type-class constraints as possible.
runApplicationSolver :: (TCM builtin m) => CheckExprTypeFn builtin m -> Proxy builtin -> m ()
runApplicationSolver checkExprType proxy = do
  logCompilerSection2 MaxDetail "application solver run" $
    runConstraintSolver
      getActiveApplicationConstraints
      setApplicationConstraints
      (solveApplicationConstraint checkExprType)
      True
      proxy

solveApplicationConstraint ::
  (TCM builtin m) =>
  CheckExprTypeFn builtin m ->
  WithContext (ApplicationConstraint builtin) ->
  m ()
solveApplicationConstraint checkExprType (WithContext InferArgs {..} ctx) = do
  let boundCtx = boundContextOf ctx
  result <- solveArgInsertionProblem checkExprType boundCtx argInsertionProblem
  case result of
    Right (finalExpr, normFinalType) -> do
      let finalType = unnormalise (boundCtxLv boundCtx) normFinalType
      solveMeta exprSolution finalExpr boundCtx
      solveMeta typeSolution finalType boundCtx
    Left (blockedProblem, blockingMetas) -> do
      let newConstraint = InferArgs {argInsertionProblem = blockedProblem, ..}
      let finalConstraint = WithContext newConstraint (blockCtxOn blockingMetas ctx)
      addApplicationConstraint finalConstraint

-------------------------------------------------------------------------------
-- Arg insertion problem

type ArgInsertionProblemSolution builtin =
  Either (ArgInsertionProblem builtin, MetaSet) (Expr builtin, VType builtin)

-- Can't import this directly from `Bidirectional` due to cyclic dependencies.
type CheckExprTypeFn builtin m =
  (TCM builtin m) =>
  BoundCtx (Type builtin) ->
  Relevance ->
  Type builtin ->
  Expr builtin ->
  m (Expr builtin)

-- | Deals with insertion of missing implicits and instance arguments
solveArgInsertionProblem ::
  (TCM builtin m) =>
  CheckExprTypeFn builtin m ->
  BoundCtx (Type builtin) ->
  ArgInsertionProblem builtin ->
  m (ArgInsertionProblemSolution builtin)
solveArgInsertionProblem checkExprType ctx problem@ArgInsertionProblem {..} = do
  (forcedExpectedType, blockingMetas) <- deepForceValue currentExpectedType
  -- First see if the unnormalised type is correct.
  case forcedExpectedType of
    -- If a standard Pi type then proceed to check against it (need to do this first before we check if args
    -- are null, as it may be a non-explicit binder for which we do need to insert arguments even if the user
    -- hasn't provided any)
    VPi binder resultType
      | isExplicit binder && null uncheckedArgs ->
          argInsertionProblemSolved problem
      | otherwise -> do
          newProblem <- checkArgsAgainstPiType checkExprType ctx problem binder resultType
          solveArgInsertionProblem checkExprType ctx newProblem

    -- Otherwise if we are blocked on metas then we can postpone the problem until these metas are solved
    _
      | not (MetaSet.null blockingMetas) -> do
          let newProblem = ArgInsertionProblem {currentExpectedType = Forced forcedExpectedType, ..}
          return $ Left (newProblem, blockingMetas)
      -- Otherwise we're truely stuck and we error.
      | otherwise -> do
          let boundCtx = toNamedBoundCtx ctx
          throwError $
            TypingError $
              FunctionTypeMismatch $
                FunctionTypeMismatchError
                  { _ctx = boundCtx,
                    originalFunction = originalFun,
                    currentExpectedType = currentExpectedType,
                    currentUncheckedArgs = uncheckedArgs
                  }

checkArgsAgainstPiType ::
  (TCM builtin m) =>
  CheckExprTypeFn builtin m ->
  BoundCtx (Type builtin) ->
  ArgInsertionProblem builtin ->
  VBinder builtin ->
  Closure builtin ->
  m (ArgInsertionProblem builtin)
checkArgsAgainstPiType checkExprType ctx problem@ArgInsertionProblem {..} normBinder closure = do
  let nameCtx = toNamedBoundCtx ctx
  showAppEnter nameCtx problem
  let binder = unnormalise (boundCtxLv ctx) normBinder

  -- Determine whether we have an arg that matches the binder
  let visibility = visibilityOf binder
  (matchedUncheckedArg, remainingUncheckedArgs) <- case uncheckedArgs of
    [] -> return (Nothing, uncheckedArgs)
    (arg : remainingArgs)
      | visibilityOf arg == visibility -> return (Just arg, remainingArgs)
      | isExplicit binder ->
          throwError $
            TypingError $
              MissingExplicitArg $
                MissingExplicitArgError
                  { _ctx = toNamedBoundCtx ctx,
                    explicitBinder = binder,
                    nonExplicitArg = arg
                  }
      | otherwise -> return (Nothing, uncheckedArgs)

  -- Calculate what the new checked arg should be, create a fresh meta
  -- if no arg was matched above
  let p = provenanceOf originalFun
  checkedArg <- case matchedUncheckedArg of
    Just arg -> do
      logDebug MaxDetail $ "matching-arg-found" <+> prettyVerbose arg
      let relevance = relevanceOf binder
      let ctxRelevance = if contextRelevance == Irrelevant then Irrelevant else relevance
      checkedArgExpr <- checkExprType ctx ctxRelevance (typeOf binder) (argExpr arg)
      return $ Arg (visibilityOf arg) relevance checkedArgExpr
    Nothing -> do
      logDebug MaxDetail "no-matching-arg-found"
      let original = (originalFun, originalArgs, originalFunType)
      instantiateArgForNonExplicitBinder ctx p original binder

  let newCheckedArgs = checkedArg : checkedArgs
  let argValue = thunkifyExpr (boundContextToEnv ctx) $ argExpr checkedArg
  let newExpectedType = extendClosure closure normBinder argValue
  let newProblem =
        problem
          { checkedArgs = newCheckedArgs,
            currentExpectedType = newExpectedType,
            uncheckedArgs = remainingUncheckedArgs
          }

  showAppExit nameCtx newProblem

  return newProblem

argInsertionProblemSolved ::
  (MonadTypeChecker builtin m) =>
  ArgInsertionProblem builtin ->
  m (ArgInsertionProblemSolution builtin)
argInsertionProblemSolved problem@ArgInsertionProblem {..} =
  return $ Right (solutionSoFar problem, currentExpectedType)

instantiateArgForNonExplicitBinder ::
  (TCM builtin m) =>
  BoundCtx (Type builtin) ->
  Provenance ->
  (Expr builtin, [Arg builtin], Type builtin) ->
  Binder builtin ->
  m (Arg builtin)
instantiateArgForNonExplicitBinder boundCtx p (fun, funArgs, funType) binder = do
  let binderType = typeOf binder
  checkedExpr <- case visibilityOf binder of
    Explicit {} -> compilerDeveloperError "Should not be instantiating Arg for explicit Binder"
    Implicit {} -> freshMetaExpr p binderType boundCtx
    Instance {} -> do
      let origin =
            InstanceArgOrigin $
              ArgOrigin
                { checkedInstanceOp = fun,
                  checkedInstanceOpArgs = funArgs,
                  checkedInstanceOpType = funType,
                  checkedInstanceType = binderType
                }
      createFreshInstanceConstraint (isAuxiliaryConstraint binderType) boundCtx (provenanceOf fun) origin (relevanceOf binder) binderType
  return $ Arg (markInserted $ visibilityOf binder) (relevanceOf binder) checkedExpr

showAppEnter :: (TCM builtin m) => NamedBoundCtx -> ArgInsertionProblem builtin -> m ()
showAppEnter ctx problem@ArgInsertionProblem {..} = do
  logDebugM MaxDetail $ do
    let checkedExprDoc = prettyExternal (WithContext (solutionSoFar problem) ctx)
    let uncheckedArgsDoc = prettyExternal (WithContext uncheckedArgs ctx)
    return $ "checking-args-enter" <+> checkedExprDoc <+> "@" <+> uncheckedArgsDoc
  incrCallDepth
  logDebug MaxDetail $
    "expected-type:" <+> prettyExternal (WithContext currentExpectedType ctx)

showAppExit :: (TCM builtin m) => NamedBoundCtx -> ArgInsertionProblem builtin -> m ()
showAppExit ctx problem@ArgInsertionProblem {..} = do
  logDebug MaxDetail $
    "new-expected-type:" <+> prettyExternal (WithContext currentExpectedType ctx)
  decrCallDepth
  logDebug MaxDetail $ do
    let newCheckedExprDoc = prettyExternal (WithContext (solutionSoFar problem) ctx)
    let newUncheckedArgsDoc = prettyExternal (WithContext uncheckedArgs ctx)
    "checking-args-exit" <+> newCheckedExprDoc <+> "@" <+> newUncheckedArgsDoc
