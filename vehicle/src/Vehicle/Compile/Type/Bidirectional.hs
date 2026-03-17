module Vehicle.Compile.Type.Bidirectional
  ( checkExprType,
    checkTelescope,
    checkRecordDefinition,
    inferExprType,
    createFreshUnificationConstraint,
  )
where

import Control.Monad.Except (MonadError (..))
import Control.Monad.Reader (MonadReader (..), ReaderT (..))
import Data.Data (Proxy (..))
import Data.List.NonEmpty qualified as NonEmpty (toList)
import Data.Maybe (fromMaybe)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Quote
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Type.Constraint.ApplicationSolver
import Vehicle.Compile.Type.Constraint.UnificationSolver (solveUnificationConstraint)
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.Monad.Class (createFreshConstraintCtx, getRecordDefinition)
import Vehicle.Compile.Type.System (HasTypeSystem (..), TCM)
import Vehicle.Data.Builtin.Interface.Type (TypableBuiltin (..))
import Vehicle.Data.Code.Value (Thunk (..), Value (..), boundContextToEnv, thunkifyExpr)
import Vehicle.Data.Universe (UniverseLevel (..))
import Vehicle.Data.Variable.Bound.Context.Generic
import Vehicle.Data.Variable.Bound.Context.Name (MonadReadableNameContext (..))
import Vehicle.Data.Variable.Free.Context
import Prelude hiding (pi)

--------------------------------------------------------------------------------
-- Bidirectional type-checking

-- Recurses through the expression, switching between check and infer modes.
-- Inserts meta-variables for missing implicit and instance arguments and
-- gathers the constraints over those meta-variables.

-- | Type checking monad with additional bound context for the bidirectional
-- type-checking pass.
type MonadBidirectional builtin m =
  ( TCM builtin m,
    MonadBoundContext (Type builtin) m,
    MonadReader Relevance m
  )

runMonadBidirectional ::
  forall m builtin a.
  (MonadTypeChecker builtin m) =>
  BoundCtx (Type builtin) ->
  Relevance ->
  BoundContextT (Type builtin) (ReaderT Relevance m) a ->
  m a
runMonadBidirectional ctx relevance x =
  runReaderT (runBoundContextT ctx x) relevance

--------------------------------------------------------------------------------
-- Checking

-- | Checks that the given expression is of the provided type while
-- generating the necessary constraints along the way, returning a well-typed
-- version of the expression with the necessary implicit and instance arguments
-- inserted.
checkExprType ::
  (TCM builtin m) =>
  BoundCtx (Type builtin) ->
  Relevance ->
  Type builtin ->
  Expr builtin ->
  m (Expr builtin)
checkExprType boundCtx relevance expectedType expr = do
  runMonadBidirectional boundCtx relevance $ checkExpr expectedType expr

-- | Checks that the given expression is of the provided type while
-- generating the necessary constraints along the way, returning a well-typed
-- version of the expression with the necessary implicit and instance arguments
-- inserted.
checkExpr ::
  forall builtin m.
  (MonadBidirectional builtin m) =>
  Type builtin ->
  Expr builtin ->
  m (Expr builtin)
checkExpr expectedType expr = do
  showCheckEntry expectedType expr
  res <- case (expectedType, expr) of
    -- In the case where we have a matching pi binder and lam binder use the pi-binder to
    -- aid inference of lambda binder.
    (Pi _ piBinder resultType, Lam p lamBinder body)
      | visibilityOf piBinder == visibilityOf lamBinder -> do
          -- Check the lambda binder
          checkedLamBinder <- checkBinder lamBinder

          -- Check that the lambda and pi binders have the same type.
          checkPiBinderMatchesLamBinder piBinder checkedLamBinder

          let finalLamBinder = setBinderRelevance checkedLamBinder (relevanceOf piBinder)

          -- Add bound variable to context and check if the type of the expression
          -- matches the expected result type.
          checkedBody <- addBinderToContext finalLamBinder $ checkExpr resultType body

          return $ Lam p finalLamBinder checkedBody

    -- In the case where we have an implicit or instance pi binder then insert a new
    -- lambda expression.
    (Pi p piBinder resultType, e)
      | isImplicit piBinder || isInstance piBinder -> do
          logDebug MaxDetail $ "inserting-binder" <+> prettyVerbose piBinder

          -- Create a suitable binder
          lamBinderName <- getBinderNameOrFreshName (nameOf piBinder) (typeOf piBinder)
          let lamBinderForm = BinderDisplayForm (OnlyName lamBinderName mempty) False
          let lamBinder =
                piBinder
                  { binderDisplayForm = lamBinderForm
                  }

          -- Re-check the expression
          checkedExpr <- addBinderToContext lamBinder $ checkExpr resultType (liftDBIndices 1 e)

          return $ Lam p lamBinder checkedExpr

    -- Otherwise switch to inference mode
    (_, _) -> viaInfer expectedType expr

  showCheckExit res
  return res

viaInfer ::
  (MonadBidirectional builtin m) =>
  Type builtin ->
  Expr builtin ->
  m (Expr builtin)
viaInfer expectedType expr = do
  let p = provenanceOf expr
  -- Switch to inference mode
  (checkedExpr, actualType) <- inferExpr expr
  -- Insert any needed implicit or instance arguments
  (appliedCheckedExpr, resultType) <- inferApp checkedExpr actualType []
  -- Check the expected and the actual types are equal
  checkExprTypesEqual p expr expectedType resultType
  return appliedCheckedExpr

checkBinder ::
  (MonadBidirectional builtin m) =>
  Binder builtin ->
  m (Binder builtin)
checkBinder binder = do
  let p = provenanceOf binder
  checkedBinderType <- checkExpr (TypeUniverse p 0) (typeOf binder)
  let checkedBinder = replaceBinderType checkedBinderType binder
  return checkedBinder

checkTelescope ::
  (MonadBidirectional builtin m) =>
  Telescope builtin ->
  m a ->
  m (Telescope builtin, a)
checkTelescope telescope checkBody = case telescope of
  [] -> ([],) <$> checkBody
  binder : binders -> do
    checkedBinder <- checkBinder binder
    (checkedBinders, checkedFields) <-
      addBinderToContext checkedBinder $
        checkTelescope binders checkBody
    return (checkedBinder : checkedBinders, checkedFields)

--------------------------------------------------------------------------------
-- Inference

inferExprType ::
  (TCM builtin m) =>
  BoundCtx (Type builtin) ->
  Relevance ->
  Expr builtin ->
  m (Expr builtin, Type builtin)
inferExprType boundCtx relevance expr = do
  runMonadBidirectional boundCtx relevance $ inferExpr expr

-- | Takes in an unchecked expression and attempts to infer it's type.
-- Returns the expression annotated with its type as well as the type itself.
inferExpr ::
  forall builtin m.
  (MonadBidirectional builtin m) =>
  Expr builtin ->
  m (Expr builtin, Type builtin)
inferExpr e = do
  showInferEntry e
  res <- case e of
    -- TODO fix once we have a universe solver up and running.
    Universe p (UniverseLevel l) -> return (e, TypeUniverse p l)
    Meta _ m -> do
      metaType <- getMetaType m
      return (e, metaType)
    Hole p _name -> do
      -- Replace the hole with meta-variable.
      -- NOTE, different uses of the same hole name will be interpreted
      -- as different meta-variables.
      boundCtx <- getBoundCtx (Proxy @(Type builtin))
      metaType <- freshMetaExpr p (TypeUniverse p 0) boundCtx
      metaExpr <- freshMetaExpr p metaType boundCtx
      return (metaExpr, metaType)
    Pi p binder body -> do
      checkedBinder <- checkBinder binder
      checkedBody <- addBinderToContext checkedBinder $ checkExpr (TypeUniverse p 0) body
      return (Pi p checkedBinder checkedBody, TypeUniverse p 0)
    App fun args -> do
      (checkedFun, checkedFunType) <- inferExpr fun
      inferApp checkedFun checkedFunType (NonEmpty.toList args)
    BoundVar p i -> do
      ctx <- getBoundCtx (Proxy @(Type builtin))
      let binder = lookupIxInBoundCtx i ctx
      currentRelevance <- getCurrentRelevance (Proxy @builtin)
      if currentRelevance == Relevant && relevanceOf binder == Irrelevant
        then do
          let varName = fromMaybe "<unknown>" $ nameOf binder
          throwError $ TypingError $ RelevantUseOfIrrelevantVariable $ RelevantUseOfIrrelevantVariableError (Proxy @builtin) p varName
        else do
          let liftedCheckedType = liftDBIndices (Lv $ unIx i + 1) (typeOf binder)
          return (BoundVar p i, liftedCheckedType)
    FreeVar p ident -> do
      originalFunType <- getDeclType (Proxy @builtin) ident
      return (FreeVar p ident, originalFunType)
    Let p boundExpr binder body -> do
      checkedBinder <- checkBinder binder

      -- Check the type of the body, with the bound variable added to the context.
      (checkedBody, typeOfBody) <-
        addBinderToContext checkedBinder $ inferExpr body

      -- Check that the expression being bound is correct.
      let typeOfBoundExpr = typeOf checkedBinder
      checkedBoundExpr <- checkExpr typeOfBoundExpr boundExpr
      -- Substitute through the type of the bound expression to preserve well-typedness
      let finalType = typeOfBoundExpr `substDBInto` typeOfBody
      return (Let p checkedBoundExpr checkedBinder checkedBody, finalType)
    Lam p binder body -> do
      checkedBinder <- checkBinder binder
      (checkedBody, typeOfBody) <- addBinderToContext checkedBinder $ inferExpr body
      return (Lam p checkedBinder checkedBody, Pi p checkedBinder typeOfBody)
    Builtin p op -> do
      typ <- typeBuiltin p op
      return (Builtin p op, typ)
    Record p uncheckedRecordType uncheckedFields -> do
      (checkedRecordType, expectedFieldTypes) <- checkRecordTypeAndCalculateRecordFieldTypes p uncheckedRecordType
      checkedFields <- traverse (checkRecordField expectedFieldTypes) uncheckedFields
      return (Record p checkedRecordType checkedFields, checkedRecordType)
    RecordProj p uncheckedRecordType uncheckedRecord field -> do
      (checkedRecordType, expectedFieldTypes) <- checkRecordTypeAndCalculateRecordFieldTypes p uncheckedRecordType
      checkedRecord <- checkExpr checkedRecordType uncheckedRecord
      let fieldType = lookupRecordField expectedFieldTypes field
      return (RecordProj p checkedRecordType checkedRecord field, fieldType)

  showInferExit res
  return res

checkRecordTypeAndCalculateRecordFieldTypes ::
  forall builtin m.
  (MonadBidirectional builtin m) =>
  Provenance ->
  Type builtin ->
  m (Type builtin, RecordFields builtin)
checkRecordTypeAndCalculateRecordFieldTypes p uncheckedRecordType = do
  checkedRecordType <- checkExpr (Universe p 0) uncheckedRecordType

  (recordIdent, recordParameters) <- case checkedRecordType of
    App (FreeVar _ ident) args -> return (ident, NonEmpty.toList args)
    FreeVar _ ident -> return (ident, [])
    _ ->
      developerError $
        "Ill-formed record type found during type-checking:"
          <> lineIndent (prettyVerbose checkedRecordType)

  (telescope, fields) <- getRecordDefinition (Proxy @builtin) recordIdent
  let substField fieldType = calculateRarameterisedRecordFieldType telescope fieldType recordParameters
  let finalFields = mapRecordFields substField fields

  return (checkedRecordType, finalFields)

checkRecordDefinition ::
  forall builtin m.
  (MonadTypeChecker builtin m, HasTypeSystem builtin) =>
  Telescope builtin ->
  RecordFields builtin ->
  m (Telescope builtin, RecordFields builtin)
checkRecordDefinition t f =
  runMonadBidirectional @m @builtin emptyBoundCtx Relevant $ checkRecordFieldsDef f t

checkRecordFieldsDef ::
  forall builtin m.
  (MonadBidirectional builtin m) =>
  RecordFields builtin ->
  Telescope builtin ->
  m (Telescope builtin, RecordFields builtin)
checkRecordFieldsDef fields = \case
  [] -> do
    checkedFields <- traverseRecordFields (checkExpr (Universe mempty 0)) fields
    return ([], checkedFields)
  binder : binders -> do
    checkedBinder <- checkBinder binder
    (checkedBinders, checkedFields) <-
      addBinderToContext checkedBinder $ checkRecordFieldsDef fields binders
    return (checkedBinder : checkedBinders, checkedFields)

-- | Takes a function and its arguments, inserts any needed implicits
-- or instance arguments and then returns the function applied to the full
-- list of arguments as well as the result type.
inferApp ::
  forall builtin m.
  (MonadBidirectional builtin m) =>
  Expr builtin ->
  Type builtin ->
  [Arg builtin] ->
  m (Expr builtin, Type builtin)
inferApp fun funType args = do
  relevance <- getCurrentRelevance (Proxy @builtin)
  ctx <- getBoundCtx (Proxy @(Type builtin))
  let normFunType = Unforced $ Thunk (boundContextToEnv ctx) funType
  let insertionProblem =
        ArgInsertionProblem
          { originalFun = fun,
            originalArgs = args,
            originalFunType = funType,
            checkedArgs = mempty,
            uncheckedArgs = args,
            currentExpectedType = normFunType,
            contextRelevance = relevance
          }

  -- Try solving the problem immediately
  result <- solveArgInsertionProblem checkExprType ctx insertionProblem
  case result of
    -- If succeeds then great
    Right (resultExpr, normResultType) -> do
      let resultType = unnormalise (boundCtxLv ctx) normResultType
      return (resultExpr, resultType)
    -- Otherwise add the blocked problem as a constraint
    Left (problem, blockingMetas) ->
      createFreshApplicationConstraint ctx problem blockingMetas

-------------------------------------------------------------------------------
-- Utility functions

checkExprTypesEqual ::
  forall builtin m.
  (MonadBidirectional builtin m) =>
  Provenance ->
  Expr builtin ->
  Type builtin ->
  Type builtin ->
  m ()
checkExprTypesEqual p expr expectedType actualType = do
  ctx <- getBoundCtx (Proxy @(Type builtin))
  let origin =
        CheckingExprType $
          CheckingExpr
            { checkedExpr = Right expr,
              checkedExprExpectedType = expectedType,
              checkedExprActualType = actualType
            }
  createFreshUnificationConstraint p ctx origin expectedType actualType

checkPiBinderMatchesLamBinder ::
  forall builtin m.
  (MonadBidirectional builtin m) =>
  Binder builtin ->
  Binder builtin ->
  m ()
checkPiBinderMatchesLamBinder piBinder lamBinder = do
  ctx <- getBoundCtx (Proxy @(Type builtin))
  let expectedType = typeOf piBinder
  let actualType = typeOf lamBinder
  let origin =
        CheckingExprType $
          CheckingExpr
            { checkedExpr = Left (nameOf lamBinder),
              checkedExprExpectedType = expectedType,
              checkedExprActualType = actualType
            }
  createFreshUnificationConstraint (provenanceOf lamBinder) ctx origin expectedType actualType

checkRecordField ::
  (MonadBidirectional builtin m) =>
  GenericRecordFields (Type builtin) ->
  RecordField builtin ->
  m (RecordField builtin)
checkRecordField declaredFields (field, value) = do
  let fieldType = lookupRecordField declaredFields field
  checkedValue <- checkExpr fieldType value
  return (field, checkedValue)

-- | Adds an entirely new unification constraint (as opposed to one
-- derived from another constraint).
createFreshUnificationConstraint ::
  forall builtin m.
  (MonadTypeChecker builtin m, TypableBuiltin builtin) =>
  Provenance ->
  BoundCtx (Type builtin) ->
  UnificationConstraintOrigin builtin ->
  Type builtin ->
  Type builtin ->
  m ()
createFreshUnificationConstraint p ctx origin expectedType actualType = do
  let env = boundContextToEnv ctx
  context <- createFreshConstraintCtx p ctx
  let unification = Unify origin (thunkifyExpr env expectedType) (thunkifyExpr env actualType)
  solveUnificationConstraint (WithContext unification context)

getCurrentRelevance :: (MonadBidirectional builtin m) => Proxy builtin -> m Relevance
getCurrentRelevance _ = ask

--------------------------------------------------------------------------------
-- Debug functions

showCheckEntry :: forall builtin m. (MonadBidirectional builtin m) => Type builtin -> Expr builtin -> m ()
showCheckEntry t e = do
  ctx <- getNameContext
  logDebug MaxDetail $ "check-entry" <+> prettyExternal (WithContext e ctx) <+> ":" <+> prettyExternal (WithContext t ctx)
  incrCallDepth

showCheckExit :: forall builtin m. (MonadBidirectional builtin m) => Expr builtin -> m ()
showCheckExit e = do
  decrCallDepth
  ctx <- getNameContext
  logDebug MaxDetail $ "check-exit " <+> prettyExternal (WithContext e ctx)

showInferEntry :: forall builtin m. (MonadBidirectional builtin m) => Expr builtin -> m ()
showInferEntry e = do
  ctx <- getNameContext
  logDebug MaxDetail $ "infer-entry" <+> prettyExternal (WithContext e ctx)
  incrCallDepth

showInferExit :: forall builtin m. (MonadBidirectional builtin m) => (Expr builtin, Type builtin) -> m ()
showInferExit (e, t) = do
  decrCallDepth
  ctx <- getNameContext
  -- logDebug MaxDetail $ "infer-exit " <+> prettyVerbose e <+> ":" <+> prettyVerbose t <+> pretty (length ctx)
  logDebug MaxDetail $ "infer-exit " <+> prettyExternal (WithContext e ctx) <+> ":" <+> prettyExternal (WithContext t ctx)
