module Vehicle.Compile.Print.Error.Typing
  ( typingErrorDetails,
    prettyIdentName,
    unsupportedAnnotationTypeDescription,
  )
where

import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Monoid (Endo (..))
import Data.Text (Text, pack)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Core
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Type.Core
import Vehicle.Data.Builtin.Core (BuiltinType (..))
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Builtin.Interface.Type (TypableBuiltin (..), isCoercionExpr)
import Vehicle.Data.DSL
import Vehicle.Data.Variable.Bound.Context.Generic
import Prelude hiding (pi)

typingErrorDetails ::
  forall builtin.
  (TypableBuiltin builtin) =>
  TypingError builtin ->
  VehicleError
typingErrorDetails = \case
  MissingExplicitArg err -> missingExplicitArgError err
  FunctionTypeMismatch err -> functionTypeMismatchError err
  FailedUnificationConstraints err -> failedUnificationConstraintsError err
  FailedInstanceConstraint err -> failedInstanceConstraintError err
  RelevantUseOfIrrelevantVariable err -> relevantUseOfIrrelevantVariableError err
  FailedIndexConstraintTooBig ctx v n ->
    VehicleError
      { provenance = Just $ provenanceOf ctx,
        problem =
          "the value"
            <+> squotes (pretty v)
            <+> "is too big to"
            <+> "be used as an index of size"
            <+> squotes (pretty n)
            <> ".",
        fix = Nothing
      }
  FailedIndexConstraintUnknown ctx v t ->
    VehicleError
      { provenance = Just $ provenanceOf ctx,
        problem =
          "unable to determine if"
            <+> squotes (prettyFriendly (WithContext v (namedBoundCtxOf ctx)))
            <+> "is a valid index of size"
            <+> squotes (prettyFriendly (WithContext t (namedBoundCtxOf ctx)))
            <> ".",
        fix = Nothing
      }
  UnsolvedConstraints cs ->
    VehicleError
      { provenance = Just $ provenanceOf ctx,
        problem = constraintOriginMessage,
        fix = Just "try adding more type annotations"
      }
    where
      WithContext constraint ctx = NonEmpty.head cs
      nameCtx = namedBoundCtxOf ctx

      constraintOriginMessage = case constraint of
        UnificationConstraint (Unify origin _ _) -> case origin of
          CheckingExprType CheckingExpr {..} ->
            "expected"
              <+> ( case checkedExpr of
                      Left binder -> "variable" <+> quotePretty binder
                      Right expr -> squotes (prettyUnificationConstraintOriginExpr ctx expr)
                  )
              <+> "to be of type"
              <+> squotes (prettyFriendly $ WithContext checkedExprExpectedType nameCtx)
              <+> "but was unable to prove it."
          CheckingInstanceType instanceOrigin ->
            instanceOriginConstraintMessage instanceOrigin
        InstanceConstraint (Resolve instanceOrigin _ _ _ _) -> instanceOriginConstraintMessage instanceOrigin
        -- AuxiliaryConstraint (Auxiliary auxiliaryOrigin _ _) -> auxiliaryOriginConstraintMessage auxiliaryOrigin
        ApplicationConstraint {} ->
          "unsolved application constraint: " <+> prettyFriendly (WithContext constraint ctx)

      instanceOriginConstraintMessage = \case
        InstanceArgOrigin ArgOrigin {..} ->
          "insufficient information to find a valid type for the overloaded expression"
            <+> squotes (prettyTypeClassConstraintOriginExpr ctx checkedInstanceOp checkedInstanceOpArgs)
        InstanceTypeRestrictionOrigin {} -> developerError "Unexpected type-restriction error"
  UnsolvedMetas _ ms ->
    VehicleError
      { provenance = Just p,
        problem = "Unable to infer type of bound variable",
        fix = Just "add more type annotations"
      }
    where
      (_, p) = NonEmpty.head ms
  InvalidInstanceHead (ident, p) expr ->
    VehicleError
      { provenance = Just p,
        problem =
          "Cannot add"
            <+> prettyIdentName ident
            <+> "as an instance"
            <+> "as"
            <+> prettyFriendlyEmptyCtx expr
            <+> "is not a valid shape.",
        fix = Just "add more type annotations"
      }
  NonTypeClassInstanceHead _ (ident, p) typeClassIdent ->
    VehicleError
      { provenance = Just p,
        problem =
          "Cannot add"
            <+> prettyIdentName ident
            <+> "as an instance"
            <+> "as"
            <+> prettyIdentName typeClassIdent
            <+> "is not annotated as a"
            <+> pretty AnnTypeClass
            <+> ".",
        fix = Just "add more type annotations"
      }

--------------------------------------------------------------------------------
-- Individual errors
--------------------------------------------------------------------------------
-- MissingExplicitArgError

missingExplicitArgError ::
  (PrintableBuiltin builtin) =>
  MissingExplicitArgError builtin ->
  VehicleError
missingExplicitArgError (MissingExplicitArgError ctx explicitBinder nonExplicitArg) = do
  let argTypeDoc = prettyFriendly $ WithContext (typeOf explicitBinder) ctx
  let argDoc = prettyFriendly $ WithContext (argExpr nonExplicitArg) ctx
  VehicleError
    { provenance = Just $ provenanceOf nonExplicitArg,
      problem =
        "expected an"
          <+> pretty Explicit
          <+> "argument of type"
          <+> argTypeDoc
          <+> "but instead found"
          <+> pretty (visibilityOf nonExplicitArg)
          <+> "argument"
          <+> squotes argDoc,
      fix = Just $ "try inserting an argument of type" <+> argTypeDoc
    }

--------------------------------------------------------------------------------
-- FunctionTypeMismatchError

functionTypeMismatchError ::
  forall builtin.
  (PrintableBuiltin builtin) =>
  FunctionTypeMismatchError builtin ->
  VehicleError
functionTypeMismatchError (FunctionTypeMismatchError ctx fun nonPiType args) = do
  VehicleError
    { provenance = Just $ provenanceOf fun,
      problem =
        "expected"
          <+> squotes (prettyFriendly $ WithContext fun ctx)
          <+> "to have something of type"
          <+> squotes (prettyFriendly $ WithContext expectedType ctx)
          <+> "but inferred type"
          <+> squotes (prettyFriendly $ WithContext nonPiType ctx),
      fix = Nothing
    }
  where
    mkRes :: [Endo (DSLExpr builtin)]
    mkRes =
      [ Endo $ \tRes -> pi Nothing (visibilityOf arg) (relevanceOf arg) (tHole ("arg" <> pack (show i))) (const tRes)
        | (i, arg) <- zip [0 :: Int ..] args
      ]

    expectedType :: Expr builtin
    expectedType = fromDSL mempty (appEndo (mconcat mkRes) (tHole "res"))

--------------------------------------------------------------------------------
-- RelevantUseOfIrrelevantVariableError

relevantUseOfIrrelevantVariableError ::
  RelevantUseOfIrrelevantVariableError builtin ->
  VehicleError
relevantUseOfIrrelevantVariableError (RelevantUseOfIrrelevantVariableError _ p name) =
  VehicleError
    { provenance = Just p,
      problem = "cannot use irrelevant variable" <+> quotePretty name <+> "in an relevant context",
      fix = Nothing
    }

--------------------------------------------------------------------------------
-- FailedUnificationConstraintsError

failedUnificationConstraintsError ::
  forall builtin.
  (TypableBuiltin builtin) =>
  FailedUnificationConstraintsError builtin ->
  VehicleError
failedUnificationConstraintsError (FailedUnificationConstraintsError _freeEnv (err :| _)) = failedConstraintMessage err
  where
    failedConstraintMessage :: WithContext (UnificationConstraint builtin) -> VehicleError
    failedConstraintMessage (WithContext (Unify origin e1 e2) ctx) = do
      let boundCtx = boundContextOf ctx
      let namedBoundCtx = toNamedBoundCtx boundCtx
      let originMessage = case origin of
            CheckingExprType CheckingExpr {..} -> do
              "expected"
                <+> ( case checkedExpr of
                        Left binder -> "variable" <+> quotePretty binder
                        Right expr -> squotes (prettyUnificationConstraintOriginExpr ctx expr)
                    )
                <+> "to be of type"
                <+> squotes (prettyFriendly (WithContext checkedExprExpectedType namedBoundCtx))
                <+> "but was found to be of type"
                <+> typeAndNormalisedTypeDescription checkedExprExpectedType
            CheckingInstanceType (InstanceArgOrigin ArgOrigin {..}) ->
              "unable to find a consistent type for the overloaded expression"
                <+> squotes (prettyTypeClassConstraintOriginExpr ctx checkedInstanceOp checkedInstanceOpArgs)
            CheckingInstanceType (InstanceTypeRestrictionOrigin (TypeRestrictionOrigin _ _ (Right sort) _)) ->
              "All fields of record declarations annotated with" <+> quotePretty sort <+> "must have the same type"
            CheckingInstanceType (InstanceTypeRestrictionOrigin {}) ->
              ""

      let problemDescription = case origin of
            CheckingInstanceType (InstanceTypeRestrictionOrigin (TypeRestrictionOrigin _ (ident, _) (Right (FieldTypesMatch f1 f2)) _)) ->
              "."
                <> line
                <> "In the declaration of"
                  <+> quotePretty (nameOf ident)
                  <+> "field"
                  <+> quotePretty (nameOf f1)
                  <+> "has type:"
                <> line
                <> indent 2 (squotes (prettyFriendly (WithContext e1 namedBoundCtx)))
                <> line
                <> "which is not the same as the type of field"
                  <+> quotePretty (nameOf f2)
                <> line
                <> indent 2 (squotes (prettyFriendly (WithContext e2 namedBoundCtx)))
            _ ->
              "."
                <+> "In particular"
                <+> squotes (prettyFriendly (WithContext e1 namedBoundCtx))
                <+> "is not equal to"
                <+> squotes (prettyFriendly (WithContext e2 namedBoundCtx))
                <> "."

      let fixDescription = case origin of
            CheckingInstanceType (InstanceTypeRestrictionOrigin (TypeRestrictionOrigin _ _ (Right (FieldTypesMatch f1 f2)) _)) ->
              "either remove the @tensor annotation or ensure"
                <+> quotePretty (nameOf f1)
                <+> "and"
                <+> quotePretty (nameOf f2)
                <+> "have the same type"
            _ ->
              "check your types"

      VehicleError
        { provenance = Just $ provenanceOf ctx,
          problem =
            originMessage
              <> problemDescription,
          fix = Just fixDescription
        }

--------------------------------------------------------------------------------
-- FailedInstanceConstraintError

failedInstanceConstraintError ::
  forall builtin.
  (TypableBuiltin builtin) =>
  FailedInstanceConstraintError builtin ->
  VehicleError
failedInstanceConstraintError (FailedInstanceConstraintError freeEnv _metaEnv (WithContext constraint ctx) candidates) =
  case instanceOrigin constraint of
    InstanceTypeRestrictionOrigin t -> typeRestrictionError ctx t candidates
    InstanceArgOrigin t -> instanceArgOriginError freeEnv ctx t candidates

typeRestrictionError ::
  (Eq builtin, NormalisableBuiltin builtin) =>
  ConstraintContext builtin ->
  InstanceTypeRestrictionOrigin builtin ->
  [(WithContext (InstanceCandidate builtin), UnAnnDoc)] ->
  VehicleError
typeRestrictionError _ctx (TypeRestrictionOrigin _freeEnv (ident, p) sort typ) _candidates = do
  VehicleError
    { provenance = Just p,
      problem = problemDescription,
      fix =
        Just $
          "change the type of"
            <+> fixIdent
            <+> "to a supported type"
    }
  where
    fixIdent = case sort of
      Right (FieldTypeIsAllowed f) -> quotePretty (nameOf f)
      _ -> prettyIdentName ident

    problemDescription = case sort of
      Right (FieldTypeIsAllowed f) ->
        "The type of"
          <+> quotePretty (nameOf f)
          <+> "in record declaration"
          <+> quotePretty (nameOf ident :: Text)
          <> ":"
          <> line
          <> indent 2 (prettyFriendlyEmptyCtx typ)
          <> line
          <> "is not supported."
            <+> "All fields of a record declaration annotated with"
            <+> quotePretty sort
            <+> "must have the same type and must be either:"
          <> line
          <> indent 2 (prettyAllowedTypes supportedTypes)
      _ ->
        unsupportedAnnotationTypeDescription (pretty sort) ident typ
          <> "."
            <+> "The possible valid types for"
            <+> quotePretty sort
            <+> "annotated declarations are:"
          <> line
          <> indent 2 (prettyAllowedTypes supportedTypes)

    supportedTypes = case sort of
      Left RestrictedProperty -> ["Bool", "Vector Bool n", "Tensor Bool ns"]
      Left (RestrictedParameter Inferable) -> [pretty NatType]
      Left (RestrictedParameter NonInferable) -> map pretty [BoolType, IndexType, NatType, RatType]
      Left RestrictedDataset -> ["List A    " <+> datasetElementTypes, "Vector A n" <+> datasetElementTypes]
      Left RestrictedNetwork -> ["Tensor Rat [a_1, ..., a_n] -> Tensor Rat [b_1, ..., b_n]  (where 'a_i' and 'b_i' are all constants at compile time)"]
      Right _ -> ["The element of a tensor (e.g. Real), or", "A tensor (e.g. Tensor Real [...])"]

    datasetElementTypes = "(where A is either `Index n`, `Nat`, `Rat`, `List A`, `Vector A n`)"

    prettyAllowedTypes :: [Doc a] -> Doc a
    prettyAllowedTypes ts = vsep ((\(t, no) -> pretty no <> "." <+> t) <$> zip ts [1 :: Int ..])

instanceArgOriginError ::
  forall builtin.
  (TypableBuiltin builtin) =>
  FreeCtx builtin ->
  ConstraintContext builtin ->
  InstanceArgOrigin builtin ->
  [(WithContext (InstanceCandidate builtin), UnAnnDoc)] ->
  VehicleError
instanceArgOriginError _freeCtx ctx (ArgOrigin tcOp tcOpArgs tcOpType _tc) candidates =
  VehicleError
    { provenance = Just $ provenanceOf ctx,
      problem =
        "unable to work out a valid type for the overloaded expression"
          <+> originExpr
          <> "."
          <> line
          <> "The possible options explored were:"
          <> line
          <> indent 2 (vsep (fmap candidateOpType (zip [1 ..] candidates))),
      fix = Nothing
    }
  where
    originExpr :: Doc a
    originExpr = squotes (prettyTypeClassConstraintOriginExpr ctx tcOp tcOpArgs)

    actualArgs = if isCoercionExpr tcOp then tcOpArgs else []

    -- This assumes that the parameters of the type-class instance are the first arguments of the type-class operation.
    -- e.g. if `HasAdd t1 t2 t3` then `add` has type `forall {t1 t2 t3} . X`. If this is not the case then this function
    -- will not work.
    candidateOpType :: (Int, (WithContext (InstanceCandidate builtin), UnAnnDoc)) -> UnAnnDoc
    candidateOpType (no, (candidate, err)) = do
      let (candidateTypeArgs, _solutionCtx) = calculateInstanceCandidateTypeArgs candidate
      let finalTypeDoc = calculateInstanceDisplayType tcOpType candidateTypeArgs actualArgs -- freeCtx solutionCtx
      pretty no
        <> "." <+> finalTypeDoc
        <> line
        <> indent 2 ("- rejected:" <+> err)

calculateInstanceCandidateTypeArgs ::
  forall builtin.
  (PrintableBuiltin builtin) =>
  WithContext (InstanceCandidate builtin) ->
  ([Arg builtin], BoundCtx (Expr builtin))
calculateInstanceCandidateTypeArgs (WithContext candidate typingCtx) =
  calculateCandidateType typingCtx (candidateExpr candidate)
  where
    calculateCandidateType :: BoundCtx (Expr builtin) -> Expr builtin -> ([Arg builtin], BoundCtx (Expr builtin))
    calculateCandidateType dbCtx = \case
      Builtin _ _tc -> ([], dbCtx)
      FreeVar _ _ident -> ([], dbCtx)
      App (Builtin _ _tc) args ->
        (NonEmpty.toList args, dbCtx)
      App (FreeVar _ _ident) args ->
        (NonEmpty.toList args, dbCtx)
      Pi _ binder result ->
        calculateCandidateType (binder : dbCtx) result
      t -> developerError $ "UNSUPPORTED PRINTING" <+> prettyVerbose t

calculateInstanceDisplayType ::
  forall builtin a.
  (NormalisableBuiltin builtin, PrintableBuiltin builtin) =>
  Type builtin ->
  [Arg builtin] ->
  [Arg builtin] ->
  Doc a
calculateInstanceDisplayType _fullType _actualArgs _typingArgs = "TODO"

{-
do
  let normFullType = runNorm $ normaliseInFreeCtx freeEnv (toNamedBoundCtx boundCtx) (boundContextToEnv boundCtx) fullType
  let opArgs = mergeArgs actualArgs typingArgs
  instantiateTelescope normFullType opArgs
  where
    -- This is a complete hack
    mergeArgs :: [Arg builtin] -> [Arg builtin] -> [(Arg builtin, Bool)]
    mergeArgs args1 [] = fmap (,True) args1
    mergeArgs [] args2 = fmap (,False) args2
    mergeArgs (arg1 : args1) (arg2 : args2) = do
      let arg
            | isAbstract arg2 = (arg1, True)
            | isAbstract arg1 = (arg2, False)
            | otherwise = (arg1, True)
      arg : mergeArgs args1 args2
      where
        isAbstract :: Arg builtin -> Bool
        isAbstract (argExpr -> e) = case e of
          Hole {} -> True
          BoundVar {} -> True
          _ -> False

    instantiateTelescope ::
      VType builtin ->
      [(Arg builtin, Bool)] ->
      m (Doc a)
    instantiateTelescope typ arguments = do
      forcedType <- forceValue typ
      case (forcedType, arguments) of
        (VPi binder _, []) | isExplicit binder -> prettyFriendlyInCtx typ
        (VPi binder closure, args) -> do
          (alterEnv, remainingArgs) <- findRemainingArgs binder args
          let recType = runNorm $ normaliseInFreeCtx freeEnv (toNamedBoundCtx ctx) (alterEnv env) body
          let unnormBinder = quote mempty (boundCtxLv ctx) binder
          addNameToContext unnormBinder $ instantiateTelescope recType remainingArgs
        (_, []) -> prettyFriendlyInCtx typ
        _ ->
          return $
            "Malformed type-class operation type"
              <+> prettyVerbose typ
              <+> "and args"
              <+> prettyVerbose (fmap fst arguments)

    findRemainingArgs ::
      VBinder binder ->
      [(Arg builtin, Bool)] ->
      m (BoundEnv builtin -> BoundEnv builtin, [(Arg builtin, Bool)])
    findRemainingArgs binder args = case args of
      [] -> (extendEnvWithBound (boundCtxLv ctx) binder, [])
      ((arg, fromCandidate) : remainingArgs)
        | visibilityOf arg == visibilityOf binder || fromCandidate -> do
            let normArg = runNorm $ normaliseInFreeCtx freeEnv (toNamedBoundCtx ctx) (boundContextToEnv ctx) (argExpr arg)
            (extendEnvWithDefined normArg binder, remainingArgs)
        | isExplicit binder -> developerError "Missing explicit argument when printing"
        | otherwise -> (extendEnvWithBound (boundCtxLv ctx) binder, args)
runNorm :: SilentLoggerT Identity b -> b
runNorm = fst . runIdentity . runSilentLoggerT

-}
--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

prettyTypeClassConstraintOriginExpr ::
  (TypableBuiltin builtin) =>
  ConstraintContext builtin ->
  Expr builtin ->
  [Arg builtin] ->
  Doc a
prettyTypeClassConstraintOriginExpr ctx fun args = do
  let expr = case fun of
        -- We don't want to print out the actual coercion functions as the user is
        -- oblivious to them. Instead we want to print out what they are applied to.
        Builtin _ b -> case coercionArgs b of
          Just f -> f args
          Nothing -> fun
        _ -> fun
  prettyFriendly $ WithContext expr (namedBoundCtxOf ctx)

prettyUnificationConstraintOriginExpr ::
  (PrintableBuiltin builtin) =>
  ConstraintContext builtin ->
  Expr builtin ->
  Doc a
prettyUnificationConstraintOriginExpr ctx expr =
  prettyFriendly $ WithContext expr (namedBoundCtxOf ctx)

typeAndNormalisedTypeDescription ::
  forall builtin a.
  (Eq builtin, PrintableBuiltin builtin) =>
  Type builtin ->
  Doc a
typeAndNormalisedTypeDescription typ = do
  let reducedType = typ :: Expr builtin
  let reducedTypeDoc = prettyFriendlyEmptyCtx reducedType
  let unreducedTypeDoc = prettyFriendlyEmptyCtx typ

  line
    <> indent 2 unreducedTypeDoc
    <> line
    <> ( if layoutAsString reducedTypeDoc == layoutAsString unreducedTypeDoc
           then ""
           else
             "which reduces to:"
               <> line
               <> indent 2 reducedTypeDoc
               <> line
       )

unsupportedAnnotationTypeDescription ::
  forall builtin a.
  (Eq builtin, PrintableBuiltin builtin) =>
  Doc a ->
  Identifier ->
  Type builtin ->
  Doc a
unsupportedAnnotationTypeDescription annotation ident resourceType = do
  "The type of"
    <+> annotation
    <+> quotePretty (nameOf ident :: Text)
    <> ":"
    <> typeAndNormalisedTypeDescription resourceType
    <> "is not supported"

prettyIdentName :: Identifier -> Doc a
prettyIdentName ident = quotePretty (nameOf ident :: Name)
