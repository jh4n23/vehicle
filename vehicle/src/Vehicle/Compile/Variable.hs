module Vehicle.Compile.Variable
  ( createUserVar,
  )
where

-- Needed as Applicative is exported by Prelude in GHC 9.6 and above.
import Control.Monad (when)
import Control.Monad.Except (MonadError (..))
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.NBE (forceThunk)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Compile.TypedView
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Value (VBinder, Value (..))
import Vehicle.Data.Variable.Bound.Context.Name
import Vehicle.Data.Variable.Free.Context (MonadFreeContext)
import Prelude hiding (Applicative (..))

--------------------------------------------------------------------------------
-- Extraction

type MonadCreateUserVar m =
  ( MonadCompile m,
    MonadReadableNameContext m,
    MonadFreeContext Builtin m
  )

createUserVar ::
  (MonadCreateUserVar m) =>
  DeclProvenance ->
  VBinder Builtin ->
  m (Value Builtin)
createUserVar propertyProvenance binder = do
  let varName = getBinderName binder
  checkUserVariableNameIsUnique propertyProvenance varName
  varDimensions <- getUserVariableDims binder
  return varDimensions

checkUserVariableNameIsUnique ::
  (MonadCreateUserVar m) =>
  DeclProvenance ->
  Name ->
  m ()
checkUserVariableNameIsUnique propertyProvenance varName = do
  namedCtx <- getNameContext
  let isDuplicateName = Just varName `elem` namedCtx
  when isDuplicateName $
    throwError $
      DuplicateQuantifierNames propertyProvenance varName

getUserVariableDims ::
  (MonadCreateUserVar m) =>
  VBinder Builtin ->
  m (Value Builtin)
getUserVariableDims binder = do
  forcedType <- forceTypeExpr (typeOf binder)
  case forcedType of
    VTensorType _tElem dims -> return dims
    _ -> developerError $ "Unexpected quantifier type:" <+> prettyVerbose (Unforced $ typeOf binder)
