module Vehicle.Compile.ExpandResources.Parameter
  ( parseParameterValue,
  )
where

import Control.Monad.Except
import Data.Map qualified as Map
import Data.Text (pack)
import Data.Text.Read (rational)
import Text.Read (readMaybe)
import Vehicle.Compile.Error
import Vehicle.Compile.ExpandResources.Core
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.TypedView.Core
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value

--------------------------------------------------------------------------------
-- Parameter parsing

parseParameterValue ::
  (MonadExpandResources m) =>
  DeclProvenance ->
  Type Builtin ->
  String ->
  m (Value Builtin)
parseParameterValue decl parameterType providedValue = do
  parser <- decideParser decl parameterType
  parser decl providedValue

decideParser ::
  (MonadExpandResources m) =>
  DeclProvenance ->
  Type Builtin ->
  m (DeclProvenance -> String -> m (Value Builtin))
decideParser declProv parameterType = do
  implicitParams <- getInferableParameterContext
  forcedType <- forceTypeExpr $ thunkifyExpr emptyBoundEnv parameterType
  case forcedType of
    -- TODO check that Index dimension is constant, or at least will be after
    -- implicit parameters are filled in (the tricky bit).
    VIndexType size -> do
      forcedSize <- forceNatExpr size
      case forcedSize of
        VNatParameter varIdent
          | Map.member varIdent implicitParams ->
              throwError $ ParameterTypeInferableParameterIndex declProv varIdent
        VNatLiteral n -> return (parseIndex n)
        _ -> throwError $ ParameterTypeVariableSizeIndex declProv parameterType size
    VNatType {} -> return parseNat
    VTensorType tElem _ -> do
      forcedTElem <- forceTypeExpr tElem
      case forcedTElem of
        VBoolType -> return parseBool
        VRatType -> return parseRat
        _ -> invalidParameterType
    _ -> invalidParameterType
  where
    invalidParameterType =
      compilerDeveloperError $
        "Invalid parameter type"
          <+> squotes (prettyVerbose parameterType)
          <+> "should have been caught during type-checking"

parseBool :: (MonadCompile m) => DeclProvenance -> String -> m (Value Builtin)
parseBool decl value = case readMaybe value of
  Just v -> return $ IBoolLiteral v
  Nothing -> throwError $ ParameterValueUnparsable decl value BoolType

parseNat :: (MonadCompile m) => DeclProvenance -> String -> m (Value Builtin)
parseNat decl value = case readMaybe value of
  Just v
    | v >= 0 -> return $ INatLiteral v
    | otherwise -> throwError $ ParameterValueInvalidNat decl v
  Nothing -> throwError $ ParameterValueUnparsable decl value NatType

parseRat :: (MonadCompile m) => DeclProvenance -> String -> m (Value Builtin)
parseRat decl value = case rational (pack value) of
  Left _err -> throwError $ ParameterValueUnparsable decl value RatType
  Right (v, _) -> return $ IRatLiteral v

parseIndex :: (MonadCompile m) => Int -> DeclProvenance -> String -> m (Value Builtin)
parseIndex n decl value = case readMaybe value of
  Nothing -> throwError $ ParameterValueUnparsable decl value IndexType
  Just v ->
    if v >= 0 && v < n
      then return $ IIndexLiteral v (Forced $ INatLiteral n)
      else throwError $ ParameterValueInvalidIndex decl v n
