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
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.TypedView
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
  forcedType <- forceExpr emptyBoundEnv parameterType

  case toTypeValue forcedType of
    -- TODO check that Index dimension is constant, or at least will be after
    -- implicit parameters are filled in (the tricky bit).
    VIndexType size -> do
      forcedSize <- forceValue size
      case toNatValue forcedSize of
        VNatParameter varIdent
          | Map.member varIdent implicitParams ->
              throwError $ ParameterTypeInferableParameterIndex declProv varIdent
        VNatLiteral n -> return (parseIndex n)
        _ -> throwError $ ParameterTypeVariableSizeIndex declProv parameterType size
    VNatType {} -> return parseNat
    VTensorType tElem _ -> do
      forcedTElem <- forceValue tElem
      case toTypeValue forcedTElem of
        VBoolType -> return parseBool
        VRatType -> return parseRat
        _ -> invalidParameterType forcedType
    _ -> invalidParameterType forcedType
  where
    invalidParameterType forcedType =
      compilerDeveloperError $
        "Invalid parameter type"
          <+> squotes (prettyVerbose forcedType)
          <+> "should have been caught during type-checking"

parseBool :: (MonadCompile m) => DeclProvenance -> String -> m (Value Builtin)
parseBool decl value = case readMaybe value of
  Just v -> return $ Forced $ IBoolLiteral v
  Nothing -> throwError $ ParameterValueUnparsable decl value BoolType

parseNat :: (MonadCompile m) => DeclProvenance -> String -> m (Value Builtin)
parseNat decl value = case readMaybe value of
  Just v
    | v >= 0 -> return $ Forced $ INatLiteral v
    | otherwise -> throwError $ ParameterValueInvalidNat decl v
  Nothing -> throwError $ ParameterValueUnparsable decl value NatType

parseRat :: (MonadCompile m) => DeclProvenance -> String -> m (Value Builtin)
parseRat decl value = case rational (pack value) of
  Left _err -> throwError $ ParameterValueUnparsable decl value RatType
  Right (v, _) -> return $ Forced $ IRatLiteral v

parseIndex :: (MonadCompile m) => Int -> DeclProvenance -> String -> m (Value Builtin)
parseIndex n decl value = case readMaybe value of
  Nothing -> throwError $ ParameterValueUnparsable decl value IndexType
  Just v ->
    if v >= 0 && v < n
      then return $ Forced $ IIndexLiteral v (INatLiteral n)
      else throwError $ ParameterValueInvalidIndex decl v n
