module Vehicle.Data.Builtin.Interface.Print where

import Vehicle.Data.AST.Expr.Desugared (Expr (..), pattern App)
import Vehicle.Data.Builtin.Standard.Core
import Vehicle.Prelude

--------------------------------------------------------------------------------
-- Conversion

--------------------------------------------------------------------------------
-- Printing

-- | Use to convert builtins for printing that have no representation in the
-- standard `Builtin` type.
cheatConvertBuiltin :: Provenance -> Doc a -> Expr builtin
cheatConvertBuiltin p b = Var p $ layoutAsText b

class (Show builtin, Pretty builtin) => PrintableBuiltin builtin where
  convertBuiltin :: Provenance -> builtin -> Expr Builtin

instance PrintableBuiltin Builtin where
  convertBuiltin = Builtin

instance PrintableBuiltin BuiltinType where
  convertBuiltin p = Builtin p . BuiltinType

instance PrintableBuiltin TypeClassOp where
  convertBuiltin p = Builtin p . TypeClassOp

instance PrintableBuiltin BuiltinConstructor where
  convertBuiltin p = Builtin p . BuiltinConstructor

instance PrintableBuiltin BuiltinFunction where
  convertBuiltin p = Builtin p . BuiltinFunction

instance PrintableBuiltin DerivedFunction where
  convertBuiltin p = Builtin p . DerivedFunction

instance PrintableBuiltin ComparisonOp where
  convertBuiltin p = convertBuiltin p . CompareTC

convertBuiltins :: (PrintableBuiltin builtin) => Expr builtin -> Expr Builtin
convertBuiltins expr = case expr of
  Builtin p b -> convertBuiltin p b
  App fun args -> App (convertBuiltins fun) (fmap (fmap convertBuiltins) args)
  Pi p binder res -> Pi p (fmap convertBuiltins binder) $ convertBuiltins res
  Let p bound binder body -> Let p (convertBuiltins bound) (fmap convertBuiltins binder) (convertBuiltins body)
  Lam p binder body -> Lam p (fmap convertBuiltins binder) (convertBuiltins body)
  Record p fs -> Record p (mapRecordFields convertBuiltins fs)
  RecordAcc p r field -> RecordAcc p (convertBuiltins r) field
  Universe p -> Universe p
  Var p v -> Var p v
  Hole p n -> Hole p n
