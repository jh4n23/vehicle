-- | At various points in the compiler, we have different sets of builtins (e.g.
-- first time we type-check we use the standard set of builtins + type +
-- type classes, but when checking polarity and linearity information we
-- subsitute out all the types and type-classes for new types.)
--
-- The interfaces defined in this file allow us to abstract over the exact set
-- of builtins being used, and therefore allows us to define operations
-- (e.g. normalisation) once, rather than once for each builtin type.
module Vehicle.Data.Code.Interface
  ( module Args,
    module Operations,
    module Patterns,
  )
where

import Vehicle.Data.Code.Interface.Args as Args
import Vehicle.Data.Code.Interface.Operations as Operations
import Vehicle.Data.Code.Interface.Patterns as Patterns
