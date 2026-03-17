module Vehicle.Compile.Type.Meta.Variable
  ( MetaInfo (..),
    extendMetaCtx,
    getMetaDependencies,
    HasMetas (..),
    MetaVariableContext,
    findMetaInfo,
    addMetaSolution,
  )
where

import Control.Monad.Writer (MonadWriter (..), execWriter)
import Data.List.NonEmpty (NonEmpty)
import Vehicle.Compile.Normalise.Quote (unnormalise)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Meta.Map (MetaMap)
import Vehicle.Compile.Type.Meta.Map qualified as MetaMap
import Vehicle.Compile.Type.Meta.Set (MetaSet)
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet
import Vehicle.Data.Variable.Bound.Context.Generic.Core

-- Eventually when metas make into the builtins, this should module
-- should also contain the definition of meta-variables themselves.

--------------------------------------------------------------------------------
-- Meta information

-- | The information stored about each meta-variable.
data MetaInfo builtin = MetaInfo
  { -- | Location in the source file the meta-variable was generated
    metaProvenance :: Provenance,
    -- | The type of the meta-variable
    metaType :: Type builtin,
    -- | The number of bound variables in scope when the meta-variable was created.
    metaCtx :: BoundCtx (Expr builtin),
    -- | The solution to the meta variable
    metaSolution :: Maybe (Expr builtin)
  }
  deriving (Show)

extendMetaCtx :: Binder builtin -> MetaInfo builtin -> MetaInfo builtin
extendMetaCtx binder MetaInfo {..} =
  MetaInfo
    { metaCtx = binder : metaCtx,
      ..
    }

getMetaDependencies :: [Arg builtin] -> [Ix]
getMetaDependencies = \case
  (ExplicitArg _ (BoundVar _ i)) : args -> i : getMetaDependencies args
  _ -> []

--------------------------------------------------------------------------------
-- Objects which have meta variables in.

class HasMetas a where
  findMetas :: (MonadWriter MetaSet m) => a -> m ()

  metasIn :: a -> MetaSet
  metasIn e = execWriter (findMetas e)

instance HasMetas (Expr builtin) where
  findMetas expr = case expr of
    Meta _ m -> tell (MetaSet.singleton m)
    Universe {} -> return ()
    Hole {} -> return ()
    Builtin {} -> return ()
    BoundVar {} -> return ()
    FreeVar {} -> return ()
    Pi _ binder result -> do findMetas binder; findMetas result
    Let _ bound binder body -> do findMetas bound; findMetas binder; findMetas body
    Lam _ binder body -> do findMetas binder; findMetas body
    App fun args -> do findMetas fun; findMetas args
    Record _ _ fields -> findMetas $ fmap snd fields
    RecordProj _ recordType record _ -> do findMetas recordType; findMetas record

instance (HasMetas expr) => HasMetas (GenericArg expr) where
  findMetas = mapM_ findMetas

instance (HasMetas expr) => HasMetas (GenericBinder expr) where
  findMetas = mapM_ findMetas

instance (HasMetas a) => HasMetas [a] where
  findMetas = mapM_ findMetas

instance (HasMetas a) => HasMetas (NonEmpty a) where
  findMetas = mapM_ findMetas

instance HasMetas (Contextualised (InstanceConstraint builtin) (ConstraintContext builtin)) where
  findMetas (WithContext (Resolve _ m _ _ goal) ctx) = do
    tell (MetaSet.singleton m)
    let argExprs = fmap (unnormalise (contextDBLevel ctx) . argExpr) (goalSpine goal) :: [Expr builtin]
    findMetas argExprs

instance HasMetas (Contextualised (UnificationConstraint builtin) (ConstraintContext builtin)) where
  findMetas (WithContext (Unify _ e1 e2) ctx) = do
    findMetas (unnormalise (contextDBLevel ctx) e1 :: Expr builtin)
    findMetas (unnormalise (contextDBLevel ctx) e2 :: Expr builtin)

instance HasMetas (ArgInsertionProblem builtin) where
  findMetas ArgInsertionProblem {..} = do
    findMetas originalFun
    findMetas checkedArgs
    findMetas uncheckedArgs

instance HasMetas (ApplicationConstraint builtin) where
  findMetas (InferArgs _ _ insertionProblem) = findMetas insertionProblem

instance HasMetas (Contextualised (Constraint builtin) (ConstraintContext builtin)) where
  findMetas (WithContext constraint ctx) = case constraint of
    UnificationConstraint c -> findMetas (WithContext c ctx)
    InstanceConstraint c -> findMetas (WithContext c ctx)
    ApplicationConstraint c -> findMetas c

--------------------------------------------------------------------------------
-- Meta context

type MetaVariableContext builtin = MetaMap (MetaInfo builtin)

findMetaInfo :: MetaVariableContext builtin -> MetaID -> MetaInfo builtin
findMetaInfo ctx meta =
  case MetaMap.lookup meta ctx of
    Just info -> info
    Nothing ->
      developerError $
        "Requesting info for unknown meta" <+> pretty meta <+> "not in context"

addMetaSolution :: Expr builtin -> MetaID -> MetaVariableContext builtin -> MetaVariableContext builtin
addMetaSolution solution = MetaMap.adjust (\info -> info {metaSolution = Just solution})
