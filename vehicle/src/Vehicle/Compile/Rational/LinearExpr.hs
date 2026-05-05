module Vehicle.Compile.Rational.LinearExpr
  ( LinearityError (..),
    compileLinearAssertion,
  )
where

-- Needed as Applicative is exported by Prelude in GHC 9.6 and above.
import Control.Applicative (Applicative (..))
import Control.Monad.Except (MonadError (..), runExceptT)
import Control.Monad.Trans (MonadTrans (..))
import Vehicle.Compile.Constants.Rational
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Prelude
import Vehicle.Compile.TypedView.Purification (ConstraintExpr (..))
import Vehicle.Data.Assertion (comparisonToAssertion)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.LinearExpr
import Vehicle.Data.Tensor (TensorShape, pattern ConstantTensor)
import Vehicle.Data.Variable.Bound.Level
import Prelude hiding (Applicative (..))

type MonadCompileLinearExpr m =
  ( MonadLogger m,
    MonadError LinearityError m,
    MonadNorm Builtin m
  )

data LinearityError
  = NonLinearity
  | UnreducedExpr ConstraintExpr
  | TrivialExpr Bool

--------------------------------------------------------------------------------
-- Tensor expression

compileLinearAssertion ::
  (MonadLogger m, MonadNorm Builtin m) =>
  (Lv -> m SliceVariable) ->
  ComparisonOp ->
  TensorShape ->
  ConstraintExpr ->
  ConstraintExpr ->
  m (Either LinearityError LinearAssertion)
compileLinearAssertion toVar op shape x y = do
  runExceptT $ do
    linX <- compile (lift . toVar) shape x
    linY <- compile (lift . toVar) shape y
    boolOrAssertion <- comparisonToAssertion op linX linY
    either (throwError . TrivialExpr) return boolOrAssertion

compile ::
  forall m.
  (MonadCompileLinearExpr m) =>
  (Lv -> m SliceVariable) ->
  TensorShape ->
  ConstraintExpr ->
  m LinearExpression
compile toVar shape expr = case expr of
  ----------------
  -- Base cases --
  ----------------
  ERatTensorLiteral t -> do
    return $ constantExpr t
  ERatTensorBoundVar lv -> do
    singletonVarExpr (ConstantTensor shape 0) <$> toVar lv
  ---------------------
  -- Inductive cases --
  ---------------------
  ENegRatTensor e -> scaleExpr (-1) <$> compile toVar shape e
  EAddRatTensor e1 e2 -> addExprsUnsafe 1 1 <$> compile toVar shape e1 <*> compile toVar shape e2
  ESubRatTensor e1 e2 -> addExprsUnsafe 1 (-1) <$> compile toVar shape e1 <*> compile toVar shape e2
  EMulRatTensor e1 e2 -> do
    e1' <- compile toVar shape e1
    e2' <- compile toVar shape e2
    case (isConstant e1', isConstant e2') of
      (Just (ConstantTensor _ c1), _) -> return $ scaleExpr c1 e2'
      (_, Just (ConstantTensor _ c2)) -> return $ scaleExpr c2 e1'
      (Just _, _) -> unreduced
      (_, Just _) -> unreduced
      _ -> throwError NonLinearity
  EDivRatTensor e1 e2 -> do
    e1' <- compile toVar shape e1
    e2' <- compile toVar shape e2
    case isConstant e2' of
      Just (ConstantTensor _ c2) -> return $ scaleExpr (1 / c2) e1'
      Just _ -> unreduced
      _ -> throwError NonLinearity
  where
    unreduced = throwError $ UnreducedExpr expr
