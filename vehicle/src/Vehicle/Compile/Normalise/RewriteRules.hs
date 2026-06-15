module Vehicle.Compile.Normalise.RewriteRules where

{-

fuseReduceAndForeachTensor ::
  forall m expr thunk builtin.
  (MonadLogger m, PrintableBuiltin builtin, Quote (expr builtin) (Expr builtin), HasBuiltinConstructor expr thunk, HasLambdaConstructor expr thunk Closure, NormalisableBuiltin builtin, BuiltinHasNatType builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin, BuiltinHasTensors builtin, BuiltinHasListLiterals builtin, BuiltinHasNatLiterals builtin, BuiltinHasBoolLiterals builtin, HasTensorLiterals expr builtin, HasLiftableTensorOperations expr thunk builtin) =>
  NamedBoundCtx ->
  expr builtin ->
  m (Maybe (thunk builtin, thunk builtin))
fuseReduceAndForeachTensor ctx value = do
  fusionEnter ctx value
  fusionExit ctx =<< case getExpr accessForeachTensor value of
    Just (ForeachTensorArgs typ d _ (getExpr accessForcedLamC -> Just (binder, Closure env body))) -> do
      let lv = boundCtxLv ctx
      let newEnv = extendEnvWithBound lv binder env
      let newCtx = nameOf binder : ctx
      body' <- eval newCtx newEnv body
      case getExpr accessReduceAnd body' of
        Just (TensorReductionArgs (tensorDims :: thunk builtin) tensor) -> do
          (newDims, newTensor) <- fromMaybe (tensorDims, tensor) <$> fuseReduceAndForeachTensor @m @expr @thunk newCtx (force tensor)
          let newTensor' = quote @(expr builtin) mempty (lv + 1) (force newTensor)
          let newLam = mkExpr accessForcedLamC (binder, Closure (namedBoundContextToEnv ctx) newTensor')
          let newForeachArgs = ForeachTensorArgs typ d newDims newLam
          newBody' <- evalForeachTensor newCtx newForeachArgs
          return $ Just (exprToThunk $ IDimCons d newDims, exprToThunk newBody')
        _ -> return Nothing
    _ -> return Nothing

-}
