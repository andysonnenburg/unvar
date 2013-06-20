{-# LANGUAGE FlexibleInstances #-}
{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module UnVar
       ( plugin
       ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict

import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Monoid (Any (..))

import GhcPlugins

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install
                       }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  reinitializeGlobals
  return $ todo ++ [CoreDoPluginPass "unvar" unVar] ++ todo

unVar :: ModGuts -> CoreM ModGuts
unVar guts = do
  let binds = mg_binds guts
  printPpr binds
  (_, _, captured) <- runQueryM $ mapM queryBind binds
  binds' <- runTransformM (mapM transformBind binds) captured
  printPpr binds'
  return guts { mg_binds = binds' }

printPpr :: Outputable a => a -> CoreM ()
printPpr = putMsg . ppr

data MutVarDeps
  = ClosesOver (UniqSet CoreBndr) MutVarDeps
  | PointsTo CoreBndr
  | None deriving Eq

instance Outputable MutVarDeps where
  ppr deps = case deps of
    ClosesOver bndrs deps' ->
      ptext (sLit "ClosesOver") <+> ppr bndrs <+> parens (ppr deps')
    PointsTo bndr ->
      ptext (sLit "PointsTo") <+> ppr bndr
    None ->
      ptext (sLit "None")

type QueryM = StateT S CoreM

data S = S { bndrMutVarDeps :: !(UniqFM MutVarDeps)
           , candidateBndrs :: !(UniqSet CoreBndr)
           }

runQueryM :: QueryM a -> CoreM (a, UniqFM MutVarDeps, UniqSet CoreBndr)
runQueryM m = do
  (a, S deps captured) <- runStateT m (S emptyUFM emptyUniqSet)
  return (a, deps, captured)

queryExpr e = do
  r@(deps, labels) <- queryExpr' e
  lift $ do
    putMsgS "XXX queryExpr XXX"
    printPpr e
    printPpr deps
    printPpr labels
  return r

queryExpr' :: CoreExpr -> QueryM (MutVarDeps, UniqSet CoreBndr)
queryExpr' expr = case expr of
  Case (App (App (App (App (Var f) _) _) e1) _)
    _ _ [(_, [_, x], e2)] | isNewMutVar f -> do
    (deps1, bndrs1) <- queryExpr e1
    abandonDepBndrs deps1
    captureBndr x
    putBndrDeps x $ PointsTo x
    (deps2, bndrs2) <- queryExpr e2
    when (x `memberOfDeps` deps2) $ abandonBndr x
    return (deps2, delOneFromUniqSet (unionUniqSets bndrs1 bndrs2) x)
  Case (App (App (App (App (Var f) _) _) (Var x)) _)
    _ _ [(_, [_, _], e)] | isReadMutVar f -> do
    bndrs <- depsToUniqSet <$> getBndrDeps x
    (deps, bndrs') <- queryExpr e
    return (deps, unionUniqSets bndrs bndrs')    
  Case (App (App (App (App (App (Var f) _) _) (Var x)) e1) _)
    _ _ [(DEFAULT, [], e2)] | isWriteMutVar f -> do
    bndrs <- depsToUniqSet <$> getBndrDeps x
    (deps1, bndrs1) <- queryExpr e1
    abandonDepBndrs deps1
    (deps2, bndrs2) <- queryExpr e2
    return (deps2, unionManyUniqSets [bndrs, bndrs1, bndrs2])
  Var x -> do
    deps <- getBndrDeps x
    return (deps, depsToUniqSet deps)
  Lit _ ->
    return (None, emptyUniqSet)
  App e1 e2 -> do
    (deps1, bndrs1) <- queryExpr e1
    (deps2, bndrs2)  <- queryExpr e2
    abandonDepBndrs deps2
    let (bndrs', deps') = unconsDeps deps1
    return (deps', unionManyUniqSets [bndrs1, bndrs2, bndrs'])
  Lam _ e -> do
    (deps, bndrs) <- queryExpr e
    return (ClosesOver bndrs deps, emptyUniqSet)
  Let bind e -> do
    bndrs <- queryBind bind
    (deps, bndrs') <- queryExpr e
    return (deps, unionUniqSets bndrs bndrs')
  Case e x _ alts -> do
    (deps, bndrs) <- queryExpr e
    putBndrDeps x deps
    (deps', bndrs') <- queryAlts alts
    return (deps', unionManyUniqSets [depsToUniqSet deps, bndrs, bndrs'])
  Cast e _ ->
    queryExpr e
  Tick _ e ->
    queryExpr e
  Type _ ->
    return (None, emptyUniqSet)
  Coercion _ ->
    return (None, emptyUniqSet)

queryBind :: CoreBind -> QueryM (UniqSet CoreBndr)
queryBind bind = case bind of
  NonRec x e -> do
    (deps, bndrs) <- queryExpr e
    putBndrDeps x deps
    return bndrs
  Rec binds -> do
    mapM_ (flip putBndrDeps None . fst) binds
    fmap unionManyUniqSets $ runQueryRecM $ forM binds $ \ (x, e) -> do
      (deps, bndrs) <- lift $ queryExpr e
      putRecBndrDeps x deps
      return bndrs

type QueryRecM = WriterT Any QueryM

runQueryRecM :: QueryRecM a -> QueryM a
runQueryRecM m = do
  (a, w) <- runWriterT m
  if getAny w then runQueryRecM m else return a

putRecBndrDeps :: CoreBndr -> MutVarDeps -> QueryRecM ()
putRecBndrDeps x deps = do
  deps' <- lift $ getBndrDeps x
  when (deps /= deps') $ do
    lift $ putBndrDeps x deps
    tell $ Any True

queryAlts :: [CoreAlt] -> QueryM (MutVarDeps, UniqSet CoreBndr)
queryAlts = foldlM1 f <=< mapM queryAlt
  where
    f (deps, bndrs) (deps', bndrs') =
      (,) <$> unifyDeps deps deps' <*> pure (unionUniqSets bndrs bndrs')

foldlM1 :: Monad m => (a -> a -> m a) -> [a] -> m a
foldlM1 _ [] = error "foldlM1': empty structure"
foldlM1 f (x0:xs) = foldr f' return xs x0
  where
    f' x k z = f z x >>= k

queryAlt :: CoreAlt -> QueryM (MutVarDeps, UniqSet CoreBndr)
queryAlt (_, _, e) = queryExpr e

getBndrDeps :: CoreBndr -> QueryM MutVarDeps
getBndrDeps x = gets $ fromMaybe None . flip lookupUFM x . bndrMutVarDeps

putBndrDeps :: CoreBndr -> MutVarDeps -> QueryM ()
putBndrDeps x deps = modify $ \ s@(S xs _) ->
  s { bndrMutVarDeps = addToUFM xs x deps }

captureBndr :: CoreBndr -> QueryM ()
captureBndr bndr = modify $ \ s@(S _ xs) ->
  s { candidateBndrs = addOneToUniqSet xs bndr }

abandonDepBndrs :: MutVarDeps -> QueryM ()
abandonDepBndrs deps = case deps of
  ClosesOver bndrs deps' -> do
    modify $ \ s@(S _ xs) -> s { candidateBndrs = xs `minusUniqSet` bndrs }
    abandonDepBndrs deps'
  PointsTo bndr ->
    abandonBndr bndr
  None ->
    return ()

abandonBndr :: CoreBndr -> QueryM ()
abandonBndr bndr = modify $ \ s@(S _ xs) ->
  s { candidateBndrs = delOneFromUniqSet xs bndr }

abandonBndrs :: UniqSet CoreBndr -> QueryM ()
abandonBndrs bndrs = modify $ \ s@(S _ xs) ->
  s { candidateBndrs = xs `minusUniqSet` bndrs }

unconsDeps :: MutVarDeps -> (UniqSet CoreBndr, MutVarDeps)
unconsDeps deps = case deps of
  ClosesOver bndrs deps' -> (bndrs, deps')
  PointsTo _ -> (emptyUniqSet, None)
  None -> (emptyUniqSet, None)

memberOfDeps :: CoreBndr -> MutVarDeps -> Bool
memberOfDeps bndr deps = case deps of
  ClosesOver bndrs deps' ->
    elementOfUniqSet bndr bndrs ||
    memberOfDeps bndr deps'
  PointsTo bndr' ->
    bndr == bndr'
  None ->
    False

unifyDeps :: MutVarDeps -> MutVarDeps -> QueryM MutVarDeps
unifyDeps x y = case (x, y) of
  (ClosesOver as x', ClosesOver bs y') -> do
    abandonBndrs $ unionUniqSets as bs `minusUniqSet` as'
    ClosesOver as' <$> unifyDeps x' y'
    where
      as' = intersectUniqSets as bs
  (PointsTo a, PointsTo b)
    | a == b -> return x
  _ -> do
    abandonDepBndrs x
    abandonDepBndrs y
    return None

depsToUniqSet :: MutVarDeps -> UniqSet CoreBndr
depsToUniqSet deps = case deps of
  ClosesOver _ _ -> emptyUniqSet
  PointsTo bndr -> unitUniqSet bndr
  None -> emptyUniqSet

type TransformM = ReaderT R CoreM

data R = R { capturedBndrs :: UniqSet CoreBndr
           , bndrSubst :: UniqFM CoreBndr
           }

runTransformM :: TransformM a -> UniqSet CoreBndr -> CoreM a
runTransformM m captured = runReaderT m (R captured emptyUFM)

transformExpr :: CoreExpr -> TransformM CoreExpr
transformExpr expr = do
  captured <- asks capturedBndrs
  case expr of
    Case (App (App (App (App (Var f) (Type t)) _) e1) (Var s))
      _ _ [(_, [s', x], e2)] | isNewMutVar f && elementOfUniqSet x captured ->
      Let <$>
      (NonRec x' <$> transformExpr e1) <*>
      localBndr x x'
      (join $
       localBndr s' <$>
       transformBndr s <*>
       pure (transformExpr e2))
      where
        x' = setIdInfo (setVarType x t) vanillaIdInfo
    Case (App (App (App (App (Var f) _) _) (Var x)) (Var s))
      _ _ [(_, [s', a], e)] | isReadMutVar f && elementOfUniqSet x captured ->
      Let <$>
      (NonRec a <$> (Var <$> transformBndr x)) <*>
      join (localBndr s' <$> transformBndr s <*> pure (transformExpr e))
    Case (App (App (App (App (App (Var f) _) _) (Var x)) e1) (Var s))
      s' _ [(DEFAULT, [], e2)] | isWriteMutVar f && elementOfUniqSet x captured ->
      setVarUnique <$> transformBndr x <*> lift getUniqueM >>= \ x' ->
      Let <$>
      (NonRec x' <$> transformExpr e1) <*>
      localBndr x x'
      (join $
       localBndr s' <$>
       transformBndr s <*>
       pure (transformExpr e2))
    Var x -> Var <$> transformBndr x
    Lit _ -> return expr
    App e1 e2 -> App <$> transformExpr e1 <*> transformExpr e2
    Lam x e -> Lam <$> transformBndr x <*> transformExpr e
    Let bind e -> Let <$> transformBind bind <*> transformExpr e
    Case e x typ alts -> transformCase e x typ alts
    Cast e coercion -> Cast <$> transformExpr e <*> pure coercion
    Tick tick e -> Tick tick <$> transformExpr e
    Type _ -> return expr
    Coercion _ -> return expr

transformCase :: CoreExpr -> Var -> Type -> [CoreAlt] -> TransformM CoreExpr
transformCase e x typ alts =
  Case <$> transformExpr e <*> pure x <*> pure typ <*> transformAlts alts

transformBind :: CoreBind -> TransformM CoreBind
transformBind bind = case bind of
  NonRec bndr e -> NonRec <$> transformBndr bndr <*> transformExpr e
  Rec binds -> Rec <$> mapM transformTuple binds
    where
      transformTuple (bndr, expr) =
        (,) <$> transformBndr bndr <*> transformExpr expr

transformAlts :: [CoreAlt] -> TransformM [CoreAlt]
transformAlts = mapM transformAlt

transformAlt :: CoreAlt -> TransformM CoreAlt
transformAlt (altCon, vars, expr) = (,,) altCon vars <$> transformExpr expr

localBndr :: CoreBndr -> CoreBndr -> TransformM a -> TransformM a
localBndr bndr bndr' = local $ \ r@(R _ subst) ->
  r { bndrSubst = addToUFM subst bndr bndr' }

transformBndr :: CoreBndr -> TransformM CoreBndr
transformBndr bndr = asks $ fromMaybe bndr . flip lookupUFM bndr . bndrSubst

isNewMutVar :: NamedThing a => a -> Bool
isNewMutVar =
  (&&) <$>
  (== ghcPrimModule) . Stable . nameModule . getName <*>
  (== newMutVarOccName) . Stable . getOccName

newMutVarOccName :: Stable OccName
newMutVarOccName = Stable $ mkVarOcc "newMutVar#"

isReadMutVar :: NamedThing a => a -> Bool
isReadMutVar =
  (&&) <$>
  (== ghcPrimModule) . Stable . nameModule . getName <*>
  (== readMutVarOccName) . Stable . getOccName

readMutVarOccName :: Stable OccName
readMutVarOccName = Stable $ mkVarOcc "readMutVar#"

isWriteMutVar :: NamedThing a => a -> Bool
isWriteMutVar =
  (&&) <$>
  (== ghcPrimModule) . Stable . nameModule . getName <*>
  (== writeMutVarOccName) . Stable . getOccName

writeMutVarOccName :: Stable OccName
writeMutVarOccName = Stable $ mkVarOcc "writeMutVar#"

ghcPrimModule :: Stable Module
ghcPrimModule = Stable $ mkModule primPackageId (mkModuleName "GHC.Prim")

newtype Stable a = Stable { unStable :: a }

instance Eq (Stable Module) where
  x == y =
    ((==) `on` Stable . modulePackageId . unStable) x y &&
    ((==) `on` Stable . moduleName . unStable) x y

instance Eq (Stable PackageId) where
  x == y = (stablePackageIdCmp `on` unStable) x y == EQ

instance Eq (Stable ModuleName) where
  x == y = (stableModuleNameCmp `on` unStable) x y == EQ

instance Eq (Stable OccName) where
  x == y = (compare `on` unStable) x y == EQ
