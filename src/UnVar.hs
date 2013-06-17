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

import Data.Function (on)
import Data.Maybe

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
  printPpr $ mg_binds guts
  binds <- runUnVarM $ mapM transformBind $ mg_binds guts
  printPpr binds
  return guts { mg_binds = binds }

printPpr :: Outputable a => a -> CoreM ()
printPpr = putMsg . ppr

type UnVarM = ReaderT (UniqFM Var) CoreM

data MutVarDeps
  = ClosesOver (UniqSet MutVarLabel) MutVarDeps
  | PointsTo MutVarLabel
  | Undefined

type MutVarLabel = Unique

runUnVarM :: UnVarM a -> CoreM a
runUnVarM = flip runReaderT emptyUFM

queryExpr :: CoreExpr -> CoreM (UniqFM MutVarDeps, UniqSet MutVarLabel)
queryExpr = undefined

transformExpr :: CoreExpr -> UnVarM CoreExpr
transformExpr expr = case expr of
  Case (App (App (App (App (Var f) (Type t)) _) e1) (Var s))
    _ _ [(_, [s', x], e2)] | isNewMutVar f -> do
    p <- canTransformBndr x
    if p then
      let x' = setVarType x t in
      Let <$>
      (NonRec x' <$> transformExpr e1) <*>
      localBndr x x'
      (join $
       localBndr s' <$>
       transformBndr s <*>
       pure (transformExpr e2))
      else transformExprDefault expr
  Case (App (App (App (App (Var f) _) _) (Var x)) (Var s))
    _ _ [(_, [s', a], e)] | isReadMutVar f -> do
    p <- canTransformBndr x
    if p then
      Let <$>
      (NonRec a <$> (Var <$> transformBndr x)) <*>
      join (localBndr s' <$> transformBndr s <*> pure (transformExpr e))
      else transformExprDefault expr
  Case (App (App (App (App (App (Var f) _) _) (Var x)) e1) (Var s))
    s' _ [(DEFAULT, [], e2)] | isWriteMutVar f -> do
    p <- canTransformBndr x
    if p then
      setVarUnique <$> transformBndr x <*> lift getUniqueM >>= \ x' ->
      Let <$>
      (NonRec x' <$> transformExpr e1) <*>
      localBndr x x'
      (join $
       localBndr s' <$>
       transformBndr s <*>
       pure (transformExpr e2))
      else transformExprDefault expr
  _ -> transformExprDefault expr

transformExprDefault :: CoreExpr -> UnVarM CoreExpr
transformExprDefault expr = case expr of
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

transformCase :: CoreExpr -> Var -> Type -> [CoreAlt] -> UnVarM CoreExpr
transformCase e x typ alts =
  Case <$> transformExpr e <*> pure x <*> pure typ <*> transformAlts alts

transformBind :: CoreBind -> UnVarM CoreBind
transformBind bind = case bind of
  NonRec bndr e -> NonRec <$> transformBndr bndr <*> transformExpr e
  Rec binds -> Rec <$> mapM transformTuple binds
    where
      transformTuple (bndr, expr) =
        (,) <$> transformBndr bndr <*> transformExpr expr

transformAlts :: [CoreAlt] -> UnVarM [CoreAlt]
transformAlts = mapM transformAlt

transformAlt :: CoreAlt -> UnVarM CoreAlt
transformAlt (altCon, vars, expr) = (,,) altCon vars <$> transformExpr expr

localBndr :: CoreBndr -> CoreBndr -> UnVarM a -> UnVarM a
localBndr bndr bndr' = local (\ m -> addToUFM m bndr bndr')

transformBndr :: CoreBndr -> UnVarM CoreBndr
transformBndr bndr = asks $ fromMaybe bndr . flip lookupUFM bndr

canTransformBndr :: CoreBndr -> UnVarM Bool
canTransformBndr _ = return True

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
