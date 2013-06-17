{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module UnVar
       ( plugin
       ) where

import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader

import Data.Maybe

import GhcPlugins

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install
                       }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  reinitializeGlobals
  printPpr todo
  return $ todo ++ [CoreDoPluginPass "unvar" unVar] ++ todo

unVar :: ModGuts -> CoreM ModGuts
unVar guts = do
  binds <- runUnVarM $ mapM transformBind $ mg_binds guts
  return guts { mg_binds = binds }

printPpr :: Outputable a => a -> CoreM ()
printPpr = putMsg . ppr

type UnVarM = ReaderT (UniqFM Var) CoreM

runUnVarM :: UnVarM a -> CoreM a
runUnVarM = flip runReaderT emptyUFM

transformExpr :: CoreExpr -> UnVarM CoreExpr
transformExpr expr = case expr of
  Case expr'@(App (App (App (App (Var newMutVar) (Type t)) _) a) (Var s)) var typ
    alts@[(_, [s', x], b)]
    | isNewMutVar newMutVar -> do
      p <- canTransformBndr x
      if p
        then localBndr s' s $
             Let <$>
             (NonRec (setVarType x t) <$> transformExpr a) <*>
             localBndr x x (transformExpr b)
        else Case <$>
             transformExpr expr' <*>
             pure var <*>
             pure typ <*>
             transformAlts alts
  Case expr'@(App (App (App (App (Var readMutVar) _) _) (Var x)) (Var s)) var typ
    alts@[(_, [s', a], b)]
    | isReadMutVar readMutVar -> do
      p <- canTransformBndr x
      if p
        then localBndr s' s $ do
             x' <- transformBndr x
             Let (NonRec a (Var x')) <$> transformExpr b
        else Case <$>
             transformExpr expr' <*>
             pure var <*>
             pure typ <*>
             transformAlts alts
  Case expr'@(App (App (App (App (App (Var writeMutVar) _) (Type t)) (Var x)) a) (Var s))
    s' typ alts@[(DEFAULT, [], b)]
    | isWriteMutVar writeMutVar -> do
      p <- canTransformBndr x
      if p
        then localBndr s' s $ do
             x' <- transformBndr x
             i <- lift getUniqueM
             let x'' = setVarType (setVarUnique x' i) t
             Let <$>
               (NonRec x'' <$> transformExpr a) <*>
               localBndr x x'' (transformExpr b)
        else Case <$>
             transformExpr expr' <*>
             pure s' <*>
             pure typ <*>
             transformAlts alts
  Var var ->
    Var <$> transformBndr var
  Lit _ ->
    return expr
  App expr' arg ->
    App <$> transformExpr expr' <*> transformExpr arg
  Lam bndr expr' ->
    Lam <$> transformBndr bndr <*> transformExpr expr'
  Let bind expr' ->
    Let <$> transformBind bind <*> transformExpr expr'
  Case expr' b typ alts ->
    Case <$> transformExpr expr' <*> pure b <*> pure typ <*> transformAlts alts
  Cast expr' coercion ->
    Cast <$> transformExpr expr' <*> pure coercion
  Tick tick expr' ->
    Tick tick <$> transformExpr expr'
  Type _ ->
    return expr
  Coercion _ ->
    return expr

transformBind :: CoreBind -> UnVarM CoreBind
transformBind bind = case bind of
  NonRec bndr expr ->
    NonRec <$> transformBndr bndr <*> transformExpr expr
  Rec binds ->
    Rec <$> mapM transformTuple binds
    where
      transformTuple (bndr, expr) = (,) <$> transformBndr bndr <*> transformExpr expr

transformAlts :: [CoreAlt] -> UnVarM [CoreAlt]
transformAlts = mapM transformAlt

transformAlt :: CoreAlt -> UnVarM CoreAlt
transformAlt (altCon, vars, expr) = (,,) altCon vars <$> transformExpr expr

localBndr :: CoreBndr -> CoreBndr -> UnVarM a -> UnVarM a
localBndr bndr bndr' = local (\ m -> go m bndr bndr')
  where
    go m a b = maybe (addToUFM m a b) (go m a) $ lookupUFM m b

transformBndr :: CoreBndr -> UnVarM CoreBndr
transformBndr bndr = asks $ fromMaybe bndr . flip lookupUFM bndr

canTransformBndr :: CoreBndr -> UnVarM Bool
canTransformBndr _ = return True

isNewMutVar :: Var -> Bool
isNewMutVar =
  (&&) <$>
  (== EQ) . stableModuleCmp ghcPrimModule . nameModule . getName <*>
  (== EQ) . compare newMutVarOccName . getOccName

newMutVarOccName :: OccName
newMutVarOccName = mkVarOcc "newMutVar#"

isReadMutVar :: Var -> Bool
isReadMutVar =
  (&&) <$>
  (== EQ) . stableModuleCmp ghcPrimModule . nameModule . getName <*>
  (== EQ) . compare readMutVarOccName . getOccName

readMutVarOccName :: OccName
readMutVarOccName = mkVarOcc "readMutVar#"

isWriteMutVar :: Var -> Bool
isWriteMutVar =
  (&&) <$>
  (== EQ) . stableModuleCmp ghcPrimModule . nameModule . getName <*>
  (== EQ) . compare writeMutVarOccName . getOccName

writeMutVarOccName :: OccName
writeMutVarOccName = mkVarOcc "writeMutVar#"

ghcPrimModule :: Module
ghcPrimModule = mkModule primPackageId (mkModuleName "GHC.Prim")
