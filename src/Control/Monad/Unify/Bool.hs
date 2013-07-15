{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module Control.Monad.Unify.Bool
       ( module Control.Monad.Unify
       , Term
       , true
       , false
       , not
       , (/\)
       , (\/)
       , unify
       ) where

import Control.Monad (MonadPlus, liftM, liftM2, mzero)
import Control.Monad.Unify

import Prelude hiding (Bool (..), not)
import Prelude (Bool)
import qualified Prelude

infixr 3 /\
infixr 2 \/

data Term var
  = Var !(var (Term var))
  | True
  | False
  | Not !(Term var)
  | !(Term var) :&& !(Term var)
  | !(Term var) :|| !(Term var)

instance MonadUnify var (Term var) where
  fresh = liftM Var freshVar
  is = unify mzero

unify :: MonadVar var m => m () -> Term var -> Term var -> m ()
unify m p q = do
  let t = p <+> q
  cc <- unify0 t =<< freeVars t
  if cc then m else return ()

freeVars :: MonadVar var m => Term var -> m [var (Term var)]
freeVars = go []
  where
    go xs t = case t of
      Var x -> maybe
               (return $! if any (sameVar x) xs then xs else x:xs)
               (go xs) =<< readVar x
      True -> return xs
      False -> return xs
      Not t' -> go xs t'
      p :&& q -> flip go p =<< go xs q
      p :|| q -> flip go p =<< go xs q

unify0 :: MonadVar var m => Term var -> [var (Term var)] -> m Bool
unify0 t [] = freeze t
unify0 t (x:xs) = do
  t0 <- (x ~> false) t
  t1 <- (x ~> true) t
  x' <- fresh
  writeVar x $! Just $! t0 \/ (x' /\ not t1)
  unify0 (t0 /\ t1) xs

(~>) :: MonadVar var m => var (Term var) -> Term var -> Term var -> m (Term var)
(x ~> a) t = case t of
  Var x'
    | sameVar x x' -> return a
    | otherwise -> maybe (return t) (x ~> a) =<< readVar x'
  True -> return True
  False -> return False
  Not t' -> liftM Not $ (x ~> a) t'
  p :&& q -> liftM2 (:&&) ((x ~> a) p) ((x ~> a) q)
  p :|| q -> liftM2 (:||) ((x ~> a) p) ((x ~> a) q)

freeze :: MonadVar var m => Term var -> m Bool
freeze t = case t of
  Var x -> maybe (fail "freeze: free var") freeze =<< readVar x
  True -> return Prelude.True
  False -> return Prelude.False
  Not t' -> liftM Prelude.not (freeze t')
  a :&& b -> liftM2 (&&) (freeze a) (freeze b)
  a :|| b -> liftM2 (||) (freeze a) (freeze b)    

true :: Term var
true = True

false :: Term var
false = False

not :: Term var -> Term var
not = Not

(/\) :: Term var -> Term var -> Term var
(/\) = (:&&)

(\/) :: Term var -> Term var -> Term var
(\/) = (:||)

(<+>) :: Term var -> Term var -> Term var
p <+> q = (p \/ q) /\ not (p /\ q)
