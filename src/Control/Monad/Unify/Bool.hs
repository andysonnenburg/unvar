{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PatternGuards #-}
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

import Control.Monad (MonadPlus, guard, liftM, liftM2, mzero, when)
import Control.Monad.Fix (mfix)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (evalStateT, get, modify)
import Control.Monad.Unify

import Data.Function (fix)
import Data.List (find)

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

true :: Term var
true = True

false :: Term var
false = False

not :: Term var -> Term var
not t = case t of
  Var _ -> Not t
  True -> False
  False -> True
  Not t' -> t'
  p :&& q -> not p \/ not q
  p :|| q -> not p /\ not q

(/\) :: Term var -> Term var -> Term var
p /\ q = case (p, q) of
  (True, _) -> q
  (False, _) -> False
  (_, True) -> p
  (_, False) -> False
  _ -> p :&& q

(\/) :: Term var -> Term var -> Term var
p \/ q = case (p, q) of
  (True, _) -> True
  (False, _) -> q
  (_, True) -> True
  (_, False) -> p
  _ -> p :|| q

unify :: MonadVar var m => m () -> Term var -> Term var -> m ()
unify m p q = do
  t <- semiprune $ p <+> q
  cc <- unify0 t =<< freeVars t
  whenM (always cc) m

semiprune :: MonadVar var m => Term var -> m (Term var)
semiprune t0@(Var var0) = fix (\ rec t var ->
  readVar var >>= maybe (return t) (\ t' -> case t' of
    Var var' -> do
      t'' <- rec t' var'
      writeVar var t''
      return t''
    _ -> return t)) t0 var0
semiprune t0 = return t0

freeVars :: MonadVar var m => Term var -> m [var (Term var)]
freeVars = liftM (keys . filter snd) . robin [] (fix $ \ rec t xs -> case t of
  Var x
    | any (sameVar x . fst) xs -> return xs
    | otherwise -> readVar x >>= \ m -> case m of
      Nothing -> return $ (x, Prelude.True):xs
      Just t' -> rec t' $ (x, Prelude.False):xs
  True -> return xs
  False -> return xs
  Not t' -> rec t' xs
  p :&& q -> rec p =<< rec q xs
  p :|| q -> rec p =<< rec q xs)

keys :: [(a, b)] -> [a]
keys = map fst

robin :: a -> (b -> a -> c) -> b -> c
robin x f y = f y x

unify0 :: MonadVar var m => Term var -> [var (Term var)] -> m (Term var)
unify0 t [] = return t
unify0 t (x:xs) = do
  t0 <- (x ~> false) t
  t1 <- (x ~> true) t
  x' <- fresh
  writeVar x $! t0 \/ (x' /\ not t1)
  unify0 (t0 /\ t1) xs

(~>) :: MonadVar var m => var (Term var) -> Term var -> Term var -> m (Term var)
x ~> a = flip evalStateT [(x, a)] . fix (\ rec t -> get >>= \ xs -> case t of
  Var x'
    | Just t' <- lookupBy (sameVar x') xs -> return t'
    | otherwise -> lift (readVar x') >>= \ m -> case m of
      Nothing -> return t
      Just t' -> mfix $ \ t'' -> do
        modify ((x', t''):)
        rec t'
  True -> return True
  False -> return False
  Not t' -> liftM not $ rec t'
  p :&& q -> liftM2 (/\) (rec p) (rec q)
  p :|| q -> liftM2 (\/) (rec p) (rec q))

lookupBy :: (a -> Bool) -> [(a, b)] -> Maybe b
lookupBy f = fmap snd . find (f . fst)

always :: MonadVar var m => Term var -> m Bool
always t = do
  p <- eval t
  return $! case p of
    T -> Prelude.True
    I -> Prelude.False
    F -> Prelude.False

eval :: MonadVar var m => Term var -> m Kleene
eval t = case t of
  Var x -> readVar x >>= maybe (return I) (\ t' -> do
    p <- eval t'
    case p of
      T -> do
        writeVar x True
        return T
      I -> return I
      F -> do
        writeVar x False
        return F)
  True -> return T
  False -> return F
  Not t' -> notM $ eval t'
  p :&& q -> eval p `andM` eval q
  p :|| q -> eval p `orM` eval q

data Kleene = T | I | F

notM :: Monad m => m Kleene -> m Kleene
notM m = do
  p <- m
  return $! case p of
    T -> F
    I -> I
    F -> T

andM :: Monad m => m Kleene -> m Kleene -> m Kleene
andM m n = do
  p <- m
  case p of
    T -> n
    I -> do
      q <- n
      return $! case q of
        F -> F
        _ -> I
    F -> return F

orM :: Monad m => m Kleene -> m Kleene -> m Kleene
orM m n = do
  p <- m
  case p of
    T -> return T
    I -> do
      q <- n
      return $! case q of
        T -> T
        _ -> I
    F -> n

(<+>) :: Term var -> Term var -> Term var
p <+> q = (p \/ q) /\ not (p /\ q)

whenM :: Monad m => m Bool -> m () -> m ()
whenM m n = m >>= flip when n
