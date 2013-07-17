{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module Control.Monad.Unify.Atom
       ( module Control.Monad.Unify
       , Term
       , atom
       , unify
       ) where

import Control.Monad (MonadPlus, liftM, mzero, when)
import Control.Monad.Unify

import Data.Function (fix)

data Term var a = Pure a | Wrap !(var (Term var a))

instance Eq a => MonadUnify var (Term var a) where
  fresh = liftM Wrap freshVar
  is = unify mzero

atom :: a -> Term var a
atom = Pure

unify :: (Eq a, MonadVar var m) => m () -> Term var a -> Term var a -> m ()
unify m t1 t2 = do
  s1 <- semiprune t1
  s2 <- semiprune t2
  case (s1, s2) of
    (UnwrittenVar var1 :* _, UnwrittenVar var2 :* t2')
      | sameVar var1 var2 -> return ()
      | otherwise -> writeVar var1 t2'
    (UnwrittenVar var1 :* _, WrittenVar _ _ :* t2') -> writeVar var1 t2'
    (WrittenVar _ _ :* t1', UnwrittenVar var2 :* _) -> writeVar var2 t1'
    (WrittenVar var1 a1 :* _, WrittenVar var2 a2 :* t2')
      | sameVar var1 var2 -> return ()
      | otherwise -> do
        match a1 a2
        writeVar var2 $ atom a1
        writeVar var1 t2'
    (UnwrittenVar var1 :* _, Atom _ :* t2') -> writeVar var1 t2'
    (Atom _ :* t1', UnwrittenVar var2 :* _) -> writeVar var2 t1'
    (WrittenVar var1 a1 :* _, Atom a2 :* t2') -> do
      match a1 a2
      writeVar var1 t2'
    (Atom a1 :* t1', WrittenVar var2 a2 :* _) -> do
      match a1 a2
      writeVar var2 t1'
    (Atom a :* _, Atom b :* _) -> match a b
  where
    match a b = when (a /= b) m

semiprune :: MonadVar var m =>
             Term var a -> m (Pair (SemiprunedTerm var a) (Term var a))
semiprune t0 = case t0 of
  Pure a -> return $! Atom a :* t0
  Wrap var0 -> fix (\ rec t var ->
    readVar var >>= (return $! UnwrittenVar var :* t) `maybe` \ t' -> case t' of
      Wrap var' -> do
        s@(_ :* t'') <- rec t' var'
        writeVar var t''
        return s
      Pure a -> return $! WrittenVar var a :* t) t0 var0

data Pair a b = !a :* !b

data SemiprunedTerm var a
  = Atom a
  | UnwrittenVar !(var (Term var a))
  | WrittenVar !(var (Term var a)) a
