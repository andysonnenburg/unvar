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

import Control.Monad (MonadPlus (mzero), liftM)
import Control.Monad.Unify

data Term var a = Pure a | Wrap !(var (Term var a))

instance Eq a => MonadUnify var (Term var a) where
  fresh = liftM Wrap freshVar
  x `is` y = unify (\ _ _ -> mzero) x y

atom :: a -> Term var a
atom = Pure

unify :: (Eq a, MonadVar var m) =>
         (a -> a -> m ()) ->
         Term var a -> Term var a -> m ()
unify f t1 t2 = do
  x1 <- semiprune t1
  x2 <- semiprune t2
  case (x1, x2) of
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
    match a b
      | a == b = return ()
      | otherwise = f a b

semiprune :: MonadVar var m => Term var a -> m (Pair (Semipruned var a) (Term var a))
semiprune t0 = case t0 of
  Pure a -> return $! Atom a :* t0
  Wrap var -> go t0 var
  where
    go t var = do
      m <- readVar var
      case m of
        Nothing -> return $! UnwrittenVar var :* t
        Just t'@(Wrap var') -> do
          x@(_ :* t'') <- go t' var'
          writeVar var t''
          return x
        Just (Pure a) -> return $! WrittenVar var a :* t

data Pair a b = !a :* !b

data Semipruned var a
  = Atom a
  | UnwrittenVar !(var (Term var a))
  | WrittenVar !(var (Term var a)) a
