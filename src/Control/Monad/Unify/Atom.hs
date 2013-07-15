{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module Control.Monad.Unify.Atom
       ( module Control.Monad.Unify
       , Term
       , val
       , freeze
       , toTerm
       , fromTerm
       , unify
       ) where

import Control.Monad (MonadPlus (mzero), (>=>), liftM)
import Control.Monad.Unify

data Term var a = Val a | Var !(var (Term var a))

instance Eq a => MonadUnify var (Term var a) where
  fresh = liftM Var freshVar
  x `is` y = do
    _ <- unify (\ _ _ -> mzero) x y
    return ()

val :: a -> Term var a
val = toTerm

freeze :: (MonadVar var m, MonadPlus m) => Term var a -> m a
freeze = fromTerm (\ _ -> mzero)

toTerm :: a -> Term var a
toTerm = Val

fromTerm :: MonadVar var m => (var (Term var a) -> m a) -> Term var a -> m a
fromTerm f = semiprune >=> \ x -> case x of
  Pure a :* _ -> return a
  UnwrittenVar v :* _ -> f v
  WrittenVar _ a :* _ -> return a

unify :: (Eq a, MonadVar var m) =>
         (a -> a -> m ()) ->
         Term var a -> Term var a -> m (Term var a)
unify f t1 t2 = do
  x1 <- semiprune t1
  x2 <- semiprune t2
  case (x1, x2) of
    (UnwrittenVar v1 :* _, UnwrittenVar v2 :* t2')
      | sameVar v1 v2 -> return t2'
      | otherwise -> do
        writeVar v1 $ Just t2'
        return t2'
    (UnwrittenVar v1 :* _, WrittenVar _ _ :* t2') -> do
      writeVar v1 $ Just t2'
      return t2'
    (WrittenVar _ _ :* t1', UnwrittenVar v2 :* _) -> do
      writeVar v2 $ Just t1'
      return t1'
    (WrittenVar v1 a1 :* _, WrittenVar v2 a2 :* t2')
      | sameVar v1 v2 -> return t2'
      | otherwise -> do
        match a1 a2
        writeVar v2 $ Just $ val a1
        writeVar v1 $ Just t2'
        return t2'
    (UnwrittenVar v1 :* t1', Pure _ :* t2') -> do
      writeVar v1 $ Just t2'
      return t1'
    (Pure _ :* t1', UnwrittenVar v2 :* t2') -> do
      writeVar v2 $ Just t1'
      return t2'
    (WrittenVar v1 a1 :* t1', Pure a2 :* t2') -> do
      match a1 a2
      writeVar v1 $ Just t2'
      return t1'
    (Pure a1 :* t1', WrittenVar v2 a2 :* t2') -> do
      match a1 a2
      writeVar v2 $ Just t1'
      return t2'
    (Pure a :* t1', Pure b :* _) -> do
      match a b
      return t1'
  where
    match a b
      | a == b = return ()
      | otherwise = f a b

semiprune :: MonadVar var m => Term var a -> m (Pair (Semipruned var a) (Term var a))
semiprune t0 = case t0 of
  Val a -> return $! Pure a :* t0
  Var v -> go t0 v
  where
    go t v = do
      r <- readVar v
      case r of
        Nothing -> return $! UnwrittenVar v :* t
        Just t'@(Var v') -> do
          x@(_ :* t'') <- go t' v'
          writeVar v $ Just t''
          return x
        Just (Val a) -> return $! WrittenVar v a :* t

data Pair a b = !a :* !b

data Semipruned var a
  = Pure a
  | UnwrittenVar !(var (Term var a))
  | WrittenVar !(var (Term var a)) a
