{-# LANGUAGE
    DefaultSignatures
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  , StandaloneDeriving
  , UndecidableInstances #-}
{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module Control.Monad.Unify.Atom
       ( MonadVar (..)
       , Term
       , val
       , fresh
       , freeze
       , is
       , toTerm
       , freshTerm
       , fromTerm
       , unify
       ) where

import Control.Applicative
import Control.Monad (MonadPlus (mzero), (>=>), liftM)
import Control.Monad.ST.Safe
import Control.Monad.Trans.Class
import Control.Monad.Trans.ST

import Data.Var.ST

infix 4 `is`

class IsVar var where
  sameVar :: var a -> var a -> Bool

  default sameVar :: Eq (var a) => var a -> var a -> Bool
  sameVar = (==)

class (IsVar var, Monad m) => MonadVar var m | m -> var where
  freshVar :: m (var a)

  lookupVar :: var a -> m (Maybe a)

  assignVar :: var a -> a -> m ()

  default freshVar :: (MonadTrans t, MonadVar var m) => t m (var a)
  freshVar = lift freshVar

  default lookupVar :: (MonadTrans t, MonadVar var m) => var a -> t m (Maybe a)
  lookupVar = lift . lookupVar

  default assignVar :: (MonadTrans t, MonadVar var m) => var a -> a -> t m ()
  assignVar var = lift . assignVar var

newtype WrappedVar var a =
  WrapVar { unwrapVar :: var (Maybe a)
          }

deriving instance Eq (var (Maybe a)) => Eq (WrappedVar var a)

instance IsVar (WrappedVar (STVar s))

instance MonadVar (WrappedVar (STVar s)) (ST s) where
  freshVar = WrapVar <$> newVar Nothing
  lookupVar = readVar . unwrapVar
  assignVar var = writeVar (unwrapVar var) . Just

instance IsVar (WrappedVar (STTVar s m))

instance MonadST m => MonadVar (WrappedVar (STTVar s m)) (STT s m) where
  freshVar = liftM WrapVar $ newVar Nothing
  lookupVar = readVar . unwrapVar
  assignVar var = writeVar (unwrapVar var) . Just

data Term var a = Val a | Var (var (Term var a))

freshTerm :: MonadVar var m => m (Term var a)
freshTerm = liftM Var freshVar

val :: a -> Term var a
val = toTerm

fresh :: MonadVar var m => m (Term var a)
fresh = freshTerm

freeze :: (MonadVar var m, MonadPlus m) => Term var a -> m a
freeze = fromTerm (\ _ -> mzero)

is :: (Eq a, MonadVar var m, MonadPlus m) => Term var a -> Term var a -> m ()
x `is` y = do
  _ <- unify (\ _ _ -> mzero) x y
  return ()

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
        assignVar v1 t2'
        return t2'
    (UnwrittenVar v1 :* _, WrittenVar _ _ :* t2') -> do
      assignVar v1 t2'
      return t2'
    (WrittenVar _ _ :* t1', UnwrittenVar v2 :* _) -> do
      assignVar v2 t1'
      return t1'
    (WrittenVar v1 a1 :* _, WrittenVar v2 a2 :* t2')
      | sameVar v1 v2 -> return t2'
      | otherwise -> do
        match a1 a2
        assignVar v2 $! Val a1
        assignVar v1 t2'
        return t2'
    (UnwrittenVar v1 :* t1', Pure _ :* t2') -> do
      assignVar v1 t2'
      return t1'
    (Pure _ :* t1', UnwrittenVar v2 :* t2') -> do
      assignVar v2 t1'
      return t2'
    (WrittenVar v1 a1 :* t1', Pure a2 :* t2') -> do
      match a1 a2
      assignVar v1 t2'
      return t1'
    (Pure a1 :* t1', WrittenVar v2 a2 :* t2') -> do
      match a1 a2
      assignVar v2 t1'
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
      r <- lookupVar v
      case r of
        Nothing ->
          return $! UnwrittenVar v :* t
        Just t'@(Var v') -> do
          x@(_ :* t'') <- go t' v'
          assignVar v t''
          return x
        Just (Val a) -> return $! WrittenVar v a :* t

data Pair a b = !a :* !b

data Semipruned var a
  = Pure !a
  | UnwrittenVar !(var (Term var a))
  | WrittenVar !(var (Term var a)) a
