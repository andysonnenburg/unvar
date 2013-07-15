{-# LANGUAGE
    DefaultSignatures
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  , StandaloneDeriving
  , TypeFamilies
  , UndecidableInstances #-}
{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module Control.Monad.Unify
       ( IsVar (..)
       , MonadVar (..)
       , WrappedVar (..)
       , MonadUnify (..)
       ) where

import Control.Applicative
import Control.Monad (MonadPlus, liftM)
import Control.Monad.ST.Safe (ST)
import qualified Control.Monad.ST.Lazy.Safe as Lazy
import Control.Monad.Trans.Class
import Control.Monad.Trans.ST

import Data.Var.Class (newVar)
import qualified Data.Var.Class as Var
import Data.Var.IO (IOVar)
import Data.Var.ST (STVar)

infix 4 `is`

class IsVar var where
  sameVar :: var a -> var a -> Bool

  default sameVar :: Eq (var a) => var a -> var a -> Bool
  sameVar = (==)

class (IsVar var, Monad m) => MonadVar var m | m -> var where
  freshVar :: m (var a)

  readVar :: var a -> m (Maybe a)

  writeVar :: var a -> Maybe a -> m ()

  default freshVar :: (MonadTrans t, MonadVar var m) => t m (var a)
  freshVar = lift freshVar

  default readVar :: (MonadTrans t, MonadVar var m) => var a -> t m (Maybe a)
  readVar = lift . readVar

  default writeVar :: (MonadTrans t, MonadVar var m) => var a -> Maybe a -> t m ()
  writeVar var = lift . writeVar var

class MonadUnify var t | t -> var where
  fresh :: MonadVar var m => m t
  is :: (MonadVar var m, MonadPlus m) => t -> t -> m ()

newtype WrappedVar var a =
  WrapVar { unwrapVar :: var (Maybe a)
          }

deriving instance Eq (var (Maybe a)) => Eq (WrappedVar var a)

instance IsVar (WrappedVar (STVar s))

instance MonadVar (WrappedVar (STVar s)) (ST s) where
  freshVar = WrapVar <$> newVar Nothing
  readVar = Var.readVar . unwrapVar
  writeVar = Var.writeVar . unwrapVar

instance MonadVar (WrappedVar (STVar s)) (Lazy.ST s) where
  freshVar = WrapVar <$> newVar Nothing
  readVar = Var.readVar . unwrapVar
  writeVar = Var.writeVar . unwrapVar

instance IsVar (WrappedVar IOVar)

instance MonadVar (WrappedVar IOVar) IO where
  freshVar = WrapVar <$> newVar Nothing
  readVar = Var.readVar . unwrapVar
  writeVar = Var.writeVar . unwrapVar

instance IsVar (WrappedVar (STTVar s m))

instance ( MonadST m
         , w ~ World m
         ) => MonadVar (WrappedVar (STTVar s w)) (STT s m) where
  freshVar = liftM WrapVar $ newVar Nothing
  readVar = Var.readVar . unwrapVar
  writeVar = Var.writeVar . unwrapVar
