{-# LANGUAGE
    DefaultSignatures
  , ExistentialQuantification
  , FlexibleInstances
  , MultiParamTypeClasses
  , Rank2Types
  , TypeFamilies #-}
{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module Control.Monad.Trans.ST.Trail
       ( MonadST (..)
       , STT
       , runSTT
       , STTVar
       ) where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Logic
import Control.Monad.ST.Safe
import Control.Monad.ST.Lazy.Safe (strictToLazyST)
import qualified Control.Monad.ST.Lazy.Safe as Lazy
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader

import Data.Var.ST

class Monad m => MonadST m where
  type World m

  liftST :: ST (World m) a -> m a

  default liftST :: MonadTrans t => ST (World m) a -> t m a
  liftST = lift . liftST

instance MonadST (ST s) where
  type World (ST s) = s
  liftST = id

instance MonadST (Lazy.ST s) where
  type World (Lazy.ST s) = s
  liftST = strictToLazyST

instance MonadST IO where
  type World IO = RealWorld
  liftST = stToIO

instance MonadST m => MonadST (MaybeT m) where
  type World (MaybeT m) = World m

instance MonadST m => MonadST (ReaderT r m) where
  type World (ReaderT r m) = World m

instance MonadST m => MonadST (LogicT m) where
  type World (LogicT m) = World m

newtype STT s m a =
  STT { unSTT :: ReaderT (Env m) m a
      }

instance Functor m => Functor (STT s m) where
  fmap f = STT . fmap f . unSTT

instance Applicative m => Applicative (STT s m) where
  pure = STT . pure
  f <*> a = STT $ unSTT f <*> unSTT a

instance (MonadST m, Alternative m) => Alternative (STT s m) where
  empty = STT empty
  m <|> n = STT $ unSTT (label *> m) <|> unSTT (backtrack *> n)

instance Monad m => Monad (STT s m) where
  return = STT . return
  m >>= f = STT $ unSTT m >>= unSTT . f
  m >> n = STT $ unSTT m >> unSTT n
  fail = STT . fail

instance MonadST m => MonadST (STT s m) where
  type World (STT s m) = World m
  liftST = STT . liftST

instance (MonadST m, MonadPlus m) => MonadPlus (STT s m) where
  mzero = STT mzero
  m `mplus` n = STT $ unSTT (label >> m) `mplus` unSTT (backtrack >> n)

instance MonadTrans (STT s) where
  lift = STT . lift

instance MonadIO m => MonadIO (STT s m) where
  liftIO = STT . liftIO

label :: MonadST m => STT s m ()
label = STT $ do
  Env labelVar trailVar <- ask
  liftST $ do
    modifyVar' labelVar (+ 1)
    modifyVar' trailVar Label

backtrack :: MonadST m => STT s m ()
backtrack = STT $ do
  Env labelVar trailVar <- ask
  liftST $ do
    modifyVar' labelVar $ subtract 1
    writeVar trailVar =<< go =<< readVar trailVar
  where
    go :: Trail m -> ST (World m) (Trail m)
    go (Write var l a xs) = do
      writeVar var $! Value l a
      go xs
    go (Label xs) =
      return xs
    go Nil =
      return Nil

runSTT :: MonadST m => (forall s . STT s m a) -> m a
runSTT m = do
  r <- liftST $ Env <$> newVar minBound <*> newVar Nil
  runReaderT (unSTT m) r

newtype STTVar s m a =
  STTVar { unSTTVar :: STVar (World m) (Value a)
         } deriving Eq

instance MonadST m => Var (STTVar s m) a (STT s m) where
  newVar a = STT $ do
    Env labelVar _ <- ask
    liftST $ fmap STTVar . newVar =<< Value <$> readVar labelVar <*> pure a
  readVar var = liftST $ do
    Value _ a <- readVar $ unSTTVar var
    return a
  writeVar (STTVar var) a = STT $ do
    Env labelVar trailVar <- ask
    liftST $ do
      l <- readVar labelVar
      Value l' a' <- liftST $ readVar var
      when (l' < l) $ modifyVar' trailVar $ Write var l' a'
      writeVar var $! Value l a

data Env m =
  Env
  {-# UNPACK #-} !(STUVar (World m) Label)
  {-# UNPACK #-} !(STVar (World m) (Trail m))

data Trail m
  = forall a .
    Write
    {-# UNPACK #-} !(STVar (World m) (Value a))
    {-# UNPACK #-} !Label
    a
    !(Trail m)
  | Label !(Trail m)
  | Nil

data Value a = Value {-# UNPACK #-} !Label a

type Label = Int
