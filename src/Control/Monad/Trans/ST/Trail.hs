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
       , RealWorld
       , STT
       , runSTT
       , STTVar
       ) where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Logic
import Control.Monad.Fix (MonadFix (mfix))
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
  STT { unSTT :: ReaderT (Env s (World m)) m a
      }

instance Functor m => Functor (STT s m) where
  fmap f = STT . fmap f . unSTT

instance Applicative m => Applicative (STT s m) where
  pure = STT . pure
  f <*> a = STT $ unSTT f <*> unSTT a

instance (MonadST m, Alternative m) => Alternative (STT s m) where
  empty = STT empty
  m <|> n = STT $ unSTT (pushLabel *> m) <|> unSTT (popLabel *> n)

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
  m `mplus` n = STT $ unSTT (pushLabel >> m) `mplus` unSTT (popLabel >> n)

instance MonadFix m => MonadFix (STT s m) where
  mfix f = STT $ mfix (unSTT . f)

instance MonadTrans (STT s) where
  lift = STT . lift

instance MonadIO m => MonadIO (STT s m) where
  liftIO = STT . liftIO

pushLabel :: MonadST m => STT s m ()
pushLabel = STT $ do
  Env labelVar trailVar <- ask
  liftST $ do
    modifyVar' labelVar (+ 1)
    modifyVar' trailVar Label

popLabel :: MonadST m => STT s m ()
popLabel = STT $ do
  Env labelVar trailVar <- ask
  liftST $ do
    modifyVar' labelVar $ subtract 1
    writeVar trailVar =<< go =<< readVar trailVar
  where
    go :: Trail s w -> ST w (Trail s w)
    go (Write labelVar var label a xs) = do
      writeVar labelVar label
      writeVar var a
      go xs
    go (Label xs) = return xs
    go Nil = return Nil

runSTT :: MonadST m => (forall s . STT s m a) -> m a
runSTT m = do
  r <- liftST $ Env <$> newVar minBound <*> newVar Nil
  runReaderT (unSTT m) r

data STTVar s w a =
  STTVar
  {-# UNPACK #-} !(STUVar w (Label s))
  {-# UNPACK #-} !(STVar w a) deriving Eq

instance (MonadST m, w ~ World m) => Var (STTVar s w) a (STT s m) where
  newVar a = STT $ do
    env <- ask
    liftST $ do
      label <- readLabel env
      STTVar <$> newVar label <*> newVar a
  readVar (STTVar _ var) = liftST $ readVar var
  writeVar (STTVar labelVar var) a = STT $ do
    env <- ask
    liftST $ do
      label <- readLabel env
      label' <- readVar labelVar
      when (label' /= label) $ do
        modifyTrail' env . Write labelVar var label' =<< readVar var
        writeVar labelVar label
      writeVar var a

data Env s w =
  Env
  {-# UNPACK #-} !(STUVar w (Label s))
  {-# UNPACK #-} !(STVar w (Trail s w))

readLabel :: Env s w -> ST w (Label s)
readLabel (Env labelVar _) = readVar labelVar

modifyTrail' :: Env s w -> (Trail s w -> Trail s w) -> ST w ()
modifyTrail' (Env _ trailVar) = modifyVar' trailVar

data Trail s w
  = forall a .
    Write
    {-# UNPACK #-} !(STUVar w (Label s))
    {-# UNPACK #-} !(STVar w a)
    {-# UNPACK #-} !(Label s)
    a
    !(Trail s w)
  | Label !(Trail s w)
  | Nil

type Label s = Int
