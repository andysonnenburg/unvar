{-# OPTIONS_GHC -fplugin=UnVar #-}
module Main
       ( main
       , mean
       ) where

import Control.Applicative
import Control.Monad
import Control.Monad.ST

import Data.IORef
import Data.Var.ST

main :: IO ()
main = print $ mean [1 .. 10]
-- main = do
--   x <- newIORef False
--   writeIORef x True
--   print =<< readIORef x

mean :: [Double] -> Double
mean xs = runST $ do
  s <- newVar 0 :: ST s (STVar s Double)
  l <- newVar 0 :: ST s (STVar s Int)
  forM_ xs $ \ x -> do
    modifyVar' s (+ x)
    modifyVar' l (+ 1)
  (/) <$> readVar s <*> (fromIntegral <$> readVar l)
