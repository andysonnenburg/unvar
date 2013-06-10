module Main (main) where

import Data.IORef

import UnVar

{-# ANN main UnVar #-}
main :: IO ()
main = do
  x <- newIORef False
  writeIORef x True
  print =<< readIORef x
