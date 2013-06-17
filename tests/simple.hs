{-# OPTIONS_GHC -fplugin=UnVar #-}
module Main (main) where

import Data.IORef

main :: IO ()
main = do
  x <- newIORef False
  writeIORef x True
  print =<< readIORef x
