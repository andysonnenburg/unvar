{-# LANGUAGE DeriveDataTypeable #-}
{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module UnVar.Ann (UnVar (..)) where

import Data.Data (Data, Typeable)

data UnVar = UnVar deriving (Typeable, Data)
