{- |
Copyright   :  (c) Andy Sonnenburg 2013
License     :  BSD3
Maintainer  :  andy22286@gmail.com
-}
module UnVar
       ( module UnVar.Ann
       , plugin
       ) where

import GhcPlugins

import UnVar.Ann

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install
                       }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  reinitializeGlobals
  putMsgS "hello"
  return todo
