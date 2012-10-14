{-# LANGUAGE ExistentialQuantification #-}

module Undo where

import Data.IORef
import Control.Monad.State

data Restore = forall a . Restore (IORef a) a

type Undo = StateT [Restore] IO

ureadIORef :: IORef a -> Undo a
ureadIORef ptr = lift $ readIORef ptr

unewIORef :: a -> Undo (IORef a)
unewIORef v = lift $ newIORef v

uwriteIORef :: IORef a -> a -> Undo ()
uwriteIORef ptr newval = do
 oldval <- ureadIORef ptr
 modify (Restore ptr oldval :)
 lift $ writeIORef ptr newval

umodifyIORef :: IORef a -> (a -> a) -> Undo ()
umodifyIORef ptr f = do
 oldval <- ureadIORef ptr
 modify (Restore ptr oldval :)
 lift $ writeIORef ptr (f oldval)

ureadmodifyIORef :: IORef a -> (a -> a) -> Undo a
ureadmodifyIORef ptr f = do
 oldval <- ureadIORef ptr
 modify (Restore ptr oldval :)
 lift $ writeIORef ptr (f oldval)
 return oldval

runUndo :: Undo a -> IO a
runUndo x = do
 (res, restores) <- runStateT x []
 mapM_ (\(Restore ptr oldval) -> writeIORef ptr oldval) restores  -- reverse order is slower
 return res

