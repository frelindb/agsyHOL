module DLList where

import Data.IORef (IORef, newIORef, readIORef)
import qualified Data.IORef as NoUndo (writeIORef)

--import Control.Monad.State (lift)

import Undo


data Node a = Node {nelt :: Maybe a, nnext :: IORef (Node a), nprev :: IORef (Node a)}

type DLList a = Node a

empty :: IO (DLList a)
empty = do
 nextp <- newIORef undefined
 prevp <- newIORef undefined
 let node = Node {nelt = Nothing, nnext = nextp, nprev = prevp}
 NoUndo.writeIORef nextp node
 NoUndo.writeIORef prevp node
 return node

insertBefore :: a -> Node a -> Undo (Node a)
insertBefore x next = do
 prev <- ureadIORef (nprev next)
 nextp <- unewIORef next
 prevp <- unewIORef prev
 let node = Node {nelt = Just x, nnext = nextp, nprev = prevp}
 uwriteIORef (nprev next) node
 uwriteIORef (nnext prev) node
 return node

remove :: Node a -> Undo (Node a)  -- returns next node which can be used with insertBefore to insert new elements at same position
remove node = do
 next <- ureadIORef (nnext node)
 prev <- ureadIORef (nprev node)
 uwriteIORef (nprev next) prev
 uwriteIORef (nnext prev) next
 return next

getNext :: Node a -> IO (Maybe a, Node a)
getNext node = do
 next <- readIORef (nnext node)
 return (nelt next, next)

insertLast :: DLList a -> Node a  -- use as initial node with getNext
insertLast x = x

initVisit :: DLList a -> Node a  -- use as next node with insertBefore to insert at end of list
initVisit x = x

toList :: DLList a -> IO [a]
toList x = f $ initVisit x
 where
  f i = do
   (melt, i) <- getNext i
   case melt of
    Nothing -> return []
    Just elt -> do
     elts <- f i
     return $ elt : elts

{-
test = do
 l <- empty
 let sh = lift $ do
      xs <- toList l
      putStrLn $ show xs
 runUndo $ do
  let i = insertLast l
  insertBefore 1 i
  insertBefore 2 i
  insertBefore 3 i
  sh
  let i = initVisit l
  (Just 1, i) <- lift $ getNext i
  (Just 2, i) <- lift $ getNext i
  i <- remove i
  sh
  insertBefore 4 i
  insertBefore 5 i
  sh
-}

