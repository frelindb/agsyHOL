{-# LANGUAGE UndecidableInstances, Rank2Types, ExistentialQuantification, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, ScopedTypeVariables #-}

module NarrowingSearch where

import Prelude hiding (fail)
import Data.IORef (IORef, newIORef, readIORef)
import qualified Data.IORef as NoUndo (writeIORef)
import Data.Array
import Control.Monad.State hiding (fail)
import Data.Char

import Undo
import DLList


type Prio = Int

data Prop blk = OK
              | Error String
              | And (MetaEnv (PB blk)) (MetaEnv (PB blk))
              | Cost Int (MetaEnv (PB blk))

data Metavar a blk = Metavar
 {mid :: Int,
  mbind :: IORef (Maybe a),
  mprincpres :: IORef Bool,
  mbinfos :: IORef [blk],
  mobs :: IORef [(Maybe (IORef Bool), MetaEnv (PB blk), Node (Prio, AnyMeta blk), IO String)]
 }

data AnyMeta blk = forall a . Refinable a blk => AnyMeta (Metavar a blk)
                 | NoMeta

instance Eq (Metavar a blk) where
 x == y = mprincpres x == mprincpres y

heteroeq :: Metavar a blk -> Metavar b blk -> Bool
heteroeq x y = mprincpres x == mprincpres y

newMeta :: Int -> IO (Metavar a blk)
newMeta id = do
 x1 <- newIORef Nothing
 x2 <- newIORef False
 x4 <- newIORef []
 x5 <- newIORef []
 return $ Metavar {mid = id, mbind = x1, mprincpres = x2, mbinfos = x4, mobs = x5}

initMeta :: IO (Metavar a blk)
initMeta = do
 m <- newMeta 0
 return m

-- -----------------------

type RefCreateEnv = StateT Int IO

class Refinable a blk | a -> blk where
 refinements :: blk -> [blk] -> Metavar a blk -> IO [(Int, RefCreateEnv a, String)]

newPlaceholder :: RefCreateEnv (Metavar a blk)
newPlaceholder = do
 id <- get
 put (id + 1)
 m <- lift $ newMeta id
 return m

type BlkInfo blk = (Bool, Prio, Maybe blk)  -- Bool - is principal

data MM a blk = NotM a
              | Meta (Metavar a blk)

type MetaEnv = IO

data MB a blk = NotB a
              | forall b . Refinable b blk => Blocked (Metavar b blk) (MetaEnv (MB a blk))
              | Failed String

data PB blk = NotPB (Prop blk)
            | forall b . Refinable b blk => PBlocked (Metavar b blk) (BlkInfo blk) (MetaEnv (PB blk)) (IO String)
            | forall b1 b2 . (Refinable b1 blk, Refinable b2 blk) => PDoubleBlocked (Metavar b1 blk) (Metavar b2 blk) (MetaEnv (PB blk))


gheadc :: Refinable a blk => MM a blk -> (a -> MetaEnv (MB b blk)) -> MetaEnv (MB b blk)
gheadc x f = case x of
 NotM x -> f x
 x@(Meta m) -> do
  bind <- readIORef $ mbind m
  case bind of
   Just x -> f x
   Nothing -> return $ Blocked m (gheadc x f)

gheadp :: Refinable a blk => BlkInfo blk -> IO String -> MM a blk -> (a -> MetaEnv (PB blk)) -> MetaEnv (PB blk)
gheadp blkinfo pr x f = case x of
 NotM x -> f x
 x@(Meta m) -> do
  bind <- readIORef $ mbind m
  case bind of
   Just x -> f x
   Nothing -> return $ PBlocked m blkinfo (gheadp (error "not used") (error "not used") x f) pr  -- blkinfo not needed because will be notb next time

gheadm :: Refinable a blk => BlkInfo blk -> IO String -> Metavar a blk -> (a -> MetaEnv (PB blk)) -> MetaEnv (PB blk)
gheadm blkinfo pr m f = do
 bind <- readIORef $ mbind m
 case bind of
  Just x -> f x
  Nothing -> return $ PBlocked m blkinfo (gheadm (error "not used") (error "not used") m f) pr  -- blkinfo not needed because will be notb next time


cheadc :: MetaEnv (MB a blk) -> (a -> MetaEnv (MB b blk)) -> MetaEnv (MB b blk)
cheadc x f = do
 x' <- x
 case x' of
  NotB x -> f x
  Blocked m x -> return $ Blocked m (cheadc x f)
  Failed msg -> return $ Failed msg

cheadp :: (Prio, Maybe blk) -> IO String -> MetaEnv (MB a blk) -> (a -> MetaEnv (PB blk)) -> MetaEnv (PB blk)
cheadp blkinfo pr x f = do
 x' <- x
 case x' of
  NotB x -> f x
  Blocked m x -> return $ PBlocked m (False, prio, bi) (cheadp (prio, bi) pr x f) pr  -- enabled princ pres again
   where
    (prio, bi) = blkinfo
  Failed msg -> return $ NotPB $ Error msg


mbret :: a -> MetaEnv (MB a blk)
mbret x = return $ NotB x

mbfailed :: String -> MetaEnv (MB a blk)
mbfailed msg = return $ Failed msg

mpret :: Prop blk -> MetaEnv (PB blk)
mpret p = return $ NotPB p

expandbind :: MM a blk -> MetaEnv (MM a blk)
expandbind x = case x of
 NotM{} -> return x
 Meta m -> do
  bind <- readIORef $ mbind m
  case bind of
   Just x -> return $ NotM x
   Nothing -> return x

-- -----------------------

runProp :: MProp blk -> IO String
runProp p = do
 p <- p
 case p of
  PBlocked{} -> return "<blocked>"
  NotPB p ->
   case p of
    OK -> return "OK"
    Error msg -> return $ "\"" ++ msg ++ "\""
    And p1 p2 -> do
     p1 <- runProp p1
     p2 <- runProp p2
     return $ "(" ++ p1 ++ ") & (" ++ p2 ++ ")"
    Cost _ p -> runProp p

-- -----------------------

ok = mpret OK
err s = mpret $ Error s
fail s = return $ Failed s
andp p1 p2 = mpret $ And p1 p2
subtractcost c p = mpret $ Cost c p

type MProp blk = MetaEnv (PB blk) 
type MComp a blk = MetaEnv (MB a blk)

assert :: Bool -> MProp blk
assert True = ok
assert False = err "assertion failed"

-- -----------------------

type HandleSol = IO ()

lowestPrio = 0
highestPrio = 7

defaultCost = 1

-- NOTE: ticks are counted down instead of up and execution stopped when 0 is reached
topSearch :: forall blk . Bool -> IORef Int -> IORef Int -> HandleSol -> blk -> MetaEnv (PB blk) -> Int -> Int -> IO Bool
topSearch interactive ticks nsol hsol envinfo p searchdepth depthinterval = do
 conslist <- empty :: IO (DLList (Prio, AnyMeta blk))
 depthreached <- newIORef False
 stop <- newIORef False
 midcp <- newIORef 1
 localauto <- newIORef False
 depth <- newIORef searchdepth

 let
  r :: forall a . Undo ()
  r = do
   res <- findrefmeta
   case res of
    Nothing -> do  -- sol found (or no principal constraints)
     b <- lift checknoconstraintsleft
     case b of
      True -> do
       depth_ <- ureadIORef depth
       lift $ when (depth_ < depthinterval) $ do
        n <- readIORef nsol
        when (n == 1) $ NoUndo.writeIORef stop True
        NoUndo.writeIORef nsol $! n - 1
        hsol
        when interactive $ getChar >> return ()
      False -> error "no principal constraints"
    Just (prio, AnyMeta m) -> lift $ do
     blinfos <- readIORef (mbinfos m)
     obss <- readIORef (mobs m)
     let
      refine (cost, ref, _) = do
       depth_ <- readIORef depth
       if depth_ < cost + defaultCost then do
         b <- readIORef depthreached
         when (not b) $ NoUndo.writeIORef depthreached True
        else do
         n <- readIORef ticks
         NoUndo.writeIORef ticks $! n - 1
         if (n == 1) then
           NoUndo.writeIORef stop True
          else do
           midc <- readIORef midcp
           (bind, midc') <- runStateT ref midc
           runUndo $ do
            uwriteIORef midcp midc'
            uwriteIORef (mbind m) (Just bind)
            uwriteIORef depth (depth_ - cost - defaultCost)
            res <- recalcs obss
            case res of
             False -> return ()
             True -> r

      f [] = return ()
      f (ref : refs) = do
       refine ref
       s <- readIORef stop
       if s then return () else f refs

      f_inter refs = do
       la <- readIORef localauto
       if la then
         f refs
        else
         loop 0
       where
        loop refi = do
         depth_ <- readIORef depth
         refi <- prState m prio refs refi depth_
         if refi == length refs then
           return ()
          else do
           t1 <- readIORef ticks
           refine (refs !! refi)
           la <- readIORef localauto
           when la $ do
            NoUndo.writeIORef localauto False
            t2 <- readIORef ticks
            putStrLn $ "local ticks: " ++ show (t1 - t2)
            getChar
            return ()
           s <- readIORef stop
           if s then return () else loop (refi + 1)
         
     refs <- refinements envinfo blinfos m
     if interactive then f_inter refs else f refs

  prState m prio refs refi depth = do
   putStr "\x1b[2J\x1b[0;0H"
   hsol
   putStrLn "-----------------------"
   f (initVisit conslist) []
   putStrLn "-----------------------"
   putStrLn $ "?" ++ show (mid m) ++ ", prio: " ++ show prio ++ ", depth: " ++ show depth
   mapM_ (\((cost, ref, pr), i) ->
     putStrLn $ (if i == refi then "--> " else "    ") ++ show (i + 1) ++ " " ++ pr ++ " " ++ show cost
    ) (zip refs [0..])
   when (refi == length refs) $
    putStrLn "--> [back]"
   c <- getChar
   case c of
    _ | isDigit c -> return $ ord c - ord '1'
    '\n' -> return refi
    '\x7f' -> return (length refs)
    '\x1b' -> do
     NoUndo.writeIORef stop True
     return (length refs)
    'a' -> do
     when (refi < length refs) $ NoUndo.writeIORef localauto True
     return refi

   where
    f i vms = do
     (am, i) <- getNext i
     case am of
      Just (prio, m@(AnyMeta{})) -> do
       prMeta i (prio, m)
       f i (m : vms)
      Just (_, NoMeta) -> do
       f i vms
      Nothing -> return ()
    eq (AnyMeta m1) (AnyMeta m2) = heteroeq m1 m2

  prMeta node (prio, AnyMeta m) = do
   pp <- readIORef (mprincpres m)
   blinfos <- readIORef (mbinfos m)
   obss <- readIORef (mobs m)
   putStr $ "?" ++ show (mid m) ++ " -  pp: " ++ show pp ++ ", prio: " ++ show prio ++ " - "
   mapM_ (\(_, _, node', pr) ->
     if nnext node' == nnext node then do
       pp <- pr
       putStrLn pp
      else
       return ()
    ) obss

  findrefmeta :: Undo (Maybe (Prio, AnyMeta blk))
  findrefmeta = lift $ f (initVisit conslist) Nothing
   where
    f i max = do
     (am, i) <- getNext i
     case am of
      Just (prio, am@(AnyMeta m)) ->
       case max of
        Nothing -> f i (Just (prio, am))
        Just (mprio, _) ->
         if prio > mprio then
          f i (Just (prio, am))
         else
          f i max
      Just (_, NoMeta) -> f i max
      Nothing ->
       case max of
        Nothing -> return Nothing
        Just x -> return $ Just x

  checknoconstraintsleft = do
   (x, _) <- getNext $ initVisit conslist
   return $ case x of
    Nothing -> True
    Just _ -> False

  recalcs :: [(Maybe (IORef Bool), MetaEnv (PB blk), Node (Prio, AnyMeta blk), a)] -> Undo Bool
  recalcs [] = return True
  recalcs ((mflag, p, node, _) : ps) = do
   doit <- case mflag of
    Nothing -> return True
    Just flag -> do
     fl <- ureadIORef flag
     if fl then
       return False
      else do
       uwriteIORef flag True
       return True
   case doit of
    True -> do
     iptr <- remove node
     res <- recalc iptr p
     case res of
      False -> return res
      True -> recalcs ps
    False ->
     recalcs ps

  recalc :: Node (Prio, AnyMeta blk) -> MetaEnv (PB blk) -> Undo Bool
  recalc iptr p = do
   depth_ <- lift $ readIORef depth
   f depth_ p  -- limit the recursive calls
   where
    f 0 _ = return False
    f fdep p = do
     res <- lift p
     case res of
      NotPB p -> case p of
       OK -> return True
       Error{} | not interactive -> return False
       Error msg | interactive -> do
        lift (putStrLn msg >> getChar)
        return False
       And p1 p2 -> do
        res <- f (fdep - 1) p1
        case res of
         False -> return res
         True -> f (fdep - 1) p2
       Cost c p -> do
        depth_ <- ureadIORef depth
        if depth_ < c then do
          b <- ureadIORef depthreached
          when (not b) $ lift $ NoUndo.writeIORef depthreached True
          return False
         else do
          uwriteIORef depth (depth_ - c)
          f (fdep - 1) p
      PBlocked m (princ, prio, mbinfo) cont pr -> do
       node <- insertBefore (prio, AnyMeta m) iptr
       umodifyIORef (mobs m) ((Nothing, cont, node, pr) :)
       case mbinfo of
        Just i -> umodifyIORef (mbinfos m) (i :)
        Nothing -> return ()
       oprinc <- ureadIORef (mprincpres m)

       when (not oprinc && princ) $ uwriteIORef (mprincpres m) True

       return True
      PDoubleBlocked m1 m2 cont -> do
       node <- insertBefore ((-1), NoMeta) iptr
       flag <- unewIORef False
       let o = (Just flag, cont, node, return "doubleblocked")
       umodifyIORef (mobs m1) (o :)
       umodifyIORef (mobs m2) (o :)
       return True

 runUndo $ do
  res <- recalc (insertLast conslist) p
  case res of
   False -> return ()  -- immediately false
   True -> r
 b <- readIORef depthreached
 return b

-- ---------------------



