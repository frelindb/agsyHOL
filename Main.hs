
import Data.IORef
import System.Environment
import Control.Monad
import System.Timeout
import Control.Concurrent (forkIO, killThread, threadDelay)
import System.IO
import Data.Maybe

import Syntax
import NarrowingSearch
import SearchControl
import Check
import PrintProof
import TPTPSyntax hiding (App, Var, Implies, Forall)
import ParseGlue
import Parser
import Translate
import Transform
import ProofExport


parseFile :: String -> [TPTPInput]
parseFile str =
 case parse str 1 of
  FailP s -> error $ "Parse error: " ++ s
  OkP x -> x

getProb :: String -> String -> IO [ThfAnnotated]
getProb axiomspath filename = do
 file <- readFile filename
 let prob = parseFile file
 expand prob
 where
 expand [] = return []
 expand (Include axfile : xs) = do
  axprob <- getProb axiomspath (axiomspath ++ axfile)
  xs <- expand xs
  return (axprob ++ xs)
 expand (AnnotatedFormula x : xs) = expand xs >>= \xs -> return (x : xs)

itdeepSearch :: (a -> IO Bool) -> Int -> Int -> (Int -> IO a) -> IO ()
itdeepSearch stop depth step f = do
 --putStrLn $ show depth
 res <- f depth
 b <- stop res
 when (not b) $ itdeepSearch stop (depth + step) step f

solveProb :: Bool -> Bool -> Maybe Int -> Problem -> IO Bool
solveProb prodproof inter mdepth prob =
 case inter of
  True ->
   case prConjectures prob of
    [conj] -> ssingconj [conj]
    (conj : _) -> ssingconj [conj]
    _ -> error "not one conjecture"
  False -> do
   res <- timeout (300 {-300-} {-1-} * 1000000) $
    ssingconj (prConjectures prob)
   return $ case res of
    Nothing -> False
    Just ok -> ok
 where
 ssingconj [] = return True
 ssingconj ((name, conj) : conjs) = do
  putStrLn name
  ticks <- newIORef 0  -- 500000
  nsol <- newIORef 1
  prf <- initMeta
  let hsol = {-return ()  -- -}prProof 0 prf >>= putStrLn
--              >> putStrLn "" >> agdaProof prob prf >>= putStrLn
              >> when prodproof (agdaProof prob prf)  --  >>= writeFile ("Proof-" ++ prName prob ++ ".agda"))
      p = andp (checkProof [] (cl conj) prf)
               (sidecontrol prf (SCState {scsCtx = 0, scsHyps = [], scsNewHyp = NewGlobHyps{-, scsRAAok = True-}}))
      stop res = do
       nsol' <- readIORef nsol
       ticks' <- readIORef ticks
       return $ nsol' == 0 || res == False || ticks' == 0
      ss d di = topSearch inter ticks nsol hsol (BIEnv (prGlobHyps prob)) p d di
  case mdepth of
   Just depth -> ss depth (depth + 1) >> return ()
   Nothing -> case inter of
    True -> ss 1000000 (1000000 + 1) >> return ()
    False -> do
     -- dumpstate hsol $
     itdeepSearch stop 999 1000 (\d -> ss d 1000)
     return ()
  ticks <- readIORef ticks
  nsol <- readIORef nsol
  putStrLn $ show (-ticks, nsol)
  hFlush stdout
  if nsol == 0 then
    ssingconj conjs
   else
    return False

getntrProb notransform axiomspath filename = do
 putStrLn filename
 tptpprob <- getProb axiomspath filename
 --putStrLn $ show tptpprob
 let probname = (reverse . takeWhile (/= '/') . drop 2 . reverse) filename
     prob = translateProb probname tptpprob
     trprob = transformProb (not notransform) prob
 return trprob

dooneproblem prodproof inter mdepth check trprob = do
 case check of
  False ->
   solveProb prodproof inter mdepth trprob
  True -> do
--   pprob <- prProblem prob
--   putStrLn $ "translated problem:\n" ++ pprob

   ptrprob <- prProblem trprob
   putStrLn $ "transformed problem:\n" ++ ptrprob

   putStrLn "checking globhyps of transformed problem:"
   okhyps <- mapM (\gh -> do
     putStr $ ghName gh
     res <- runProp (checkForm [] typeBool $ ghForm gh)
     putStrLn $ pres res
     return $ noerrors res
    ) (prGlobHyps trprob)
   putStrLn "checking conjectures of transformed problem:"
   okconjs <- mapM (\(cname, form) -> do
     putStr cname
     res <- runProp (checkForm [] typeBool form)
     putStrLn $ pres res
     return $ noerrors res
    ) (prConjectures trprob)
   return $ and (okhyps ++ okconjs)
 where
  noerrors res = not $ '\"' `elem` res
  pres res =
   if '\"' `elem` res then
    error $ " error: " ++ res
   else
    " ok"

dumpstate y x = do
 let pe = do threadDelay 2000000
             y
             putStrLn ""
             pe
 tid <- forkIO pe
 res <- x
 killThread tid
 return res


main = do
 args <- getArgs
 let (batch, filename, args1) = case args of
      ("-batch" : f : flog : args) -> (Just flog, f, args)
      (f : args) -> (Nothing, f, args)
     (axiomspath, args2) = case args1 of
      ("-idir" : p : args) -> (p, args)
      args -> ("", args)
     (prodproof, args21) = case args2 of
      ("-prf" : args) -> (True, args)
      args -> (False, args)
     (notransform, args22) = case args21 of
      ("-notransform" : args) -> (True, args)
      args -> (False, args)
     (inter, check, args3) = case args22 of
              ("-int" : args) -> if isJust batch then
                                          error "interactive not possible in batch mode"
                                         else (True, False, args)
              ("-check" : args) -> (False, True, args)
              args -> (False, False, args)
     (mdepth, []) = case args3 of
      ("-depth" : depth : args) -> (Just (read depth), args)
      args -> (Nothing, args)
 case batch of
  Nothing -> do
   trprob <- getntrProb notransform axiomspath filename
   ok <- dooneproblem prodproof inter mdepth check trprob
   when (not inter && not check && ok) $ putStrLn "**SUCCESS**"
   return ()
  Just logfilename -> do
   nok <- newIORef (0 :: Int)
   ntot <- newIORef (0 :: Int)
   files <- liftM lines $ readFile filename
   withFile logfilename WriteMode $ \hlogfile -> do
    mapM_ (\filename ->
      let filename' = takeWhile (/= ' ') filename
      in  when (not $ null filename') $ do
       trprob <- getntrProb notransform axiomspath filename'
       ok <- dooneproblem prodproof inter mdepth check trprob
       if ok then do
         n <- readIORef nok
         writeIORef nok $! n + 1
        else
         hPutStrLn hlogfile $ filename ++ " " ++ show (probsize trprob)
       n <- readIORef ntot
       writeIORef ntot $! n + 1
     ) files
    nok <- readIORef nok
    ntot <- readIORef ntot
    putStrLn $ "-----------------------------\n" ++ show nok ++ " / " ++ show ntot ++ " successful"


