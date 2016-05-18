import System.Environment
import System.Exit
import System.Process
import Data.IORef
import Control.Monad
import System.Timeout
import Data.Maybe

import GetFullProgName
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
import ProofExportTPTP




-- ---------------------------------

getProb :: String -> String -> IO (ParseResult [ThfAnnotated])
getProb axiomspath filename = do
 file <- readFile filename
 case parse file 1 of
  FailP err -> return $ FailP err
  OkP prob ->
   expand prob
   where
   expand [] = return $ OkP []
   expand (Include axfile : xs) = do
    axprob <- getProb axiomspath (axiomspath ++ axfile)
    case axprob of
     FailP err -> return $ FailP $ "in " ++ axiomspath ++ axfile ++ ": " ++ err
     OkP axprob -> do
      xs <- expand xs
      case xs of
       FailP err -> return $ FailP err
       OkP xs -> return $ OkP (axprob ++ xs)
   expand (AnnotatedFormula x : xs) = do
    xs <- expand xs
    case xs of
     FailP err -> return $ FailP err
     OkP xs -> return $ OkP (x : xs)

-- ---------------------------------

itdeepSearch :: (a -> IO Bool) -> Int -> Int -> (Int -> IO a) -> IO ()
itdeepSearch stop depth step f = do
 res <- f depth
 b <- stop res
 when (not b) $ itdeepSearch stop (depth + step) step f

solveProb :: Bool -> Maybe Int -> Maybe Int -> Problem -> IO (Maybe [(String, MetaProof)])
solveProb saveproofs inter mdepth prob = do
 prfs <- newIORef []
 let
  doconjs [] = do
   prfs <- readIORef prfs
   return $ Just prfs
  doconjs ((name, conj) : conjs) = do
   ticks <- newIORef 0
   nsol <- newIORef 1
   prf <- initMeta
   let hsol = when saveproofs $ do
               prfcpy <- expandmetas prf
               modifyIORef prfs ((name, prfcpy) :)
       p d = andp (checkProof d [] (cl conj) prf)
                  (sidecontrol prf (SCState {scsCtx = 0, scsHyps = [], scsNewHyp = NewGlobHyps}))
       stop res = do
        nsol' <- readIORef nsol
        return $ nsol' == 0 || res == False
       ss d di = topSearch (isJust inter) ticks nsol hsol (BIEnv (prGlobHyps prob)) (p d) d di
   case mdepth of
    Just depth ->
     ss depth (depth + 1) >> return ()
    Nothing -> case isJust inter of
     True ->
      ss 100000000 (100000000 + 1) >> return ()
     False ->
      itdeepSearch stop 999 1000 (\d -> ss d 1000)
   nsol <- readIORef nsol
   if nsol == 0 then
     doconjs conjs
    else
     return Nothing
 case inter of
  Just idx ->
   doconjs [prConjectures prob !! idx]
  Nothing ->
   doconjs (prConjectures prob)

-- ---------------------------------


data CLArgs = CLArgs {
 problemfile :: String,
 fproof :: Bool,
 finteractive :: Maybe Int,
 fnotransform :: Bool,
 fagdaproof :: Bool,
 ftptpproof :: Bool,
 ftimeout :: Maybe Int,
 fcheck :: Bool,
 fdepth :: Maybe Int,
 fincludedir :: String,
 fshowproblem :: Bool
}

doit args = do
 tptpprob <- getProb (fincludedir args) (problemfile args)
 case tptpprob of
  FailP err -> do
   szs_status args "Error" "parse error"
   putStrLn err
  OkP tptpprob -> do
   let probname = (reverse . takeWhile (/= '/') . drop 2 . reverse) (problemfile args)
       prob = translateProb probname tptpprob
       trprob = transformProb (not (fnotransform args)) prob
   when (fshowproblem args) $ do
    when (not (fnotransform args)) $ do
     pprob <- prProblem prob
     putStrLn $ "non-transformed problem:\n" ++ pprob
    ptrprob <- prProblem trprob
    putStrLn $ "problem:\n" ++ ptrprob

   case fcheck args of
    False -> case prConjectures trprob of
     [] -> szs_status args "Error" "no conjecture to prove"
     _ -> do
      res <- solveProb (fproof args || (fagdaproof args && isNothing (finteractive args)) || ftptpproof args) (finteractive args) (fdepth args) trprob
      case res of
       Just prfs -> do
        szs_status args "Theorem" ""  -- solution found
        when (fproof args) $ do
         putStrLn $ "% SZS output start Proof for " ++ problemfile args
         putStrLn $ "The transformed problem consists of the following conjectures:"
         putStrLn $ concatMap (\x -> ' ' : fst x) (reverse prfs)
         mapM_ (\(name, prf) ->
           putStrLn ("\nProof for " ++ name ++ ":") >> prProof 0 prf >>= putStrLn
          ) $ reverse prfs
         putStrLn $ "% SZS output end Proof for " ++ problemfile args
        when (fagdaproof args && isNothing (finteractive args)) $ do
         putStrLn $ "The following top-level files were created:"
         mapM_ (\(name, prf) ->
           agdaProof trprob name prf
          ) $ reverse prfs
        when (ftptpproof args) $ tptpproof tptpprob prob trprob (reverse prfs)
       Nothing -> szs_status args "GaveUp" ""  -- exhaustive search
    True -> do
     when (fshowproblem args) $ putStrLn "checking globhyps:"
     okhyps <- mapM (\gh -> do
       res <- runProp (checkForm [] typeBool $ ghForm gh)
       when (fshowproblem args) $ putStrLn $ ghName gh ++ pres res
       return $ noerrors res
      ) (prGlobHyps trprob)

     when (fshowproblem args) $ putStrLn "checking conjectures:"
     okconjs <- mapM (\(cname, form) -> do
       res <- runProp (checkForm [] typeBool form)
       when (fshowproblem args) $ putStrLn $ cname ++ pres res
       return $ noerrors res
      ) (prConjectures trprob)

     case and (okhyps ++ okconjs) of
      True -> putStrLn "check OK"
      False -> putStrLn "check FAILED"

     where
      noerrors res = not $ '\"' `elem` res
      pres res =
       if '\"' `elem` res then
        error $ " error: " ++ res
       else
        " ok"

szs_status args status comment =
 putStrLn $ "% SZS status " ++ status ++ " for " ++ problemfile args ++ (if null comment then "" else (" : " ++ comment))


main = do
 args <- getArgs
 case consume "--safe-mode" args of
  Nothing ->
   case ["--help"] == args of
    False ->
     case parseargs args of
      Just args ->
       case ftimeout args of
        Nothing ->
         doit args
        Just seconds -> do
         res <- timeout (seconds * 1000000) $ doit args
         case res of
          Just () -> return ()
          Nothing -> szs_status args "Timeout" ""
      Nothing -> do
       putStrLn "command argument error\n"
       printusage
    True ->
     printusage
  Just args ->
   case parseargs args of
    Nothing -> do
     putStrLn "command argument error\n"
     printusage
    Just pargs -> do
     prgname <- getFullProgName
     (exitcode, out, err) <-
      readProcessWithExitCode
       prgname
       args
       ""
     case exitcode of
      ExitSuccess ->
       return ()
      ExitFailure code ->
       szs_status pargs "Error" ("program stopped abnormally, exitcode: " ++ show code)
     putStrLn out
     putStrLn err

parseargs = g (CLArgs {problemfile = "", fproof = False, finteractive = Nothing, fnotransform = False, fagdaproof = False, ftptpproof = False, ftimeout = Nothing, fcheck = False, fdepth = Nothing, fincludedir = "", fshowproblem = False})
 where
  g a [] = if null (problemfile a) then Nothing else Just a
  g a ("--proof" : xs) = g (a {fproof = True}) xs
  g a ("--interactive" : n : xs) = g (a {finteractive = Just (read n)}) xs
  g a ("--no-transform" : xs) = g (a {fnotransform = True}) xs
  g a ("--agda-proof" : xs) = g (a {fagdaproof = True}) xs
  g a ("--tptp-proof" : xs) = g (a {ftptpproof = True}) xs
  g a ("--time-out" : n : xs) = g (a {ftimeout = Just (read n)}) xs
  g a ("--check" : xs) = g (a {fcheck = True}) xs
  g a ("--depth" : n : xs) = g (a {fdepth = Just (read n)}) xs
  g a ("--include-dir" : s : xs) = if null (fincludedir a) then g (a {fincludedir = s}) xs else Nothing
  g a ("--show-problem" : xs) = g (a {fshowproblem = True}) xs

  g a (x : xs) = if null (problemfile a) then g (a {problemfile = x}) xs else Nothing

consume y [] = Nothing
consume y (x : xs) | x == y = Just xs
consume y (x : xs) | otherwise =
 case consume y xs of
  Just xs -> Just (x : xs)
  Nothing -> Nothing 

printusage = putStr $
 "usage:\n" ++
 "agsyHOL <flags> file <flags>\n" ++
 " file is a TPTP THF problem file.\n" ++
 " flags:\n" ++
 "  --safe-mode      Catches unhandled errors.\n" ++
 "  --proof          Output a proof (in internal format, one proof for each conjecture\n" ++
 "                   of the transformed problem).\n" ++
 "  --interactive n  Do interactive search for subproblem n (n=0,1,2..).\n" ++
 "                   Use --show-problem to see the list of subproblems.\n" ++
 "  --no-transform   Do not transform problem. (Normally the number of negations is minimized.)\n" ++
 "  --agda-proof     Save agda proof files named Proof-<problem_name>-<conjecture_name>.agda and\n" ++
 "                   Proof-<problem_name>-<conjecture_name>-<nn>.agda in current directory.\n" ++
 "                   In order to check the proof with agda, run it on all files listed in the output.\n" ++
 "                   Note that the agda files in the soundness directory must be in scope.\n" ++
 "  --time-out n     Set timeout in seconds. (default: no time out)\n" ++
 "  --check          Just check the problem for well formedness.\n" ++
 "  --depth n        Set search depth. (default: iterated deepening for auto mode (start depth: 999, step: 1000),\n" ++
 "                   unlimited depth for interactive mode)\n" ++
 "  --include-dir p  Set path to axiom files.\n" ++
 "  --show-problem   Display original and transformed problem in internal format.\n" ++
 "                   Combined with --check also show check failure details.\n" ++
 "  +RTS .. -RTS     Give general ghc run time system options, e.g. -t which outputs time and memory usage information.\n" ++
 "  --help           Show this help.\n"

