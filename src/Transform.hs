{-# LANGUAGE FlexibleContexts #-}
module Transform where

import Control.Monad.State

import NarrowingSearch hiding (And)
import Syntax
import Translate
import SearchControl (costGenericSubprob, costGenericBottom)


transformProb :: Bool -> Problem -> Problem
transformProb dosimpnegs ppr =
 let pr = loc2glob ppr
 in  pr {prGlobHyps = map trGlobHyp (prGlobHyps pr), prConjectures = concat (map trConjecture (prConjectures pr))}

 where
 trGlobHyp gh = gh {ghForm = trf, ghGenCost = calcGenCost trf}
  where
   trf = trForm (ghForm gh)

 trConjecture (n, f) =
  case splitproblem (trForm f) of
   [x] -> [(n, trForm f)]
   xs -> map (\(i, x) -> (n ++ "_" ++ show i, x)) (zip [1..length xs] xs)

 trForm :: MFormula -> MFormula
 trForm f = (if dosimpnegs then simpnegs else id) f

 splitproblem :: MFormula -> [MFormula]
 splitproblem x = f x
  where
   f (NotM (C _ Implies [t1, F t2])) = map (\x -> NotM (C nu Implies [t1, F x])) $ f t2
   f (NotM (C _ Forall [T t1, F (NotM (Lam _ _ t2))])) = map (\x -> NotM (C nu Forall [T t1, F $ NotM $ Lam nu t1 x])) $ f t2
   f (NotM (C _ And [F t1, F t2])) = f t1 ++ f t2
   f e = [e]


simpnegs :: MFormula -> MFormula
simpnegs x =
 let ((px, _), _) = f x
 in  px
 where
  f (NotM (C _ Not [F x])) =
    let ((px, wpx), (nx, wnx)) = f x
    in  (choose [(nx, wnx),
                 (cnot px, wpx + 10)],
         choose [(px, wpx),
                 (cnot nx, wnx + 10)])
  f (NotM (C _ Forall  [T t, F (NotM (Lam _ _ x))])) =
    let ((px, wpx), (nx, wnx)) = f x
    in  (choose [(cforall t px, wpx),
                 (cnot (cexists t nx), wnx + 10)],
         choose [(cexists t nx, wnx),
                 (cnot (cforall t px), wpx + 10)])
  f (NotM (C _ Exists [T t, F (NotM (Lam _ _ x))])) = f (cnot (cforall t (cnot x)))
  f (NotM (C _ Or [F x, F y])) =
    let ((px, wpx), (nx, wnx)) = f x
        ((py, wpy), (ny, wny)) = f y
    in  (choose [(cor px py, wpx + wpy),
                 (cimplies nx py, wnx + wpy),
                 (cimplies ny px, wny + wpx),
                 (cnot (cand nx ny), wnx + wny + 10)],
         choose [(cand nx ny, wnx + wny),
                 (cnot (cor px py), wpx + wpy + 10),
                 (cnot (cimplies nx py), wnx + wpy + 10),
                 (cnot (cimplies ny px), wny + wpx + 10)])
  f (NotM (C _ And [F x, F y])) = f (cnot (cor (cnot x) (cnot y)))
  f (NotM (C _ Implies [F x, F y])) = f (cor (cnot x) y)
  -- TODO: traverse eq and app
  f x = ((x, 0), (cnot x, 10))

cnot x = NotM $ C nu Not [F x]
cand x y = NotM $ C nu And [F x, F y]
cor x y = NotM $ C nu Or [F x, F y]
cimplies x y = NotM $ C nu Implies [F x, F y]
cforall t x = NotM $ C nu Forall [T t, F $ NotM $ Lam nu t x]
cexists t x = NotM $ C nu Exists [T t, F $ NotM $ Lam nu t x]

choose ((x, n) : xs) = g x n xs
 where
  g x n [] = (x, n)
  g x n ((y, m) : xs) = if m < n then g y m xs else g x n xs


-- -------------------------

calcGenCost :: MFormula -> GenCost
calcGenCost = g []
 where
  g ctx (NotM f) = case f of
   C _ And [F f1, F f2] -> GCFork (g ctx f1) (g ctx f2)
   C _ Implies [F f1, F f2] -> GCSubProb (gencost ctx f1) (g ctx f2)
   C _ Not [F f] -> GCSubProb (gencost ctx f) GCStop
   C _ Forall [T _, F (NotM (Lam _ _ f))] -> g (True : ctx) f
   C _ Exists [T _, F (NotM (Lam _ _ f))] -> g (False : ctx) f
   C _ Eq [T tp, F f1, F f2] -> case tp of
    NotM Bool -> GCFork (GCSubProb (gencost ctx f1) (g ctx f2)) (GCSubProb (gencost ctx f2) (g ctx f1))
    NotM (Map _ ot) -> g (True : ctx) (NotM $ C nu Eq [T ot, F (qq f1), F (qq f2)])
     where qq f = case f of
                   NotM (Lam _ _ f) -> f
                   NotM (App{}) -> addarg $ dlift 1 f
           addarg (NotM (App _ elr args)) = NotM $ App nu elr $ aa args
           aa (NotM ArgNil) = NotM $ ArgCons (NotM $ App nu (Var 0) (NotM ArgNil)) $ NotM $ ArgNil
           aa (NotM (ArgCons a as)) = NotM $ ArgCons a $ aa as
    _ -> GCStop
   _ -> GCStop

  gencost ctx (NotM (C _ Top [])) = 0
  gencost ctx (NotM (C _ Bot [])) = costGenericBottom
  gencost ctx (NotM (C _ And [F f1, F f2])) = gencost ctx f1 + gencost ctx f2
  gencost ctx (NotM (C _ Or [F f1, F f2])) = min (gencost ctx f1) (gencost ctx f2)
  gencost ctx (NotM (C _ Implies [F _, F f2])) = gencost ctx f2
  gencost ctx (NotM (C _ Not [F f])) = costGenericBottom
  gencost ctx (NotM (C _ Forall [T _, F (NotM (Lam _ _ f))])) = gencost (False : ctx) f
  gencost ctx (NotM (C _ Exists [T _, F (NotM (Lam _ _ f))])) = gencost (False : ctx) f
  gencost ctx f = gc ctx f costGenericSubprob

  gc ctx (NotM f) cr = case f of
   C _ _ xs ->
    let crpart = cr `div` (1 + na xs)
        na [] = 0
        na (T _ : xs) = na xs
        na (F _ : xs) = 1 + na xs
        fs [] = 0
        fs (T _ : xs) = fs xs
        fs (F f : xs) = gc ctx f crpart + fs xs
    in  fs xs
   App _ (Var i) _ | ctx !! i -> cr
   App _ _ xs ->
    let crpart = cr `div` (1 + na xs)
        na (NotM ArgNil) = 0
        na (NotM (ArgCons _ xs)) = 1 + na xs
        fs (NotM ArgNil) = 0
        fs (NotM (ArgCons f xs)) = gc ctx f crpart + fs xs
    in  fs xs
   Lam _ _ f -> gc (False : ctx) f cr

-- -------------------------

loc2glob pr =
 let (conjs, hyps) = runState (mapM gg (prConjectures pr)) (prGlobHyps pr)
 in  pr {prGlobHyps = hyps, prConjectures = conjs}
 where
  gg (n, f) = do
   f <- hh f
   return (n, f)

  hh (NotM (C _ Implies [F f1, F f2])) = do
   hyps <- get
   let id = length hyps
   put (GlobHyp {ghName = "hyp_" ++ show id, ghForm = f1, ghId = id, ghGenCost = GCStop} : hyps)
   hh f2
  hh f = return f

