module Translate where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

import NarrowingSearch hiding (And)
import qualified TPTPSyntax as T
import Syntax
import PrintProof


data TrState = TrState {trsIndSets :: Map String Int,
                        trsGlobVars :: Map String GlobVar,
                        trsDefinitions :: Map String T.Form,
                        trsGlobHyps :: Map String GlobHyp,
                        trsConjectures :: [(String, MFormula)]}

translateProb :: String -> [T.ThfAnnotated] -> Problem
translateProb probname pr =
 let st = execState (mapM_ trdecl pr) (TrState {trsIndSets = Map.empty, trsGlobVars = Map.empty,
                                                trsDefinitions = Map.empty, trsGlobHyps = Map.empty,
                                                trsConjectures = []})
 in  Problem {prName = probname, prIndSets = Map.size (trsIndSets st), prGlobVars = Map.elems (trsGlobVars st), prGlobHyps = Map.elems (trsGlobHyps st), prConjectures = trsConjectures st}

trdecl :: T.ThfAnnotated -> State TrState ()
trdecl (T.ThfAnnotated _ T.Type (T.Typed (T.Const name) (T.DefType "tType")) T.NoAnnotation) =
 modify $ \st -> st {trsIndSets = Map.insert name (Map.size $ trsIndSets st) (trsIndSets st)}
trdecl (T.ThfAnnotated _ T.Type (T.Typed (T.Const name) typ) T.NoAnnotation) = do
 typ <- trtype (error $ "not in a conjecture, in " ++ name) typ
 modify $ \st -> st {trsGlobVars = Map.insert name (GlobVar {gvName = name, gvType = typ, gvId = Map.size (trsGlobVars st)}) (trsGlobVars st)}
trdecl (T.ThfAnnotated _ T.Definition (T.Bin T.Equal (T.Const name) form) T.NoAnnotation) = do
 modify $ \st -> st {trsDefinitions = Map.insert name form (trsDefinitions st)}
trdecl (T.ThfAnnotated name role form T.NoAnnotation) | role `elem` [T.Axiom, T.Lemma, T.Hypothesis] = do
 form <- trform (error $ "not in a conjecture, in " ++ name) [] form
 modify $ \st -> st {trsGlobHyps = Map.insert name (GlobHyp {ghName = name, ghForm = form, ghId = Map.size (trsGlobHyps st), ghGenCost = GCStop}) (trsGlobHyps st)}
trdecl (T.ThfAnnotated name T.Conjecture form T.NoAnnotation) = do
 form <- pretrform name form
 modify $ \st -> st {trsConjectures = (name, form) : trsConjectures st}


pretrform :: String -> T.Form -> State TrState MFormula
pretrform cname = f
 where
  f (T.Quant T.Forall ((v, Just (T.DefType "tType")):vs) x) = do
   modify $ \st -> st {trsIndSets = Map.insert (cname ++ "." ++ v) (Map.size $ trsIndSets st) (trsIndSets st)}
   f (T.Quant T.Forall vs x)
  f (T.Quant T.Forall [] x) =
   f x
  f x = trform cname [] x

trform :: String -> [(String, MType)] -> T.Form -> State TrState MFormula
trform cname = f
 where
  f ctx x = case x of
   T.Bin T.Or x1 x2 -> do
    x1 <- f ctx x1
    x2 <- f ctx x2
    return $ NotM $ C nu Or [F x1, F x2]
   T.Bin T.App (T.Bin T.App (T.UnTerm T.UnOr) x1) x2 -> f ctx (T.Bin T.Or x1 x2)
   T.Bin T.And x1 x2 -> do
    x1 <- f ctx x1
    x2 <- f ctx x2
    return $ NotM $ C nu And [F x1, F x2]
   T.Bin T.App (T.Bin T.App (T.UnTerm T.UnAnd) x1) x2 -> f ctx (T.Bin T.And x1 x2)
   T.UnTerm T.UnAnd ->
    return $ NotM $ Lam nu (NotM Bool) (NotM $ Lam nu (NotM Bool) (NotM $ C nu And [F (NotM $ App nu (Var 1) (NotM ArgNil)), F (NotM $ App nu (Var 0) (NotM ArgNil))]))
   T.Bin T.Implies x1 x2 -> do
    x1 <- f ctx x1
    x2 <- f ctx x2
    return $ NotM $ C nu Implies [F x1, F x2]
   T.Bin T.App (T.Bin T.App (T.UnTerm T.UnImplies) x1) x2 -> f ctx (T.Bin T.Implies x1 x2)
   T.Bin T.LeftImplies x1 x2 -> f ctx (T.Bin T.Implies x2 x1)
   T.Bin T.Equal x1 x2 -> do
    t <- typeinfer cname ctx x1
    x1 <- f ctx x1
    x2 <- f ctx x2
    return $ NotM $ C nu Eq [T t, F x1, F x2]
   T.Bin T.NotEqual x1 x2 -> do
    x <- f ctx (T.Bin T.Equal x1 x2)
    return $ NotM $ C nu Not [F x]
   T.Bin T.Equiv x1 x2 -> do
    x1 <- f ctx x1
    x2 <- f ctx x2
    return $ NotM $ C nu And [F (NotM $ C nu Implies [F x1, F x2]), F (NotM $ C nu Implies [F x2, F x1])]
   T.Bin T.NotEquiv x1 x2 -> do
    x <- f ctx (T.Bin T.Equiv x1 x2)
    return $ NotM $ C nu Not [F x]
   T.Un T.Not x -> do
    x <- f ctx x
    return $ NotM $ C nu Not [F x]
   T.Bin T.App (T.UnTerm T.Not) x -> f ctx (T.Un T.Not x)
   T.UnTerm T.Not ->
    return $ NotM $ Lam nu (NotM Bool) (NotM $ C nu Not [F (NotM $ App nu (Var 0) (NotM ArgNil))])
   T.Quant _ [] x -> f ctx x
   T.Quant T.Forall ((v,Just t):vs) x -> do
    t <- trtype cname t
    vsx <- f ((v, t) : ctx) (T.Quant T.Forall vs x)
    return $ NotM $ C nu Forall [T t, F $ NotM $ Lam nu t vsx]
   T.Bin T.App (T.UnTerm T.UnForall) p -> do
    NotM (Map ti (NotM Bool)) <- typeinfer cname ctx p
    p <- f ((v, ti) : ctx) (T.Bin T.App p (T.Var v))
    return $ NotM $ C nu Forall [T ti, F $ NotM $ Lam nu ti p]
    where
     v = ":" ++ show (length ctx)
   T.Un T.UnForall p ->
    f ctx (T.Bin T.App (T.UnTerm T.UnForall) p)
   T.Quant T.Exists ((v,Just t):vs) x -> do
    t <- trtype cname t
    vsx <- f ((v, t) : ctx) (T.Quant T.Exists vs x)
    return $ NotM $ C nu Exists [T t, F $ NotM $ Lam nu t vsx]
   T.Bin T.App (T.UnTerm T.UnExists) p -> do
    NotM (Map ti (NotM Bool)) <- typeinfer cname ctx p
    p <- f ((v, ti) : ctx) (T.Bin T.App p (T.Var v))
    return $ NotM $ C nu Exists [T ti, F $ NotM $ Lam nu ti p]
    where
     v = ":" ++ show (length ctx)
   T.Un T.UnExists p ->
    f ctx (T.Bin T.App (T.UnTerm T.UnExists) p)
   T.Quant T.LambdaAbs ((v,Just t):vs) x -> do
    t <- trtype cname t
    vsx <- f ((v, t) : ctx) (T.Quant T.LambdaAbs vs x)
    return $ NotM $ Lam nu t vsx
   T.DefType "true" -> return $ NotM $ C nu Top []
   T.DefType "false" -> return $ NotM $ C nu Bot []
   T.Var v ->
    return $ NotM $ App nu (Var (idxof v ctx)) (NotM ArgNil)
   T.Const v -> do
    defs <- gets trsDefinitions
    case Map.lookup v defs of
     Just d ->
      trform v [] d
     Nothing -> do
      gvars <- gets trsGlobVars
      return $ NotM $ App nu (Glob (gvars !!! v)) (NotM ArgNil)
   T.Bin T.App x1 x2 -> do
    x1 <- f ctx x1
    x2 <- f ctx x2
    case x1 of
     NotM (Lam _ _ bdy) ->
      return $ dsub x2 bdy
     NotM (App _ elr args) ->
      return $ NotM $ App nu elr (argSnoc args x2)
     NotM (C _ c as) -> error $ "trform.App: " ++ show ("", c, length as)
   _ -> error $ "trform: " ++ show (cname, x)

argSnoc xs y = argsConcat xs (NotM $ ArgCons y $ NotM ArgNil)

argsConcat (NotM ArgNil) ys = ys
argsConcat (NotM (ArgCons x xs)) ys = NotM $ ArgCons x (argsConcat xs ys)

idxof y = f 0
 where
  f _ [] = error $ "Var not in scope: " ++ y
  f i ((x, _) : _) | x == y = i
  f i (_ : xs) = f (i + 1) xs


trtype :: String -> T.Form -> State TrState MType
trtype cname = f
 where
 f x = case x of
  T.Bin T.Map x1 x2 -> do
   x1 <- f x1
   x2 <- f x2
   return $ NotM $ Map x1 x2
  T.DefType "i" -> return $ NotM $ Ind (-1)
  T.DefType "o" -> return $ NotM Bool
  T.DefType "tType" -> error "tType should only occur on toplevel"
  T.Var v -> do
   indsets <- gets trsIndSets
   return $ NotM $ Ind $ indsets !!! (cname ++ "." ++ v)
  T.Const v -> do
   indsets <- gets trsIndSets
   return $ NotM $ Ind $ indsets !!! v

typeinfer :: String -> [(String, MType)] -> T.Form -> State TrState MType
typeinfer cname = f
 where
 f ctx x =
  case x of
   T.Var v ->
    let t = case lookup v ctx of
             Just t -> t
             Nothing -> error $ "typeinfer.Var " ++ show (cname, map fst ctx, v)
    in  return t
   T.Const v -> do
    gvars <- gets trsGlobVars
    return $ gvType $ gvars !!! v
   T.Bin T.App x1 x2 -> do
    NotM (Map _ t) <- f ctx x1
    return t
   T.Quant T.LambdaAbs [] x -> f ctx x
   T.Quant T.LambdaAbs ((v, Just ti) : vs) x -> do
    ti <- trtype cname ti
    to <- f ((v, ti) : ctx) $ T.Quant T.LambdaAbs vs x
    return $ NotM $ Map ti to
   T.Quant T.Forall _ _ -> return $ NotM Bool
   T.Quant T.Exists _ _ -> return $ NotM Bool
   T.Bin T.Or _ _ -> return $ NotM Bool
   T.Bin T.And _ _ -> return $ NotM Bool
   T.Bin T.Equal _ _ -> return $ NotM Bool
   T.DefType "true" -> return $ NotM Bool
   T.DefType "false" -> return $ NotM Bool
   T.UnTerm T.UnAnd -> return $ NotM $ Map (NotM Bool) (NotM $ Map (NotM Bool) (NotM Bool))
   T.Un T.Not _ -> return $ NotM Bool
   _ -> error $ "typeinfer: " ++ show x

dsub :: MFormula -> MFormula -> MFormula
dsub s = rr 0
 where
  rr i (NotM f) = case f of
   Lam _ t bdy -> NotM $ Lam nu t (rr (i + 1) bdy)
   C _ c args -> NotM $ C nu c (map ra args)
    where
     ra (F f) = F $ rr i f
     ra a@(T{}) = a
   App _ elr args ->
    case elr of
     Var v ->
      if v == i then
       betared (dlift i s) (ras args)
      else if v > i then
       NotM $ App nu (Var (v - 1)) (ras args)
      else
       NotM $ App nu elr (ras args)
     Glob{} ->
      NotM $ App nu elr (ras args)
    where
     ras (NotM ArgNil) = NotM ArgNil
     ras (NotM (ArgCons x xs)) = NotM $ ArgCons (ra x) (ras xs)

     ra = rr i
     betared f args = case f of
      NotM (Lam _ _ bdy) ->
       case args of
        NotM (ArgCons a args) -> betared (dsub a bdy) args
        NotM ArgNil -> f
      NotM (App _ elr args') ->
       NotM $ App nu elr (args' `argsConcat` args)
      _ ->
       case args of
        NotM ArgNil -> f

dlift :: Int -> MFormula -> MFormula
dlift 0 = \x -> x
dlift i = rr 0
 where
  rr j (NotM f) = NotM $ case f of
   Lam _ t bdy -> Lam nu t (rr (j + 1) bdy)
   C _ c args -> C nu c (map ra args)
    where
     ra (F f) = F $ rr j f
     ra a@(T{}) = a
   App _ elr args ->
    case elr of
     Var v ->
      if v >= j then
       App nu (Var (v + i)) (ras args)
      else
       App nu elr (ras args)
     Glob{} ->
      App nu elr (ras args)
    where
     ras (NotM ArgNil) = NotM ArgNil
     ras (NotM (ArgCons x xs)) = NotM $ ArgCons (ra x) (ras xs)

     ra = rr j

(!!!) :: (Ord a, Show a) => Map a b -> a -> b
f !!! x = case Map.lookup x f of
           Just y -> y
           Nothing -> error $ "not found: " ++ show x

