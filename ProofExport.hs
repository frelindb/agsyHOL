module ProofExport where

import Data.IORef
import Control.Monad (liftM, when)

import NarrowingSearch hiding (And)
import Syntax
import Check
import Translate

chunksize = 5
multiplefiles = True


data ECtxElt = Vr MType | Hp CFormula
type ECtx = [ECtxElt]

agdaProof :: Problem -> MetaProof -> IO ()
agdaProof prob proof = do
 sis <- newIORef []
 subprfs <- newIORef []
 nsubprf <- newIORef 0

 let
  ticksize i = do
   (n : xs) <- readIORef sis
   writeIORef sis $ (n - i) : xs
   return $ n - i

  eProof :: ECtx -> CFormula -> MetaProof -> IO String
  eProof ctx etyp p = do
   size <- ticksize 1
   if size <= 0 then do
     modifyIORef sis (chunksize :)
     subprf <- eProof ctx etyp p
     modifyIORef sis tail
     subproofidx <- readIORef nsubprf
     writeIORef nsubprf $! subproofidx + 1
     etyp <- eCForm ctx etyp
     ctx <- eCtx ctx
     let subproofname = "subproof-" ++ show subproofidx
         subprfdef = subproofname ++ " : _⊢_ {" ++ show (prIndSets prob + 1) ++ "} " ++ ctx ++ " " ++ etyp ++ "\n" ++ subproofname ++ " = " ++ subprf ++ "\n\n"
     modifyIORef subprfs ((subproofidx, subprfdef) :)
     return subproofname
    else
     prMeta p $ \p -> case p of
      Intro p -> do
       (etyp, ctr) <- headnormalize etyp
       condWrap (ctr > 0) ("(hn-succ " ++ show ctr ++ " _ ") ")" $
        eIntro ctx etyp p
      Elim hyp p -> do
       (hyp1, hyp2, ityp) <- eHyp ctx hyp False
       p <- eProofElim ctx etyp ityp p
       return $ "(" ++ hyp1 ++ " " ++ p ++ hyp2 ++ ")"
      RAA p -> do
       p <- eProof (Hp (CNot etyp) : ctx) (cl formBot) p
       return $ "(raa (~-I " ++ p ++ "))"

  eHyp :: ECtx -> MetaHyp -> Bool -> IO (String, String, CFormula)
  eHyp ctx hyp eqp = do
   b <- readIORef $ mbind hyp
   case b of
    Nothing -> return ("?", "", error "this should not happen")
    Just (Hyp elr ityp) ->
     case elr of
      HVar v -> return (pre ++ prHypVar ctx v, "", ityp)
      HGlob gh -> return (pre ++ prGHypVar ctx (ghName gh) ++"{- " ++ fixname (ghName gh) ++ " -}", "", ityp)
      AC _ qf p -> do
       qf <- eForm ctx $ Meta qf
       p <- eProof ctx (error "AC etyp") p
       return (preac ++ "(!-E " ++ qf ++ " (=>-E " ++ p, "))", ityp)
   where
    pre = if eqp then "step _ _ " else "elim "
    preac = if eqp then "step-ac' _ _ " else "ac' "

  eProofElim :: ECtx -> CFormula -> CFormula -> MetaProofElim -> IO String
  eProofElim ctx etyp ityp p = do
   size <- ticksize 1
   if size <= 0 then do
     modifyIORef sis (chunksize :)
     subprf <- eProofElim ctx etyp ityp p
     modifyIORef sis tail
     subproofidx <- readIORef nsubprf
     writeIORef nsubprf $! subproofidx + 1
     etyp <- eCForm ctx etyp
     ityp <- eCForm ctx ityp
     ctx <- eCtx ctx
     let subproofname = "subproof-" ++ show subproofidx
         subprfdef = subproofname ++ " : _,_⊢_ {" ++ show (prIndSets prob + 1) ++ "} " ++ ctx ++ " " ++ ityp ++ " " ++ etyp ++ "\n" ++ subproofname ++ " = " ++ subprf ++ "\n\n"
     modifyIORef subprfs ((subproofidx, subprfdef) :)
     return subproofname
    else
     prMeta p $ \p -> case p of
      Use p -> do
       p <- eProofEqSimp ctx typeBool etyp ityp p
       return $ "(use " ++ p ++ ")"
      ElimStep p -> do
       (ityp, ctr) <- headnormalize ityp
       condWrap (ctr > 0) ("(hn-ante " ++ show ctr ++ " _ _ ") ")" $
        eElimStep ctx etyp ityp p

  eProofEqElim :: IORef (CFormula, CFormula) -> ECtx -> MType -> CFormula -> CFormula -> CFormula -> MetaProofEqElim -> IO String
  eProofEqElim xx ctx typ lhs rhs ityp p = do
   size <- ticksize 1
   if size <= 0 then do
     modifyIORef sis (chunksize :)
     subprf <- eProofEqElim xx ctx typ lhs rhs ityp p
     modifyIORef sis tail
     subproofidx <- readIORef nsubprf
     writeIORef nsubprf $! subproofidx + 1
     lhs <- eCForm ctx lhs
     rhs <- eCForm ctx rhs
     ityp <- eCForm ctx ityp
     ctx <- eCtx ctx
     let subproofname = "subproof-" ++ show subproofidx
         subprfdef = subproofname ++ " : _,_⊢_==_ {" ++ show (prIndSets prob + 1) ++ "} " ++ ctx ++ " " ++ ityp ++ " " ++ lhs ++ " " ++ rhs ++ "\n" ++ subproofname ++ " = " ++ subprf ++ "\n\n"
     modifyIORef subprfs ((subproofidx, subprfdef) :)
     return subproofname
    else
     prMeta p $ \p -> case p of
      UseEq -> do
       (HNC _ Eq [_, F lhs', F rhs'], ctr) <- headnormalize ityp
       writeIORef xx (lhs', rhs')
       condWrap (ctr > 0) ("(hn-ante-eq " ++ show ctr ++ " _ _ _ ") ")" $
        return "use"
      UseEqSym -> do
       (HNC _ Eq [_, F lhs', F rhs'], ctr) <- headnormalize ityp
       writeIORef xx (rhs', lhs')
       condWrap (ctr > 0) ("(hn-ante-eq " ++ show ctr ++ " _ _ _ ") ")" $
        return "use-sym"
      EqElimStep p -> do
       (ityp, ctr) <- headnormalize ityp
       condWrap (ctr > 0) ("(hn-ante-eq " ++ show ctr ++ " _ _ _ ") ")" $
        eEqElimStep xx ctx typ lhs rhs ityp p

  eEqElimStep :: IORef (CFormula, CFormula) -> ECtx -> MType -> CFormula -> CFormula -> HNFormula -> MetaEqElimStep -> IO String
  eEqElimStep xx ctx typ lhs rhs ityp p =
   prMeta p $ \p -> case p of
    NTEqElimStep p -> eNTElimStep (eProofEqElim xx ctx typ lhs rhs) ctx ityp p

  eElimStep :: ECtx -> CFormula -> HNFormula -> MetaElimStep -> IO String
  eElimStep ctx etyp ityp p =
   prMeta p $ \p -> case p of
    BotE -> return "$false-E"
    NotE p -> do
     let HNC _ Not [F typ] = ityp
     p <- eProof ctx typ p
     return $ "(~-E " ++ p ++ ")"
    OrE p1 p2 -> do
     let HNC _ Or [F typ1, F typ2] = ityp
     p1 <- eProof (Hp typ1 : ctx) (lift 1 etyp) p1
     p2 <- eProof (Hp typ2 : ctx) (lift 1 etyp) p2
     return $ "(||-E (=>-I " ++ p1 ++ ") (=>-I " ++ p2 ++ "))"
    NTElimStep p -> eNTElimStep (eProofElim ctx etyp) ctx ityp p

  eNTElimStep :: (CFormula -> a -> IO String) -> ECtx -> HNFormula -> NTElimStep a -> IO String
  eNTElimStep pr ctx ityp p =
   case p of
    AndEl p -> do
     let HNC _ And [F typ, _] = ityp
     p <- pr typ p
     return $ "(&-E-l " ++ p ++ ")"
    AndEr p -> do
     let HNC _ And [_, F typ] = ityp
     p <- pr typ p
     return $ "(&-E-r " ++ p ++ ")"
    ExistsE p -> do
     _ <- ticksize 2
     let HNC _ Exists [T typ, F cf@(Cl env mf)] = ityp
         ityp' = CApp cf (Cl env $ NotM $ Choice nu typ mf (NotM ArgNil))
     p <- pr ityp' p
     cf <- eCForm ctx cf
     return $ "(?'-E {_} {_} {_} {_} {" ++ cf ++ "} " ++ p ++ ")"
    ImpliesE p1 p2 -> do
     let HNC _ Implies [F typ1, F typ2] = ityp
     p1 <- eProof ctx typ1 p1
     p2 <- pr typ2 p2
     return $ "(=>-E " ++ p1 ++ " " ++ p2 ++ ")"
    ForallE f p -> do
     let HNC _ Forall [_, F cf] = ityp
         ityp' = CApp cf (cl (Meta f))
     f <- eForm ctx $ Meta f
     p <- pr ityp' p
     return $ "(!'-E " ++ f ++ " " ++ p ++ ")"
  {-
    InvBoolExtl p1 p2 -> do
     p1 <- prProof ctx p1
     p2 <- pr p2
     return $ "(inv-bool-extl " ++ p1 ++ " " ++ p2 ++ ")"
    InvBoolExtr p1 p2 -> do
     p1 <- prProof ctx p1
     p2 <- pr p2
     return $ "(inv-bool-extr " ++ p1 ++ " " ++ p2 ++ ")"
    InvFunExt f p -> do
     f <- prForm ctx $ Meta f
     p <- pr p
     return $ "(inv-fun-ext " ++ f ++ " " ++ p ++ ")"
  -}

  -- TODO: Inv_Ext stuff

  eIntro :: ECtx -> HNFormula -> MetaIntro -> IO String
  eIntro ctx etyp p =
   prMeta p $ \p -> case p of
    OrIl p -> do
     let HNC _ Or [F typ, _] = etyp
     p <- eProof ctx typ p
     return $ "(||-I-l " ++ p ++ ")"
    OrIr p -> do
     let HNC _ Or [_, F typ] = etyp
     p <- eProof ctx typ p
     return $ "(||-I-r " ++ p ++ ")"
    AndI p1 p2 -> do
     let HNC _ And [F typ1, F typ2] = etyp
     p1 <- eProof ctx typ1 p1
     p2 <- eProof ctx typ2 p2
     return $ "(&-I " ++ p1 ++ " " ++ p2 ++ ")"
    ExistsI f p -> do
     _ <- ticksize 2
     let HNC _ Exists [T typ, F cf] = etyp
         etyp' = CApp cf (cl (Meta f))
     f <- eForm ctx $ Meta f
     p <- eProof ctx etyp' p
     cf <- eCForm ctx cf
     return $ "(?'-I {_} {_} {_} {_} {" ++ cf ++ "} " ++ f ++ " " ++ p ++ ")"
    ImpliesI p -> do
     let HNC _ Implies [F typ1, F typ2] = etyp
     p <- eProof (Hp typ1 : ctx) (lift 1 typ2) p
     return $ "(=>-I " ++ p ++ ")"
    NotI p -> do
     let HNC _ Not [F typ] = etyp
     p <- eProof (Hp typ : ctx) (cl formBot) p
     return $ "(~-I " ++ p ++ ")"
    ForallI p -> do
     let HNC _ Forall [T typ, F cf] = etyp
         etyp' = CApp (lift 1 cf) (cl $ NotM $ App nu (Var 0) (NotM ArgNil))
     p <- eProof (Vr typ : ctx) etyp' p
     return $ "(!'-I " ++ p ++ ")"
    TopI ->
     return "$true-I"
    EqI p -> do
     let  HNC _ Eq [T typ, F lhs, F rhs] = etyp
     p <- eProofEq ctx typ lhs rhs p
     return $ "(==-I " ++ p ++ ")"

  eProofEq :: ECtx -> MType -> CFormula -> CFormula -> MetaProofEq -> IO String
  eProofEq ctx typ lhs rhs p = do
   size <- ticksize 1
   if size <= 0 then do
     modifyIORef sis (chunksize :)
     subprf <- eProofEq ctx typ lhs rhs p
     modifyIORef sis tail
     subproofidx <- readIORef nsubprf
     writeIORef nsubprf $! subproofidx + 1
     typ <- eType typ
     lhs <- eCForm ctx lhs
     rhs <- eCForm ctx rhs
     ctx <- eCtx ctx
     let subproofname = "subproof-" ++ show subproofidx
         subprfdef = subproofname ++ " : _⊢_∋_==_ {" ++ show (prIndSets prob + 1) ++ "} " ++ ctx ++ " " ++ typ ++ " " ++ lhs ++ " " ++ rhs ++ "\n" ++ subproofname ++ " = " ++ subprf ++ "\n\n"
     modifyIORef subprfs ((subproofidx, subprfdef) :)
     return subproofname
    else
     prMeta p $ \p -> case p of
      Simp p -> do
       p <- eProofEqSimp ctx typ lhs rhs p
       return $ "(simp " ++ p ++ ")"
      Step hyp elimp simpp eqp -> do
       (hyp1, hyp2, ityp) <- eHyp ctx hyp True
       xx <- newIORef (error "this value set by eProofEqElim")
       elimp <- eProofEqElim xx ctx typ lhs rhs ityp elimp
       (lhs', rhs') <- readIORef xx
       simpp <- eProofEqSimp ctx typ lhs lhs' simpp
       eqp <- eProofEq ctx typ rhs' rhs eqp
       return $  "(" ++ hyp1 ++ " " ++ elimp ++ hyp2 ++ " " ++ simpp ++ " " ++ eqp ++ ")"
      BoolExt p1 p2 -> do
       p1 <- eProof (Hp lhs : ctx) (lift 1 rhs) p1
       p2 <- eProof (Hp rhs : ctx) (lift 1 lhs) p2
       return $ "(bool-ext (&-I (=>-I " ++ p1 ++ ") (=>-I " ++ p2 ++ ")))"
      FunExt p -> do
       let NotM (Map it ot) = typ
           lhs' = CApp (lift 1 lhs) (cl $ NotM $ App nu (Var 0) $ NotM $ ArgNil)
           rhs' = CApp (lift 1 rhs) (cl $ NotM $ App nu (Var 0) $ NotM $ ArgNil)
       p <- eProofEq (Vr it : ctx) ot lhs' rhs' p
       return $ "(fun-ext " ++ p ++ ")"

  eProofEqSimp :: ECtx -> MType -> CFormula -> CFormula -> MetaProofEqSimp -> IO String
  eProofEqSimp ctx typ lhs rhs p = do
   (lhs, ctr1) <- headnormalize lhs
   (rhs, ctr2) <- headnormalize rhs
   condWrap (ctr1 > 0) ("(hn-left " ++ show ctr1 ++ " _ _ ") ")" $
    condWrap (ctr2 > 0) ("(hn-right " ++ show ctr2 ++ " _ _ ") ")" $
    prMeta p $ \p -> case p of
     SimpLam em p -> do
      let HNLam _ _ lbdy = lhs
          HNLam _ _ rbdy = rhs
          NotM (Map it ot) = typ
      p <- eProofEq (Vr it : ctx) ot lbdy rbdy p
      return $ "(head-lam" ++ pem em ++ " _ _ _ _ " ++ p ++ ")"
      where
       pem EMNone = ""
       pem EMLeft = "-eta-left"
       pem EMRight = "-eta-right"
     SimpCons Top [] ->
      return "(head-const _ $true)"
     SimpCons Bot [] ->
      return "(head-const _ $false)"
     SimpCons And [p1, p2] -> do
      let HNC _ And [F llhs, F rlhs] = lhs
          HNC _ And [F lrhs, F rrhs] = rhs
      p1 <- eProofEq ctx typ llhs lrhs p1
      p2 <- eProofEq ctx typ rlhs rrhs p2
      return $ "(head-& " ++ p1 ++ " " ++ p2 ++ ")"
     SimpCons Or [p1, p2] -> do
      let HNC _ Or [F llhs, F rlhs] = lhs
          HNC _ Or [F lrhs, F rrhs] = rhs
      p1 <- eProofEq ctx typ llhs lrhs p1
      p2 <- eProofEq ctx typ rlhs rrhs p2
      return $ "(head-|| " ++ p1 ++ " " ++ p2 ++ ")"
     SimpCons Implies [p1, p2] -> do
      let HNC _ Implies [F llhs, F rlhs] = lhs
          HNC _ Implies [F lrhs, F rrhs] = rhs
      p1 <- eProofEq ctx typ llhs lrhs p1
      p2 <- eProofEq ctx typ rlhs rrhs p2
      return $ "(head-=> " ++ p1 ++ " " ++ p2 ++ ")"
     SimpCons Not [p] -> do
      let HNC _ Not [F lt] = lhs
          HNC _ Not [F rt] = rhs
      p <- eProofEq ctx typ lt rt p
      return $ "(head-~ " ++ p ++ ")"
     SimpCons Forall [p] -> do
      let HNC _ Forall [T qtyp, F lqf] = lhs
          HNC _ Forall [_, F rqf] = rhs
      p <- eProofEq ctx (NotM $ Map qtyp typ) lqf rqf p
      return $ "(head-app _ _ _ _ _ _ (simp (head-const _ Π)) " ++ p ++ ")"
     SimpCons Exists [p] -> do
      let HNC _ Exists [T qtyp, F lqf] = lhs
          HNC _ Exists [_, F rqf] = rhs
      p <- eProofEq ctx (NotM $ Map qtyp typ) lqf rqf p
      return $ "(head-~ (simp (head-app _ _ _ _ _ _ (simp (head-const _ Π)) (simp (head-lam _ _ _ _ (simp (head-~ (simp (head-app _ _ _ _ _ _ " ++ p ++ " (simp (head-var _ _ _)))))))))))"
      -- TODO: how to handle the 'weak F' in the def of '?'[_]_' ? Need to keep track of it or solved because var indeces are not explicit?
     SimpCons Eq [p1, p2] -> do
      let HNC _ Eq [T qtyp, F llhs, F rlhs] = lhs
          HNC _ Eq [_, F lrhs, F rrhs] = rhs
      p1 <- eProofEq ctx qtyp llhs lrhs p1
      p2 <- eProofEq ctx qtyp rlhs rrhs p2
      return $ "(head-== " ++ p1 ++ " " ++ p2 ++ ")"
     SimpApp ps -> do
      let HNApp _ elr las = lhs
          HNApp _ _ ras = rhs
          ityp = getelrtype ctx elr
      wrapArgs ityp las ras "(head-var _ _ _)" ps
     SimpChoice p ps -> do
      let HNChoice _ qtyp lqf las = lhs
          HNChoice _ _ rqf ras = rhs
      p <- eProofEq ctx (NotM $ Map qtyp typeBool) lqf rqf p
      wrapArgs qtyp las ras ("(head-app _ _ _ _ _ _ (simp (head-const _ i)) " ++ p ++ ")") ps

   where
    wrapArgs :: MType -> [CArgs] -> [CArgs] -> String -> MetaProofEqs -> IO String
    wrapArgs typ lhs rhs c xs =
     prMeta xs $ \xs -> case xs of
      PrEqNil -> return c
      PrEqCons x xs -> do
       typ <- expandbind typ
       lhs <- headnormalizeargs lhs
       rhs <- headnormalizeargs rhs
       let HNCons lf las = lhs
           HNCons rf ras = rhs
           NotM (Map it ot) = typ
       x <- eProofEq ctx it lf rf x
       wrapArgs ot las ras ("(head-app _ _ _ _ _ _ (simp " ++ c ++ ") " ++ x ++ ")") xs


 pvars <- mapM dovar (prGlobVars prob)
 phyps <- mapM dohyp (prGlobHyps prob)
 pconjs <- case prConjectures prob of {[conj] -> mapM doconj [conj]; _ -> error "not one conjecture"}
 let [(_, tt)] = prConjectures prob
 writeIORef sis [chunksize]
 proof <- eProof [] (cl tt) proof
 subprfs <- readIORef subprfs
 writeFile ("Proof-" ++ prName prob ++ ".agda") $
  "module Proof-" ++ prName prob ++ " where\n" ++
  "\n" ++
  "open import StdLibStuff\n" ++
  "\n" ++
  "open import Syntax\n" ++
  "open import STT\n" ++
  "open import FSC\n" ++
  "open import Soundness\n" ++
  "open import ProofUtilities\n" ++
  "\n" ++
  (if multiplefiles then
    importsubproofs "" proof ++
    "\n"
   else
    "") ++
  concat pvars ++
  concat phyps ++
  concat pconjs ++
  (if multiplefiles then "" else concat (reverse (map snd subprfs))) ++
  "proof : ⊢ " ++ prop2 (prGlobVars prob) ++ "\n" ++
  "proof = sound-top _ " ++ wrapProof2 (prGlobVars prob) proof ++ "\n"
 when multiplefiles $
  mapM_ (\(idx, p) ->
   writeFile ("Proof-" ++ prName prob ++ "-subproof-" ++ show idx ++ ".agda") $
    "module Proof-" ++ prName prob ++ "-subproof-" ++ show idx ++ " where\n" ++
    "\n" ++
    "open import StdLibStuff\n" ++
    "\n" ++
    "open import Syntax\n" ++
    "open import FSC\n" ++
    "open import ProofUtilities\n" ++
    "\n" ++
    importsubproofs (show idx) p ++
    "\n" ++
    p ++ "\n"
  ) subprfs
 where
  importsubproofs :: String -> String -> String
  importsubproofs me s =
   concatMap (\idx ->
    "open import Proof-" ++ prName prob ++ "-subproof-" ++ idx ++ "\n"
   ) $ gg s
   where
    gg s | take 9 s == "subproof-" =
     let (idx, s') = span (\c -> c >= '0' && c <= '9') $ drop 9 s
         sps = gg s'
     in  if elem idx sps || idx == me then sps else (idx : sps)
    gg (c:s) = gg s
    gg [] = []

  globctx = eContext (reverse $ map gvName $ prGlobVars prob)
  dohyp hyp = do
   pform <- eForm [] (ghForm hyp)
   return $
    "HYP-" ++ fixname (ghName hyp) ++ " : Form {" ++ show (prIndSets prob + 1) ++ "} " ++ globctx ++ " $o\n" ++
    "HYP-" ++ fixname (ghName hyp) ++ " = " ++ pform ++ "\n" ++
    "\n"
  doconj (name, form) = do
   pform <- eForm [] form
   return $
    "CONJ-" ++ fixname name ++ " : Form {" ++ show (prIndSets prob + 1) ++ "} " ++ globctx ++ " $o\n" ++
    "CONJ-" ++ fixname name ++ " = " ++ pform ++ "\n" ++
    "\n"
  dovar var = do
   ptype <- eType (gvType var)
   return $
    "VAR-" ++ fixname (gvName var) ++ " : Type " ++ show (prIndSets prob + 1) ++ "\n" ++
    "VAR-" ++ fixname (gvName var) ++ " = " ++ ptype ++ "\n" ++
    "\n"
  [(theconjname, _)] = prConjectures prob

  prop2 (var : vars) = "(![ VAR-" ++ fixname (gvName var) ++ " ] " ++ prop2 vars ++ ")"
  prop2 [] = prop (prGlobHyps prob)
  prop (hyp : hyps) = "(HYP-" ++ fixname (ghName hyp) ++ " => " ++ prop hyps ++ ")"
  prop [] = "CONJ-" ++ fixname theconjname

  wrapProof2 (var : vars) p = "(!-I " ++ wrapProof2 vars p ++ ")"
  wrapProof2 [] p = wrapProof (prGlobHyps prob) p
  wrapProof (hyp : hyps) p = "(=>-I " ++ wrapProof hyps p ++ ")"
  wrapProof [] p = p

  eForm :: ECtx -> MFormula -> IO String
  eForm ctx f =
   expandbind f >>= \f -> case f of
    Meta m -> return "?"
    NotM (Lam _ t bdy) -> do
     pt <- eType t
     bdy <- eForm (Vr t : ctx) bdy
     return $ "(^[ " ++ pt ++ " ] " ++ bdy ++ ")"
    NotM (C _ Top []) ->
     return "$true"
    NotM (C _ Bot []) ->
     return "$false"
    NotM (C _ And [F a1, F a2]) -> do
     a1 <- eForm ctx a1
     a2 <- eForm ctx a2
     return $ "(" ++ a1 ++ " & " ++ a2 ++ ")"
    NotM (C _ Or [F a1, F a2]) -> do
     a1 <- eForm ctx a1
     a2 <- eForm ctx a2
     return $ "(" ++ a1 ++ " || " ++ a2 ++ ")"
    NotM (C _ Implies [F a1, F a2]) -> do
     a1 <- eForm ctx a1
     a2 <- eForm ctx a2
     return $ "(" ++ a1 ++ " => " ++ a2 ++ ")"
    NotM (C _ Not [F a]) -> do
     a <- eForm ctx a
     return $ "(~ " ++ a ++ ")"
    NotM (C _ Forall [T t, F a]) ->
     do
      t <- eType t
      a <- eForm ctx a
      return $ "(!'[ " ++ t ++ " ] " ++ a ++ ")"
    NotM (C _ Exists [T t, F a]) ->
     do
      t <- eType t
      a <- eForm ctx a
      return $ "(?'[ " ++ t ++ " ] " ++ a ++ ")"
    NotM (C _ Eq [T _, F lhs, F rhs]) -> do
     lhs <- eForm ctx lhs
     rhs <- eForm ctx rhs
     return $ "(" ++ lhs ++ " == " ++ rhs ++ ")"
    NotM (App _ elr args) ->
     let pelr = case elr of
                 Var i -> "($ " ++ prVar ctx i ++ " {refl})"
                 Glob gv -> "($ " ++ prGVar ctx (gvName gv) ++ "{- " ++ fixname (gvName gv) ++ " -} {refl})"
     in  wrapArgs pelr args
    NotM (Choice _ typ qf args) ->
     do
      typ <- eType typ
      qf <- eForm ctx qf
      wrapArgs ("(ι' (" ++ typ ++ ") " ++ qf ++ ")") args
   where
    wrapArgs :: String -> MArgs -> IO String
    wrapArgs c xs =
     expandbind xs >>= \xs -> case xs of
      NotM ArgNil -> return c
      NotM (ArgCons x xs) -> do
       x <- eForm ctx x
       wrapArgs ("(" ++ c ++ " · " ++ x ++ ")") xs

  eCForm :: ECtx -> CFormula -> IO String
  eCForm ctx (Cl env f) =
   expandbind f >>= \f -> case f of
    Meta m -> return "?"
    NotM (Lam _ t bdy) -> do
     pt <- eType t
     bdy <- eCForm (Vr t : ctx) (Cl (Skip : env) bdy)
     return $ "(^[ " ++ pt ++ " ] " ++ bdy ++ ")"
    NotM (C _ Top []) ->
     return "$true"
    NotM (C _ Bot []) ->
     return "$false"
    NotM (C _ And [F a1, F a2]) -> do
     a1 <- eCForm ctx (Cl env a1)
     a2 <- eCForm ctx (Cl env a2)
     return $ "(" ++ a1 ++ " & " ++ a2 ++ ")"
    NotM (C _ Or [F a1, F a2]) -> do
     a1 <- eCForm ctx (Cl env a1)
     a2 <- eCForm ctx (Cl env a2)
     return $ "(" ++ a1 ++ " || " ++ a2 ++ ")"
    NotM (C _ Implies [F a1, F a2]) -> do
     a1 <- eCForm ctx (Cl env a1)
     a2 <- eCForm ctx (Cl env a2)
     return $ "(" ++ a1 ++ " => " ++ a2 ++ ")"
    NotM (C _ Not [F a]) -> do
     a <- eCForm ctx (Cl env a)
     return $ "(~ " ++ a ++ ")"
    NotM (C _ Forall [T t, F a]) ->
     do
      t <- eType t
      a <- eCForm ctx (Cl env a)
      return $ "(!'[ " ++ t ++ " ] " ++ a ++ ")"
    NotM (C _ Exists [T t, F a]) ->
     do
      t <- eType t
      a <- eCForm ctx (Cl env a)
      return $ "(?'[ " ++ t ++ " ] " ++ a ++ ")"
    NotM (C _ Eq [T _, F lhs, F rhs]) -> do
     lhs <- eCForm ctx (Cl env lhs)
     rhs <- eCForm ctx (Cl env rhs)
     return $ "(" ++ lhs ++ " == " ++ rhs ++ ")"
    NotM (App _ elr args) -> do
     pelr <- case elr of
              Var i -> case doclos env i of
               Left i -> return $ "($ " ++ prVar ctx i ++ " {refl})"
               Right f -> eCForm ctx f
              Glob gv -> return $ "($ " ++ prGVar ctx (gvName gv) ++ "{- " ++ fixname (gvName gv) ++ " -} {refl})"
     wrapArgs pelr args
    NotM (Choice _ typ qf args) ->
     do
      typ <- eType typ
      qf <- eCForm ctx (Cl env qf)
      wrapArgs ("(ι' (" ++ typ ++ ") " ++ qf ++ ")") args
   where
    wrapArgs :: String -> MArgs -> IO String
    wrapArgs c xs =
     expandbind xs >>= \xs -> case xs of
      NotM ArgNil -> return c
      NotM (ArgCons x xs) -> do
       x <- eCForm ctx (Cl env x)
       wrapArgs ("(" ++ c ++ " · " ++ x ++ ")") xs
  eCForm ctx (CApp c1 c2) = do
   c1 <- eCForm ctx c1
   c2 <- eCForm ctx c2
   return $ "(" ++ c1 ++ " · " ++ c2 ++ ")"
  eCForm ctx (CNot c) = do
   c <- eCForm ctx c
   return $ "(~ " ++ c ++ ")"
  eCForm _ (CHN _) = return "<CHN>"
   

  eCtx :: ECtx -> IO String
  eCtx ctx = dgv "ε" $ prGlobVars prob
   where
    dgv s (x : xs) = do
     x <- eType $ gvType x
     dgv ("(" ++ x ++ " ∷ " ++ s ++ ")") xs
    dgv s [] = dgh s $ prGlobHyps prob
    dgh s (x : xs) = do
     x <- eForm [] $ ghForm x
     dgh ("(" ++ x ++ " ∷h " ++ s ++ ")") xs
    dgh s [] = gc ctx
     where
      gc [] = return s
      gc (Hp f : ctx) = do
       f <- eCForm ctx f
       ctx <- gc ctx
       return $ "(" ++ f ++ " ∷h " ++ ctx ++ ")"
      gc (Vr t : ctx) = do
       t <- eType t
       ctx <- gc ctx
       return $ "(" ++ t ++ " ∷ " ++ ctx ++ ")"


  prGVar :: ECtx -> String -> String
  prGVar (Hp{} : xs) n = prGVar xs n
  prGVar (Vr{} : xs) n = "(next " ++ prGVar xs n ++ ")"
  prGVar [] n = gg (reverse $ prGlobVars prob)
   where
    gg (var : _) | gvName var == n = "this"
    gg (_ : vars) = "(next " ++ gg vars ++ ")"

  prGHypVar :: ECtx -> String -> String
  prGHypVar (Hp{} : xs) n = "(succ " ++ prGHypVar xs n ++ ")"
  prGHypVar (Vr{} : xs) n = "(skip " ++ prGHypVar xs n ++ ")"
  prGHypVar [] n = gg (reverse $ prGlobHyps prob)
   where
    gg (hyp : _) | ghName hyp == n = "zero"
    gg (_ : hyps) = "(succ " ++ gg hyps ++ ")"

  getelrtype :: ECtx -> Elr -> MType
  getelrtype ctx (Var v) = let Vr t = ctx !! v in t
  getelrtype ctx (Glob g) = gvType g


-- ---------------------------------



eType :: MType -> IO String
eType t = 
 expandbind t >>= \t -> case t of
  Meta _ -> return "?"
  NotM (Ind i) -> return $ "($i " ++ prNat (i + 1) ++ ")"
  NotM Bool -> return "$o"
  NotM (Map t1 t2) -> do
   t1 <- eType t1
   t2 <- eType t2
   return $ "(" ++ t1 ++ " > "  ++ t2 ++ ")"

eContext :: [String] -> String
eContext [] = "ε"
eContext (var : vars) = "(VAR-" ++ fixname var ++ " ∷ " ++ eContext vars ++ ")"



prMeta :: MMetavar a -> (a -> IO String) -> IO String
prMeta m prv = do
 b <- readIORef $ mbind m
 case b of
  Nothing -> return "?"
  Just v -> prv v


prVar :: ECtx -> Int -> String
prVar (Hp{} : _) 0 = error "ERROR2"
prVar (Hp{} : xs) n = prVar xs (n - 1)
prVar (Vr{} : _) 0 = "this"
prVar (Vr{} : xs) n = "(next " ++ prVar xs (n - 1) ++ ")"
prVar [] _ = error "ERROR1"

prHypVar :: ECtx -> Int -> String
prHypVar (Hp{} : _) 0 = "zero"
prHypVar (Hp{} : xs) n = "(succ " ++ prHypVar xs (n - 1) ++ ")"
prHypVar (Vr{} : _) 0 = error "ERROR2"
prHypVar (Vr{} : xs) n = "(skip " ++ prHypVar xs (n - 1) ++ ")"
prHypVar [] _ = error "ERROR1"

prNat :: Int -> String
prNat 0 = "zero"
prNat n = "(suc " ++ prNat (n - 1) ++ ")"


fixname [] = []
fixname ('_':xs) = '-':xs
fixname (x:xs) = x : fixname xs

condWrap :: Bool -> String -> String -> IO String -> IO String
condWrap True s1 s2 c = c >>= \c -> return (s1 ++ c ++ s2)
condWrap False _ _ c = c

-- ----------------------------

headnormalize :: CFormula -> IO (HNFormula, CompTrace)
headnormalize f =
 compute f >>= \(NotB x) -> return x

headnormalizeargs :: [CArgs] -> IO HNArgs
headnormalizeargs xs =
 getStackHead xs >>= \(NotB xs) -> return xs


normalize :: CFormula -> IO MFormula
normalize cform =
 compute cform >>= \(NotB (hnform, _)) ->
 case hnform of
  HNC muid c as -> do
   as <- mapM (\a -> case a of
                      T t -> return $ T t
                      F f -> normalize f >>= \f -> return (F f)
              ) as
   return $ NotM $ C muid c as
  HNApp muid elr as -> do
   as <- normas as
   return $ NotM $ App muid elr as
  HNChoice muid t f as -> do
   f <- normalize f
   as <- normas as
   return $ NotM $ Choice muid t f as
  HNLam muid t f -> do
   f <- normalize f
   return $ NotM $ Lam muid t f
 where
  normas as =
   getStackHead as >>= \(NotB hnas) ->
   case hnas of
    HNNil -> return $ NotM ArgNil
    HNCons f as -> do
     f <- normalize f
     as <- normas as
     return $ NotM $ ArgCons f as

