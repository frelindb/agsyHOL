{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}

module SearchControl where

import Control.Monad

import NarrowingSearch hiding (And)
import Syntax


instance Refinable Proof Blk where
 refinements _ _ _ = return $
   [(0, newPlaceholder >>= \m -> return (Intro m), "Intro"),
    (0, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> return (Elim m1 m2), "Elim"),
    (costRAA, newPlaceholder >>= \m -> return (RAA m), "RAA")
   ]

instance Refinable Hyp Blk where
 refinements (BIEnv globhyps) [BICtx ctx] _ = return $ hyps 0 ctx ++ map ghyp globhyps ++
  [(costAC, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> newPlaceholder >>= \m3 -> return (Hyp (AC m1 m2 m3) (CApp (cl $ Meta m2) (cl $ NotM $ Choice nu (Meta m1) (Meta m2) (NotM ArgNil)))), "AC")]
  where
   hyps _ [] = []
   hyps i (VarExt _ : ctx) = hyps (i + 1) ctx
   hyps i (HypExt p : ctx) =
    (costVar, return (Hyp (HVar i) (lift (i + 1) p)), "Hyp " ++ show i) : hyps (i + 1) ctx
   ghyp gh =
    (costGlobHyp, return (Hyp (HGlob gh) (cl $ ghForm gh)), "Hyp " ++ ghName gh)

instance Refinable Intro Blk where
 refinements _ [BIForm f] _ = return $
  case f of
   HNC _ Or _ ->
    [(0, newPlaceholder >>= \m -> return (OrIl m), "OrIl"),
     (0, newPlaceholder >>= \m -> return (OrIr m), "OrIr")]
   HNC _ And _ ->
    [(0, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> return (AndI m1 m2), "AndI")]
   HNC _ Exists _ ->
    [(0, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> return (ExistsI m1 m2), "ExistsI")]
   HNC _ Implies _ ->
    [(0, newPlaceholder >>= \m -> return (ImpliesI m), "ImpliesI")]
   HNC _ Not _ ->
    [(0, newPlaceholder >>= \m -> return (NotI m), "NotI")]
   HNC _ Forall _ ->
    [(0, newPlaceholder >>= \m -> return (ForallI m), "ForallI")]
   HNC _ Top _ ->
    [(0, return TopI, "TopI")]
   HNC _ Eq _ ->
    [(0, newPlaceholder >>= \m -> return (EqI m), "EqI")]
   _ -> []

instance Refinable ProofElim Blk where
 refinements _ _ _ = return $
  [(0, newPlaceholder >>= \m -> return (Use m), "Use"),
   (0, newPlaceholder >>= \m -> return (ElimStep m), "ElimStep")
  ]

instance Refinable ElimStep Blk where
 refinements _ [BIForm f] _ = return $
  case f of
   HNC _ Bot _ ->
    [(0, return BotE, "BotE")]
   HNC _ Not _ ->
    [(0, newPlaceholder >>= \m -> return (NotE m), "NotE")]
   HNC _ Or _ ->
    [(costOrE, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> return (OrE m1 m2), "OrE")]
   _ -> refNTElimStep NTElimStep f newPlaceholder

instance Refinable ProofEqElim Blk where
 refinements _ _ _ = return $
  [(0, return UseEq, "UseEq"),
   (0, return UseEqSym, "UseEqSym"),
   (0, newPlaceholder >>= \m -> return (EqElimStep m), "EqElimStep")]

instance Refinable EqElimStep Blk where
 refinements _ [BIForm f] _ = return $
  refNTElimStep NTEqElimStep f newPlaceholder

refNTElimStep c f cep =
 case f of
  HNC _ And _ ->
   [(0, cep >>= \m -> return (c $ AndEl m), "AndEl"),
    (0, cep >>= \m -> return (c $ AndEr m), "AndEr")]
  HNC _ Exists _ ->
   [(0, cep >>= \m -> return (c $ ExistsE m), "ExistsE")]
  HNC _ Implies _ ->
   [(0, newPlaceholder >>= \m1 -> cep >>= \m2 -> return (c $ ImpliesE m1 m2), "ImpliesE")]
  HNC _ Forall _ ->
   [(0, newPlaceholder >>= \m1 -> cep >>= \m2 -> return (c $ ForallE m1 m2), "ForallE")]
  HNC _ Eq _ ->
   [(0, newPlaceholder >>= \m1 -> cep >>= \m2 -> return (c $ InvBoolExtl m1 m2), "InvBoolExtl"),
    (0, newPlaceholder >>= \m1 -> cep >>= \m2 -> return (c $ InvBoolExtr m1 m2), "InvBoolExtr"),
    (0, newPlaceholder >>= \m1 -> cep >>= \m2 -> return (c $ InvFunExt m1 m2), "InvFunExt")]
  _ -> []

instance Refinable ProofEq Blk where
 refinements _ [] _ = return $
  [(0, newPlaceholder >>= \m -> return (Simp m), "Simp"),
   (0{-1000-}, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> newPlaceholder >>= \m3 -> newPlaceholder >>= \m4 ->
       return (Step m1 m2 m3 m4), "Step") , (costBoolExt, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> return (BoolExt m1 m2), "BoolExt"),
   (costFunExt, newPlaceholder >>= \m -> return (FunExt m), "FunExt")]

instance Refinable ProofEqSimp Blk where
 refinements _ [BIFormHead fh] _ = return $
  case fh of
   FHLamLam -> [(0, newPlaceholder >>= \m -> return (SimpLam EMNone m), "SimpLam EMNone")]
   FHLamApp -> [(0, newPlaceholder >>= \m -> return (SimpLam EMRight m), "SimpLam EMRight")]
   FHAppLam -> [(0, newPlaceholder >>= \m -> return (SimpLam EMLeft m), "SimpLam EMLeft")]
   FHC c ->
    [(0, replicateM (nprf c) newPlaceholder >>= \ms -> return (SimpCons c ms), "SimpCons")]
    where
     nprf Top = 0
     nprf Bot = 0
     nprf And = 2
     nprf Or = 2
     nprf Implies = 2
     nprf Not = 1
     nprf Forall = 1
     nprf Exists = 1
     nprf Eq = 2
   FHApp ->
    [(0, newPlaceholder >>= \m -> return (SimpApp m), "SimpApp")]
   FHChoice ->
    [(0, newPlaceholder >>= \m -> newPlaceholder >>= \m2 -> return (SimpChoice m m2), "SimpChoice")]

instance Refinable ProofEqs Blk where
 refinements _ [BISimpArgs cons] _ = return $
  case cons of
   False -> [(0, return PrEqNil, "SimpApp/ChoiceArgs-Nil")]
   True -> [(0, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> return (PrEqCons m1 m2), "SimpApp/ChoiceArgs-Cons")]

instance Refinable Type Blk where
 refinements _ [] _ = return []
 refinements _ (BIUnifyType typ : _) _ = return $
  [(0, return typ, "some given type")]

instance Refinable Formula Blk where
 refinements _ info mm =
  case gg info of
   Just (BIUnifyForm uids opp env) -> return $
    case opp of
     HNLam{} -> gen
     HNC muid c args ->
      let (uid, cost) = gmuid muid
      in  (cost, cargs args >>= \margs -> return (C uid c margs), "C " ++ show c)
          : gen
      where
       cargs [] = return []
       cargs (arg : args) = do
        marg <- case arg of
         F _ -> newPlaceholder >>= \m -> return (F $ Meta m)
         T _ -> newPlaceholder >>= \m -> return (T $ Meta m)
        margs <- cargs args
        return (marg : margs)
     HNApp muid (Var v) _ ->
      case univar env v of
       Just v ->
        let (uid, cost) = gmuid muid
        in  (cost, newPlaceholder >>= \m -> return (App uid (Var v) (Meta m)), "App " ++ show v)
            : gen
       Nothing ->
        gen
     HNApp muid elr@(Glob gv) _ ->
      let (uid, cost) = gmuid muid
      in  (cost, newPlaceholder >>= \m -> return (App uid elr (Meta m)), "App " ++ gvName gv)
          : gen
     HNChoice muid _ _ _ ->
      let (uid, cost) = gmuid muid
      in  (cost, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> newPlaceholder >>= \m3 ->
                 return (Choice uid (Meta m1) (Meta m2) (Meta m3)), "Choice")
          : gen
    where
     gmuid muid = case muid of
      Just uid -> (muid, hocost + if uid `elem` uids then costUnifyCircular else 0)
      Nothing -> (Just $ mid mm, hocost)
     hocost = if any issub env then costUnifyHO else 0
     issub (Sub{}) = True
     issub _ = False
     gen = map (\v -> (0, newPlaceholder >>= \m -> return (App nu (Var v) (Meta m)), "App " ++ show v)) (subsvars env) ++
           (case hh info of
             Nothing -> []
             Just (BICheckForm typ) -> case typ of
              Map t1 _ -> [(0, newPlaceholder >>= \m -> return (Lam nu t1 (Meta m)), "Lam")]
              _ -> [])
   Nothing ->
    case hh info of
     Nothing -> return []
     Just (BICheckForm typ) ->
      if computed info then
       case typ of
        Bool -> return [(0, return (C nu Top []), "Top"), (0, return (C nu Bot []), "Bot")]
        Map t1 _ -> return [(0, newPlaceholder >>= \m -> return (Lam nu t1 (Meta m)), "Lam")]
        _ -> return []
      else
       return [(0, return (Choice nu (NotM typ) (NotM $ Lam nu (NotM typ) $ NotM $ C nu Top []) (NotM ArgNil)), "choice_elt")]
  where
   gg [] = Nothing
   gg (x@(BIUnifyForm{}) : _) = Just x
   gg (_ : xs) = gg xs
   hh [] = Nothing
   hh (x@(BICheckForm {}) : _) = Just x
   hh (_ : xs) = hh xs
   computed [] = False
   computed (BIComputed : _) = True
   computed (_ : xs) = computed xs


instance Refinable Args Blk where
 refinements _ _ _ = return $
  [(0, return ArgNil, "ArgNil"),
   (0, newPlaceholder >>= \m1 -> newPlaceholder >>= \m2 -> return (ArgCons (Meta m1) (Meta m2)), "ArgCons")]

-- --------------------------------------------------

prioProof, prioIntro, prioHyp, prioProofElim, prioProofEqSimp, prioElimStep, prioEqElimStep, prioProofEqElim, prioProofEq, prioUnifyForm, prioUnifyType, prioDecompFormUnknown, prioUnknownType, prioCheckFormUnknownType, prioCheckForm, prioUnknownArgs, prioUnknownInferredType, prioCheckFormArgs, prioCheckType, prioUnknownGoal :: Int
prioProof = 5
prioIntro = 6
prioHyp = 6
prioProofElim = 6
prioElimStep = 6
prioEqElimStep = 6
prioProofEqElim = 6
prioProofEq = 7
prioProofEqSimp = 8

prioDecompFormUnknown = 6
prioUnknownType = 1
prioUnifyForm = 8
prioUnifyType = 10

prioCheckFormUnknownType = 1
prioUnknownInferredType = 1
prioCheckForm = 1
prioCheckFormArgs = 1
prioCheckType = 1
prioUnknownGoal = 1

prioUnknownArgs = 8

prioNo = 0


costVar = 1  -- 10  -- 25  -- 50  -- 200  -- 100
costGlobHyp = 300  -- 400  -- 300  -- 200  -- 50  -- 100  -- 500
costElrUsedAgain = 600  -- 400  -- 600  -- 1000

costRAA = 1000  -- 1200  -- 600  -- 800  -- 1000
costAC = 1800  -- 2000  -- 1800  -- 1200  -- 1500
costOrE = 300  -- 200  -- 300  -- 600  -- 1000
costBoolExt = 1200  -- 800  -- 1000
costFunExt = 1200  -- 800  -- 1000
costUnifyCircular = 1000  -- 500  -- 1000
costUnifyHO = 100  -- 50  -- 100  -- 200

costStep = 1000  -- 1200  -- 800  -- 600  -- 1000

costGenericSubprob, costGenericBottom :: Int
costGenericSubprob = 300  -- 500  -- 300  -- 1000
costGenericBottom = 1000  -- 600  -- 1000




pbc :: String -> IO String
pbc = return


-- -------------------------------

data NewHypState = NewGlobHyps | NewHyp Int (Maybe (MetaHyp, MetaProofElim)) | NoNewHyp

newHyp st = st {scsNewHyp = NewHyp (scsCtx st) Nothing}
noNewHyp st = st {scsNewHyp = NoNewHyp}

data SCState = SCState {scsCtx :: Int, scsHyps :: [HElr], scsNewHyp :: NewHypState}

sidecontrol :: MetaProof -> SCState -> MetaEnv MPB
sidecontrol prf st = scprf prf st
 where
  scprf prf st =
   gheadm (False, prioNo, Nothing) (pbc "sidecontrol") prf $ \prf -> case prf of
    Intro prf -> scintro prf st
    Elim hyp prf ->
     gheadm (False, prioNo, Nothing) (pbc "sidecontrol") hyp $ \(Hyp elr _) ->
     travHyp elr st $ scelim prf
     where
      scelim prf gc st =
       gheadm (False, prioNo, Nothing) (pbc "sidecontrol") prf $ \prf -> case prf of
        Use prf -> sceqsimp prf (noNewHyp st)
        ElimStep prf -> scestep prf gc st

      scestep prf gc st =
       gheadm (False, prioNo, Nothing) (pbc "sidecontrol") prf $ \prf -> case prf of
        BotE -> recentHypOk st
        NotE prf -> mpret $ Cost gccost $ andp (recentHypOk st) (scprf prf (noNewHyp st))
         where gccost = case gc of
                         GCSubProb x GCStop -> x
                         GCLocalHyp -> 0
        OrE prf1 prf2 ->
         andp (recentHypOk st) (
         updateNewHypnCheckOrder st $ \st ->
          andp (extCtx st $ scprf prf1)
               (extCtx st $ scprf prf2))
        NTElimStep prf -> scntestep scelim prf gc st

      recentHypOk st = case scsNewHyp st of
       NewGlobHyps -> ok
       NewHyp ii _ ->
        cheadp (prioNo, Nothing) (pbc "sidecontrol") (mostLocalHyp hyp prf) $ \mlh ->
        let newii = if scsCtx st - 1 - mlh < 0 then (-1) else (scsCtx st - 1 - mlh)
        in
         if newii >= ii then
          ok
         else
          err $ "recent hyp not used" ++ show (newii, ii)
       NoNewHyp -> err "no recent hyp"

      updateNewHypnCheckOrder st c = case scsNewHyp st of
       NewGlobHyps -> c $ st {scsNewHyp = NewHyp (-1) (Just (hyp, prf))}
       NewHyp ii Nothing -> c $ st {scsNewHyp = NewHyp ii (Just (hyp, prf))}
       NewHyp ii (Just (prevhyp, prevprf)) ->
        cheadp (prioNo, Nothing) (pbc "sidecontrol") (mostLocalHyp hyp prf) $ \mlh ->
        let newii = if scsCtx st - 1 - mlh < 0 then (-1) else (scsCtx st - 1 - mlh)
            newst = st {scsNewHyp = NewHyp newii (Just (hyp, prf))}
        in
         if newii == ii then
          andp
           (cheadp (prioNo, Nothing) (pbc "sidecontrol") (compareElim 1 prevhyp prevprf hyp prf) $ \o ->
            case o of
             LT -> ok
             _ -> err "nested cases not ordered correctly"
           )
           (c newst)
         else
          c newst
       NoNewHyp -> err "no recent hyp"

    RAA prf ->
      extCtx (newHyp st) $ scprf prf

  scintro prf st =
   gheadm (False, prioNo, Nothing) (pbc "sidecontrol") prf $ \prf -> case prf of
    OrIl prf -> scprf prf (noNewHyp st)
    OrIr prf -> scprf prf (noNewHyp st)
    AndI prf1 prf2 ->
     andp (scprf prf1 (noNewHyp st))
          (scprf prf2 (noNewHyp st))
    ExistsI _ prf -> scprf prf (noNewHyp st)
    ImpliesI prf -> extCtx (newHyp st) $ scprf prf
    NotI prf -> extCtx (newHyp st) $ scprf prf
    ForallI prf -> extCtx (noNewHyp st) $ scprf prf
    TopI -> ok
    EqI prf -> sceq prf False False (noNewHyp st)

  sceqelim prf gc st =
   gheadm (False, prioNo, Nothing) (pbc "sidecontrol") prf $ \prf -> case prf of
    UseEq -> ok
    UseEqSym -> ok
    EqElimStep prf -> sceqestep prf gc st

  sceqestep prf gc st =
   gheadm (False, prioNo, Nothing) (pbc "sidecontrol") prf $ \prf -> case prf of
    NTEqElimStep prf -> scntestep sceqelim prf gc st

  scntestep :: (a -> GenCost -> SCState -> MetaEnv MPB) -> NTElimStep a -> GenCost -> SCState -> MetaEnv MPB
  scntestep c prf gc st =
   case prf of
    AndEl prf -> c prf gc' st
     where gc' = case gc of
                  GCFork x _ -> x
                  GCLocalHyp -> gc
    AndEr prf -> c prf gc' st
     where gc' = case gc of
                  GCFork _ x -> x
                  GCLocalHyp -> gc
    ExistsE prf -> c prf gc st
    ImpliesE prf1 prf2 ->
     mpret $ Cost gccost $
     andp (scprf prf1 (noNewHyp st))
          (c prf2 gc' st)
     where (gccost, gc') = case gc of
                            GCSubProb x y -> (x, y)
                            GCLocalHyp -> (0, gc)
    ForallE _ prf -> c prf gc st
    InvBoolExtl prf1 prf2 ->
     mpret $ Cost gccost $
     andp (scprf prf1 (noNewHyp st))
          (c prf2 gc' st)
     where (gccost, gc') = case gc of
                            GCFork (GCSubProb x y) _ -> (x, y)
                            GCLocalHyp -> (0, gc)
                            GCStop -> (100000, gc)
                            _ -> error $ show gc
    InvBoolExtr prf1 prf2 ->
     mpret $ Cost gccost $
     andp (scprf prf1 (noNewHyp st))
          (c prf2 gc' st)
     where (gccost, gc') = case gc of
                            GCFork _ (GCSubProb x y) -> (x, y)
                            GCLocalHyp -> (0, gc)
                            GCStop -> (100000, gc)
                            _ -> error $ show gc
    InvFunExt _ prf ->
     c prf gc st

  sceq prf inchain stepcost st =
   gheadm (False, prioNo, Nothing) (pbc "sidecontrol") prf $ \prf -> case prf of
    Simp prf -> sceqsimp prf st
    Step hyp prf1 prf2 prf3 ->
     if stepcost then
      mpret $ Cost costStep pp
     else
      pp
     where
     pp =
      andp (
        gheadm (False, prioNo, Nothing) (pbc "sidecontrol") hyp $ \(Hyp elr _) ->
        travHyp elr st $ sceqelim prf1
       ) (
      andp (sceqsimp prf2 st)
           (sceq prf3 True True st))
    BoolExt prf1 prf2 ->
     if inchain then
      err "not boolext in eq chain"
     else
      andp (extCtx (newHyp st) $ scprf prf1)
           (extCtx (newHyp st) $ scprf prf2)
    FunExt prf ->
     if inchain then
      err "not funext in eq chain"
     else
      extCtx st $ sceq prf False True

  sceqsimp prf st =
   gheadm (False, prioNo, Nothing) (pbc "sidecontrol") prf $ \prf -> case prf of
    SimpLam _ prf -> extCtx st $ sceq prf False True
    SimpCons _ prfs -> andps (\prf -> sceq prf False True st) prfs
    SimpApp prfs -> sceqsimpargs prfs st
    SimpChoice prf prfs -> andp (sceq prf False True st) $ sceqsimpargs prfs st

  sceqsimpargs prfs st =
   gheadm (False, prioNo, Nothing) (pbc "sidecontrol") prfs $ \prfs -> case prfs of
    PrEqNil -> ok
    PrEqCons prf prfs ->
     andp (sceq prf False True st)
          (sceqsimpargs prfs st)


extCtx :: SCState -> (SCState -> MetaEnv MPB) -> MetaEnv MPB
extCtx st c = c (st {scsCtx = scsCtx st + 1})

travHyp :: HElr -> SCState -> (GenCost -> SCState -> MetaEnv MPB) -> MetaEnv MPB
travHyp (AC typ qf prfexi) st c = andp (sidecontrol prfexi st) (c GCLocalHyp st)
travHyp elr st c =
 if used then
  mpret $ Cost costElrUsedAgain $ add
 else
  add
 where
  elr' = case elr of
   HVar v -> HVar (scsCtx st - v)
   HGlob{} -> elr
  gc = case elr of
   HVar{} -> GCLocalHyp
   HGlob gh -> ghGenCost gh
  add = c gc (st {scsHyps = elr' : scsHyps st})
  used = case elr' of
   HVar v -> u (scsHyps st)
    where
     u [] = False
     u (HVar v' : _) | v' == v = True
     u (_ : hyps) = u hyps
   HGlob gh -> u (scsHyps st)
    where
     u [] = False
     u (HGlob gh' : _) | ghId gh' == id = True
     u (_ : hyps) = u hyps
     id = ghId gh

andps f [] = ok
andps f [x] = f x
andps f (x : xs) = andp (f x) (andps f xs)

noLocal = 100000000

mostLocalHyp :: MetaHyp -> MetaProofElim -> MetaEnv (MMB Int)
mostLocalHyp hyp prf = cmin (fhyp 0 hyp) (felim True 0 prf)
 where
  fprf n prf = gheadc (Meta prf) $ \prf -> case prf of
   Intro prf -> fintro n prf
   Elim hyp prf ->
    cmin (fhyp n hyp) (felim False n prf)
   RAA prf -> fprf (n + 1) prf

  fhyp n hyp = gheadc (Meta hyp) $ \(Hyp elr _) -> case elr of
   HVar v -> mbret $ if v < n then noLocal else (v - n)
   HGlob{} -> mbret noLocal
   AC _ _ prf -> fprf n prf

  fintro n prf = gheadc (Meta prf) $ \prf -> case prf of
   OrIl prf -> fprf n prf
   OrIr prf -> fprf n prf
   AndI prf1 prf2 -> cmin (fprf n prf1) (fprf n prf2)
   ExistsI _ prf -> fprf n prf
   ImpliesI prf -> fprf (n + 1) prf
   NotI prf -> fprf (n + 1) prf
   ForallI prf -> fprf (n + 1) prf
   TopI -> mbret noLocal
   EqI prf -> feq n prf

  felim istopelim n prf =
   gheadc (Meta prf) $ \prf -> case prf of
    Use prf -> feqsimp n prf
    ElimStep prf -> festep istopelim n prf

  festep istopelim n prf =
   gheadc (Meta prf) $ \prf -> case prf of
    BotE -> mbret noLocal
    NotE prf -> fprf n prf
    OrE prf1 prf2 ->
     if istopelim then
      mbret noLocal
     else
      cmin (fprf (n + 1) prf1) (fprf (n + 1) prf2)
    NTElimStep prf -> fntestep (felim istopelim) n prf

  feqelim n prf = gheadc (Meta prf) $ \prf -> case prf of
    UseEq -> mbret noLocal
    UseEqSym -> mbret noLocal
    EqElimStep prf -> feqestep n prf

  feqestep n prf =
   gheadc (Meta prf) $ \prf -> case prf of
    NTEqElimStep prf -> fntestep feqelim n prf

  fntestep :: (Int -> a -> MetaEnv (MMB Int)) -> Int -> NTElimStep a -> MetaEnv (MMB Int)
  fntestep c n prf =
   case prf of
    AndEl prf -> c n prf
    AndEr prf -> c n prf
    ExistsE prf -> c n prf
    ImpliesE prf1 prf2 ->
     cmin (fprf n prf1) (c n prf2)
    ForallE _ prf -> c n prf
    InvBoolExtl prf1 prf2 ->
     cmin (fprf n prf1) (c n prf2)
    InvBoolExtr prf1 prf2 ->
     cmin (fprf n prf1) (c n prf2)
    InvFunExt _ prf ->
     c n prf

  feq n prf =
   gheadc (Meta prf) $ \prf -> case prf of
    Simp prf -> feqsimp n prf
    Step hyp prf1 prf2 prf3 ->
     cmin (fhyp n hyp) (cmin (feqelim n prf1) (cmin (feqsimp n prf2) (feq n prf3)))
    BoolExt prf1 prf2 ->
     cmin (fprf (n + 1) prf1) (fprf (n + 2) prf2)
    FunExt prf ->
     feq (n + 1) prf

  feqsimp n prf =
   gheadc (Meta prf) $ \prf -> case prf of
    SimpLam _ prf -> feq (n + 1) prf
    SimpCons _ prfs -> ff prfs
     where ff [] = mbret noLocal
           ff (x : xs) = cmin (feq n x) (ff xs)
    SimpApp prfs -> feqsimpargs n prfs
    SimpChoice prf prfs -> cmin (feq n prf) (feqsimpargs n prfs)

  feqsimpargs n prfs =
   gheadc (Meta prfs) $ \prfs -> case prfs of
    PrEqNil -> mbret noLocal
    PrEqCons prf prfs ->
     cmin (feq n prf)
          (feqsimpargs n prfs)

  cmin :: MetaEnv (MMB Int) -> MetaEnv (MMB Int) -> MetaEnv (MMB Int)
  cmin x1 x2 =
   cheadc x1 $ \i1 ->
   cheadc x2 $ \i2 ->
   mbret $ min i1 i2



compareElim :: Int -> MetaHyp -> MetaProofElim -> MetaHyp -> MetaProofElim -> MetaEnv (MMB Ordering)
compareElim scopediff hyp1 prf1 hyp2 prf2 = ccomp (fhyp hyp1 hyp2) (felim True prf1 prf2)
 where
  fprf prf1 prf2 =
   gheadc (Meta prf1) $ \prf1 -> gheadc (Meta prf2) $ \prf2 -> case (prf1, prf2) of
    (Intro prf1, Intro prf2) -> fintro prf1 prf2
    (Elim hyp1 prf1, Elim hyp2 prf2) ->
     ccomp (fhyp hyp1 hyp2) (felim False prf1 prf2)
    (RAA prf1, RAA prf2) -> fprf prf1 prf2
    _ -> mbret $ compare (iprf prf1) (iprf prf2)

  iprf (Intro{}) = 0
  iprf (Elim{}) = 1
  iprf (RAA{}) = 2

  fhyp hyp1 hyp2 = gheadc (Meta hyp1) $ \(Hyp elr1 _) -> gheadc (Meta hyp2) $ \(Hyp elr2 _) -> case (elr1, elr2) of
   (HVar v1, HVar v2) -> mbret $ compare (v1 + scopediff) v2
   (HGlob gh1, HGlob gh2) -> mbret $ compare (ghId gh1) (ghId gh2)
   (AC typ1 form1 prf1, AC typ2 form2 prf2) -> ccomp (ftype (Meta typ1) (Meta typ2)) $ ccomp (fform (Meta form1) (Meta form2)) (fprf prf1 prf2)
   _ -> mbret $ compare (ielr elr1) (ielr elr2)

  ielr (HVar{}) = 0
  ielr (HGlob{}) = 1
  ielr (AC{}) = 2

  fintro prf1 prf2 = gheadc (Meta prf1) $ \prf1 -> gheadc (Meta prf2) $ \prf2 -> case (prf1, prf2) of
   (OrIl prf1, OrIl prf2) -> fprf prf1 prf2
   (OrIr prf1, OrIr prf2) -> fprf prf1 prf2
   (AndI prfl1 prfr1, AndI prfl2 prfr2) -> ccomp (fprf prfl1 prfl2) (fprf prfr1 prfr2)
   (ExistsI form1 prf1, ExistsI form2 prf2) -> ccomp (fform (Meta form1) (Meta form2)) (fprf prf1 prf2)
   (ImpliesI prf1, ImpliesI prf2) -> fprf prf1 prf2
   (NotI prf1, NotI prf2) -> fprf prf1 prf2
   (ForallI prf1, ForallI prf2) -> fprf prf1 prf2
   (TopI, TopI) -> mbret EQ
   (EqI prf1, EqI prf2) -> feq prf1 prf2
   _ -> mbret $ compare (iintro prf1) (iintro prf2)

  iintro (OrIl{}) = 0
  iintro (OrIr{}) = 1
  iintro (AndI{}) = 2
  iintro (ExistsI{}) = 3
  iintro (ImpliesI{}) = 4
  iintro (NotI{}) = 5
  iintro (ForallI{}) = 6
  iintro (TopI{}) = 7
  iintro (EqI{}) = 8

  felim istopelim prf1 prf2 =
   gheadc (Meta prf1) $ \prf1 -> gheadc (Meta prf2) $ \prf2 -> case (prf1, prf2) of
    (Use prf1, Use prf2) -> feqsimp prf1 prf2
    (ElimStep prf1, ElimStep prf2) -> festep istopelim prf1 prf2
    _ -> mbret $ compare (ielim prf1) (ielim prf2)

  ielim (Use{}) = 0
  ielim (ElimStep{}) = 1

  festep istopelim prf1 prf2 =
   gheadc (Meta prf1) $ \prf1 -> gheadc (Meta prf2) $ \prf2 -> case (prf1, prf2) of
    (BotE, BotE) -> mbret EQ
    (NotE prf1, NotE prf2) -> fprf prf1 prf2
    (OrE prfl1 prfr1, OrE prfl2 prfr2) ->
     if istopelim then
      mbret EQ
     else
      ccomp (fprf prfl1 prfl2) (fprf prfr1 prfr2)
    (NTElimStep prf1, NTElimStep prf2) -> fntestep (felim istopelim) prf1 prf2
    _ -> mbret $ compare (iestep prf1) (iestep prf2)

  iestep (BotE{}) = 0
  iestep (NotE{}) = 1
  iestep (OrE{}) = 2
  iestep (NTElimStep{}) = 3

  feqelim prf1 prf2 = gheadc (Meta prf1) $ \prf1 -> gheadc (Meta prf2) $ \prf2 -> case (prf1, prf2) of
    (UseEq, UseEq) -> mbret EQ
    (UseEqSym, UseEqSym) -> mbret EQ
    (EqElimStep prf1, EqElimStep prf2) -> feqestep prf1 prf2
    _ -> mbret $ compare (ieqelim prf1) (ieqelim prf2)

  ieqelim (UseEq{}) = 0
  ieqelim (UseEqSym{}) = 1
  ieqelim (EqElimStep{}) = 2

  feqestep prf1 prf2 =
   gheadc (Meta prf1) $ \prf1 -> gheadc (Meta prf2) $ \prf2 -> case (prf1, prf2) of
    (NTEqElimStep prf1, NTEqElimStep prf2) -> fntestep feqelim prf1 prf2

  fntestep :: (a -> a -> MetaEnv (MMB Ordering)) -> NTElimStep a -> NTElimStep a -> MetaEnv (MMB Ordering)
  fntestep c prf1 prf2 =
   case (prf1, prf2) of
    (AndEl prf1, AndEl prf2) -> c prf1 prf2
    (AndEr prf1, AndEr prf2) -> c prf1 prf2
    (ExistsE prf1, ExistsE prf2) -> c prf1 prf2
    (ImpliesE prfl1 prfr1, ImpliesE prfl2 prfr2) ->
     ccomp (fprf prfl1 prfl2) (c prfr1 prfr2)
    (ForallE form1 prf1, ForallE form2 prf2) -> ccomp (fform (Meta form1) (Meta form2)) (c prf1 prf2)
    (InvBoolExtl prfl1 prfr1, InvBoolExtl prfl2 prfr2) ->
     ccomp (fprf prfl1 prfl2) (c prfr1 prfr2)
    (InvBoolExtr prfl1 prfr1, InvBoolExtr prfl2 prfr2) ->
     ccomp (fprf prfl1 prfl2) (c prfr1 prfr2)
    (InvFunExt form1 prf1, InvFunExt form2 prf2) ->
     ccomp (fform (Meta form1) (Meta form2)) (c prf1 prf2)
    _ -> mbret $ compare (intestep prf1) (intestep prf2)

  intestep (AndEl{}) = 0
  intestep (AndEr{}) = 1
  intestep (ExistsE{}) = 2
  intestep (ImpliesE{}) = 3
  intestep (ForallE{}) = 4
  intestep (InvBoolExtl{}) = 5
  intestep (InvBoolExtr{}) = 6
  intestep (InvFunExt{}) = 7

  feq prf1 prf2 =
   gheadc (Meta prf1) $ \prf1 -> gheadc (Meta prf2) $ \prf2 -> case (prf1, prf2) of
    (Simp prf1, Simp prf2) -> feqsimp prf1 prf2
    (Step hyp1 prfa1 prfb1 prfc1, Step hyp2 prfa2 prfb2 prfc2) ->
     ccomp (fhyp hyp1 hyp2) $ ccomp (feqelim prfa1 prfa2) $ ccomp (feqsimp prfb1 prfb2) (feq prfc1 prfc2)
    (BoolExt prfa1 prfb1, BoolExt prfa2 prfb2) ->
     ccomp (fprf prfa1 prfa2) (fprf prfb1 prfb2)
    (FunExt prf1, FunExt prf2) ->
     feq prf1 prf2
    _ -> mbret $ compare (ieq prf1) (ieq prf2)

  ieq (Simp{}) = 0
  ieq (Step{}) = 1
  ieq (BoolExt{}) = 2
  ieq (FunExt{}) = 3

  feqsimp prf1 prf2 =
   gheadc (Meta prf1) $ \prf1 -> gheadc (Meta prf2) $ \prf2 -> case (prf1, prf2) of
    (SimpLam _ prf1, SimpLam _ prf2) -> feq prf1 prf2
    (SimpCons c1 prfs1, SimpCons c2 prfs2) ->
     ccomp (mbret $ compare (icon c1) (icon c2)) (ff prfs1 prfs2)
     where ff [] [] = mbret EQ
           ff (x1 : xs1) (x2 : xs2) = ccomp (feq x1 x2) (ff xs1 xs2)
           ff [] (_:_) = mbret LT
           ff (_:_) [] = mbret GT
    (SimpApp prfs1, SimpApp prfs2) -> feqsimpargs prfs1 prfs2
    (SimpChoice prf1 prfs1, SimpChoice prf2 prfs2) -> ccomp (feq prf1 prf2) (feqsimpargs prfs1 prfs2)
    _ -> mbret $ compare (ieqsimp prf1) (ieqsimp prf2)

  ieqsimp (SimpLam{}) = 0
  ieqsimp (SimpCons{}) = 1
  ieqsimp (SimpApp{}) = 2
  ieqsimp (SimpChoice{}) = 3

  icon Top = 0
  icon Bot = 1
  icon And = 2
  icon Or = 3
  icon Implies = 4
  icon Not = 5
  icon Forall = 6
  icon Exists = 7
  icon Eq = 8

  feqsimpargs prfs1 prfs2 =
   gheadc (Meta prfs1) $ \prfs1 -> gheadc (Meta prfs2) $ \prfs2 -> case (prfs1, prfs2) of
    (PrEqNil, PrEqNil) -> mbret EQ
    (PrEqCons prf1 prfs1, PrEqCons prf2 prfs2) ->
     ccomp (feq prf1 prf2)
           (feqsimpargs prfs1 prfs2)
    _ -> mbret $ compare (ieqsimpargs prfs1) (ieqsimpargs prfs2)

  ieqsimpargs (PrEqNil{}) = 0
  ieqsimpargs (PrEqCons{}) = 1

  ftype typ1 typ2 =
   gheadc typ1 $ \typ1 -> gheadc typ2 $ \typ2 -> case (typ1, typ2) of
    (Ind i1, Ind i2) -> mbret $ compare i1 i2
    (Bool, Bool) -> mbret EQ
    (Map it1 ot1, Map it2 ot2) -> ccomp (ftype it1 it2) (ftype ot1 ot2)
    _ -> mbret $ compare (itype typ1) (itype typ2)

  itype (Ind{}) = 0
  itype (Bool{}) = 1
  itype (Map{}) = 2

  fform form1 form2 =
   gheadc form1 $ \form1 -> gheadc form2 $ \form2 -> case (form1, form2) of
    (C _ c1 args1, C _ c2 args2) ->
     ccomp (mbret $ compare (icon c1) (icon c2)) (ff args1 args2)
     where ff [] [] = mbret EQ
           ff (F x1 : xs1) (F x2 : xs2) = ccomp (fform x1 x2) (ff xs1 xs2)
           ff (T t1 : xs1) (T t2 : xs2) = ccomp (ftype t1 t2) (ff xs1 xs2)
           ff (F{} : _) (T{} : _) = mbret LT
           ff (T{} : _) (F{} : _) = mbret GT
           ff [] (_:_) = mbret LT
           ff (_:_) [] = mbret GT
    (App _ elr1 args1, App _ elr2 args2) ->
     ccomp (felr elr1 elr2) (fargs args1 args2)
    (Choice _ typ1 form1 args1, Choice _ typ2 form2 args2) ->
     ccomp (ftype typ1 typ2) $ ccomp (fform form1 form2) (fargs args1 args2)
    (Lam _ typ1 form1, Lam _ typ2 form2) ->
     ccomp (ftype typ1 typ2) (fform form1 form2)
    _ -> mbret $ compare (iform form1) (iform form2)

  iform (C{}) = 0
  iform (App{}) = 1
  iform (Choice{}) = 2
  iform (Lam{}) = 3

  felr (Var v1) (Var v2) = mbret $ compare (v1 + scopediff) v2
  felr (Glob gv1) (Glob gv2) = mbret $ compare (gvId gv1) (gvId gv2)
  felr (Var{}) (Glob{}) = mbret LT
  felr (Glob{}) (Var{}) = mbret GT

  fargs args1 args2 =
   gheadc args1 $ \args1 -> gheadc args2 $ \args2 -> case (args1, args2) of
    (ArgNil, ArgNil) -> mbret EQ
    (ArgNil, ArgCons{}) -> mbret LT
    (ArgCons{}, ArgNil) -> mbret GT
    (ArgCons x1 xs1, ArgCons x2 xs2) ->
     ccomp (fform x1 x2) (fargs xs1 xs2)

  ccomp :: MetaEnv (MMB Ordering) -> MetaEnv (MMB Ordering) -> MetaEnv (MMB Ordering)
  ccomp x1 x2 =
   cheadc x1 $ \o ->
   case o of
    EQ -> x2
    _ -> mbret o


