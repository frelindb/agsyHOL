{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}

module Check where

import NarrowingSearch hiding (And)
import Syntax
import SearchControl
import PrintProof


type CompTrace = Int  -- number of reductions

data CRes = CDone HNFormula CompTrace
          | CBlocked CFormula [CArgs]
          | CFail

computei :: Int -> Bool -> CFormula -> [CArgs] -> MetaEnv (MMB CRes)
computei 1000 _ _ _ = mbret CFail
computei count fromlookup cf@(Cl env f) stack = do
 f <- expandbind f
 case f of
  Meta m -> mbret $ CBlocked cf stack
  NotM f -> case f of
   App muid (Var v) args ->
    case doclos env v of
     Left v ->
      mbret $ CDone (HNApp (gmuid muid) (Var v) (ClA env args : stack)) count
     Right sf ->
      computei count True sf (ClA env args : stack)
   App muid elr@(Glob _) args ->
    mbret $ CDone (HNApp (gmuid muid) elr (ClA env args : stack)) count
   Choice muid typ bdy args ->
    mbret $ CDone (HNChoice (gmuid muid) typ (Cl env bdy) (ClA env args : stack)) count
   Lam muid typ bdy ->
    cheadc (getStackHead stack) $ \res -> case res of
     HNNil ->
      mbret $ CDone (HNLam (gmuid muid) typ (Cl (Skip : env) bdy)) count
     HNCons arg stack ->
      computei (count + 1) False (sub arg (Cl (Skip : env) bdy)) stack
   C muid c args ->
    cheadc (getStackHead stack) $ \res -> case res of
     HNNil -> mbret $ CDone (HNC (gmuid muid) c (map clca args)) count
      where
       clca (F f) = F $ Cl env f
       clca (T t) = T t
     HNCons{} -> mbret CFail
 where
  gmuid muid = if fromlookup then Nothing else muid
computei count fromlookup (CApp f (Cl env a)) stack = computei count fromlookup f (ClA env (NotM $ ArgCons a $ NotM ArgNil) : stack)
computei count fromlookup (CNot f) stack =
 cheadc (getStackHead stack) $ \res -> case res of
  HNNil -> mbret $ CDone (HNC nu Not [F f]) count
  HNCons{} -> mbret CFail
computei count fromlookup (CHN f) stack =
 case f of
  HNApp muid elr args -> mbret $ CDone (HNApp (gmuid muid) elr (args ++ stack)) count
  HNChoice muid typ qf args -> mbret $ CDone (HNChoice (gmuid muid) typ qf (args ++ stack)) count
  HNC{} ->
   cheadc (getStackHead stack) $ \res -> case res of
    HNNil -> mbret $ CDone f count
    HNCons{} -> mbret CFail
 where
  gmuid muid = if fromlookup then Nothing else muid

getStackHead :: [CArgs] -> MetaEnv (MMB HNArgs)
getStackHead stack =
 case stack of
  [] -> mbret HNNil
  (ClA env args : stack) ->
   gheadc args $ \args -> case args of
    ArgNil -> getStackHead stack
    ArgCons arg args ->
     mbret $ HNCons (Cl env arg) (ClA env args : stack)

compute :: CFormula -> MetaEnv (MMB (HNFormula, CompTrace))
compute f = gg f []
 where
  gg f stack =
   cheadc (computei 0 False f stack) $ \res ->
   case res of
    CDone x y -> mbret (x, y)
    CBlocked cf@(Cl _ f) stack ->
     gheadc f $ \_ ->
     gg cf stack
    CFail -> NarrowingSearch.fail "computation failed"

-- ----------------------

checkProof :: Context -> CFormula -> MetaProof -> MetaEnv MPB
checkProof ctx form prf =
 getFormHead form $
 gheadm (True, prioProof, Nothing) (prCtx ctx >>= \pc -> prCFormula (length ctx) form >>= \pf -> return ("checkProof : " ++ pc ++ " : " ++ pf)) prf $ \prf -> case prf of
  Intro prf ->
   cheadp (prioDecompFormUnknown, Just BIComputed) (pbc "checkProof.Intro") (compute form) $ \(form, _) ->
   checkIntro ctx form prf
  Elim hyp prf ->
   checkHyp ctx hyp $ \focante ->
   checkProofElim ctx form focante prf
  RAA prf ->
   andp
    (cheadp (prioNo, Nothing) (pbc "checkProof.RAA sidecond") (compute form) $ \(form, _) -> case form of
      HNC _ Bot _ -> err "type not Bot in Raa rule"
      HNC _ Forall _ -> err "type not Forall in Raa rule"
      HNC _ Implies _ -> err "type not Implies in Raa rule"
      _ -> ok
    ) $
    checkProof (HypExt (CNot form) : ctx) (cl formBot) prf

getFormHead :: CFormula -> MetaEnv MPB -> MetaEnv MPB
getFormHead form c = case form of
 Cl _ f -> gheadp (False, prioUnknownGoal, Nothing) (pbc "getFormHead") f $ \_ -> c
 _ -> c

checkHyp :: Context -> MetaHyp -> (CFormula -> MetaEnv MPB) -> MetaEnv MPB
checkHyp ctx hyp cnt =
 gheadm (True, prioHyp, Just (BICtx ctx)) (pbc "checkProof.Elim") hyp $ \(Hyp hyp focante) ->
 case hyp of
  AC typ qf prfexi ->
   andp (checkType (Meta typ)) (
   andp (checkForm ctx (NotM $ Map (Meta typ) (NotM Bool)) (Meta qf)) (
   andp (checkProof ctx (cl $ NotM $ C nu Exists [T (Meta typ), F (Meta qf)]) prfexi)
        (cnt focante)))
  _ -> cnt focante

checkIntro :: Context -> HNFormula -> MetaIntro -> MetaEnv MPB
checkIntro ctx form prf =
 gheadm (True, prioIntro, Just (BIForm form)) (pbc "checkIntro") prf $ \prf -> case prf of
  OrIl prf -> case form of
   HNC _ Or [F forml, _] ->
    checkProof ctx forml prf
   _ -> err "Injl : Or"
  OrIr prf -> case form of
   HNC _ Or [_, F formr] ->
    checkProof ctx formr prf
   _ -> err "Injr : Or"
  AndI prfl prfr -> case form of
   HNC _ And [F forml, F formr] ->
    andp (checkProof ctx forml prfl)
         (checkProof ctx formr prfr)
   _ -> err "Pair : And"
  ExistsI witness prf -> case form of
   HNC _ Exists [T typ, F qf] ->
    andp (checkForm ctx typ (Meta witness))
         (checkProof ctx (CApp qf (cl (Meta witness))) prf)
   _ -> err "PairDep : Exists"
  ImpliesI prf -> case form of
   HNC _ Implies [F antef, F succf] ->
    checkProof (HypExt antef : ctx) (lift 1 succf) prf
   _ -> err "Abs : Implies"
  NotI prf -> case form of
   HNC _ Not [F antef] ->
    checkProof (HypExt antef : ctx) (cl formBot) prf
   _ -> err "AbsNot : Not"
  ForallI prf -> case form of
   HNC _ Forall [T typ, F qf] ->
    checkProof (VarExt typ : ctx) (CApp (lift 1 qf) (cl $ NotM $ App nu (Var 0) (NotM ArgNil))) prf
   _ -> err "AbsDep : Forall"
  TopI -> case form of
   HNC _ Top [] ->
    ok
   _ -> err "Trivial : Top"
  EqI prf -> case form of
   HNC _ Eq [T typ, F lhs, F rhs] ->
    checkProofEq [] [] ctx typ lhs rhs prf
   _ -> err "Refl : Eq"

checkProofElim :: Context-> CFormula -> CFormula -> MetaProofElim -> MetaEnv MPB
checkProofElim ctx form focante prf =
 gheadm (True, prioProofElim, Nothing) (prCFormula (length ctx) form >>= \pe -> prCFormula (length ctx) focante >>= \pi -> return ("checkProofElim : " ++ pi ++ " -> " ++ pe)) prf $ \prf -> case prf of
  Use prf ->
   andp
    (cheadp (prioNo, Nothing) (pbc "checkProofElim.Use sidecond") (compute focante) $ \(focante, _) -> case focante of
      HNC _ Bot _ -> err "inftype not Bot in Use rule"
      HNC _ Eq _ -> err "inftype not Eq in Use rule"
      _ -> ok
    ) $
    checkProofEqSimp [] [] ctx typeBool form focante prf
  ElimStep prf ->
   cheadp (prioDecompFormUnknown, Just BIComputed) (pbc "checkProofElim.ElimStep") (compute focante) $ \(focante, _) ->
   checkElimStep ctx form focante prf

checkElimStep :: Context -> CFormula -> HNFormula -> MetaElimStep -> MetaEnv MPB
checkElimStep ctx form focante prf =
 gheadm (True, prioElimStep, Just (BIForm focante)) (pbc "checkElimStep") prf $ \prf -> case prf of
  BotE -> case focante of
   HNC _ Bot [] ->
    ok
   _ -> err "Absurd : Bot"
  NotE prf -> case focante of
   HNC _ Not [F antef] ->
    checkProof ctx antef prf
   _ -> err "AppNot : Not"
  OrE prfl prfr -> case focante of
   HNC _ Or [F forml, F formr] ->
    andp (checkProof (HypExt forml : ctx) (lift 1 form) prfl)
         (checkProof (HypExt formr : ctx) (lift 1 form) prfr)
   _ -> err "Case : Or"
  NTElimStep prf ->
   checkNTElimStep ctx focante (checkProofElim ctx form) prf

checkProofEqElim :: Context-> MType -> (CFormula -> CFormula -> MetaEnv MPB) -> CFormula -> MetaProofEqElim -> MetaEnv MPB
checkProofEqElim ctx typ cont focante prf =
 gheadm (True, prioProofEqElim, Nothing) (pbc "checkProofEqElim") prf $ \prf -> case prf of
  UseEq ->
   unifyToEq focante $ \focante ->
   case focante of
    HNC _ Eq [T typ', F lhs, F rhs] ->
     andp (checkEqType typ typ')
          (cont lhs rhs)
    _ -> err "UseEq : Eq"
  UseEqSym ->
   unifyToEq focante $ \focante ->
   case focante of
    HNC _ Eq [T typ', F lhs, F rhs] ->
     andp (checkEqType typ typ')
          (cont rhs lhs)
    _ -> err "UseEqSym : Eq"
  EqElimStep prf ->
   cheadp (prioDecompFormUnknown, Just BIComputed) (pbc "checkProofEqElim.EqElimStep") (compute focante) $ \(focante, _) ->
   checkEqElimStep ctx typ cont focante prf

checkEqElimStep :: Context -> MType -> (CFormula -> CFormula -> MetaEnv MPB) -> HNFormula -> MetaEqElimStep -> MetaEnv MPB
checkEqElimStep ctx typ cont focante prf =
 gheadm (True, prioEqElimStep, Just (BIForm focante)) (pbc "checkEqElimStep") prf $ \prf -> case prf of
  NTEqElimStep prf ->
   checkNTElimStep ctx focante (checkProofEqElim ctx typ cont) prf

unifyToEq :: CFormula -> (HNFormula -> MetaEnv MPB) -> MetaEnv MPB
unifyToEq f cont = g f []
 where
 g f stack =
  cheadp (prioUnknownArgs, Nothing) (pbc "unifyToEq.unknownargs") (computei 0 False f stack) $ \res ->
  case res of
   CFail -> err "computation failed"
   CDone f _ ->
    cont f
   CBlocked f@(Cl env m) stack ->
    gheadp (False, prioUnifyForm, Just (BIUnifyForm [] (HNC nu Eq [T (error "not used"), F (error "not used"), F (error "not used")]) env)) (pbc "unifyToEq") m $ \_ ->
    g f stack

checkNTElimStep :: Context -> HNFormula -> (CFormula -> a -> MetaEnv MPB) -> NTElimStep a -> MetaEnv MPB
checkNTElimStep ctx focante cont prf =
 case prf of
  AndEl prf -> case focante of
   HNC _ And [F forml, _] ->
    cont forml prf
   _ -> err "Projl : And"
  AndEr prf -> case focante of
   HNC _ And [_, F formr] ->
    cont formr prf
   _ -> err "Projr : And"
  ExistsE prf -> case focante of
   HNC _ Exists [T typ, F cqf@(Cl env qf)] ->
    cont (CApp cqf (Cl env $ NotM $ Choice nu typ qf (NotM ArgNil))) prf
   _ -> err "ProjDep : Exists"
  ImpliesE prfarg prf -> case focante of
   HNC _ Implies [F forml, F formr] ->
    andp (checkProof ctx forml prfarg)
         (cont formr prf)
   _ -> err "AppImp : Implies"
  ForallE arg prf -> case focante of
   HNC _ Forall [T typ, F qf] ->
    andp (checkForm ctx typ (Meta arg))
         (cont (CApp qf (cl (Meta arg))) prf)
   _ -> err "AppDep : Forall"
  InvBoolExtl prfarg prf -> case focante of
   HNC _ Eq [T typ, F lhs, F rhs] ->
    gheadp (False, prioUnknownType, Nothing) (pbc "checkNTElimStep.InvBoolExtl") typ $ \typ -> case typ of
     Bool ->
      andp (checkProof ctx lhs prfarg)
           (cont rhs prf)
     _ -> err "InvBoolExtl : Bool"
   _ -> err "InvBoolExtl : Eq"
  InvBoolExtr prfarg prf -> case focante of
   HNC _ Eq [T typ, F lhs, F rhs] ->
    gheadp (False, prioUnknownType, Nothing) (pbc "checkNTElimStep.InvBoolExtr") typ $ \typ -> case typ of
     Bool ->
      andp (checkProof ctx rhs prfarg)
           (cont lhs prf)
     _ -> err "InvBoolExtr : Bool"
   _ -> err "InvBoolExtr : Eq"
  InvFunExt arg prf -> case focante of
   HNC uid Eq [T typ, F lhs, F rhs] ->
    gheadp (False, prioUnknownType, Nothing) (pbc "checkNTElimStep.InvFunExt") typ $ \typ -> case typ of
     Map it ot ->
      andp (checkForm ctx it (Meta arg))
           (cont (CHN (HNC uid Eq [T ot, F (CApp lhs (cl (Meta arg))), F (CApp rhs (cl (Meta arg)))])) prf)
     _ -> err "InvFunExt : Map"
   _ -> err "InvFunExt : Eq"

checkProofEq :: [Int] -> [Int] -> Context -> MType -> CFormula -> CFormula -> MetaProofEq -> MetaEnv MPB
checkProofEq luids ruids ctx typ lhs rhs prf =
 gheadm (True, prioProofEq, Nothing) (prCFormula (length ctx) lhs >>= \plhs -> prCFormula (length ctx) rhs >>= \prhs -> return ("checkProofEq " ++ plhs ++ " = " ++ prhs)) prf $ \prf -> case prf of
  Simp prf ->
   checkProofEqSimp luids ruids ctx typ lhs rhs prf
  Step hyp prfelim prfsimp prfeq ->
   checkHyp ctx hyp $ \focante ->
   checkProofEqElim ctx typ cont focante prfelim
   where
    cont lhs' rhs' =
     andp
      (checkProofEqSimp [] [] ctx typ lhs lhs' prfsimp)
      (checkProofEq [] [] ctx typ rhs' rhs prfeq)
  BoolExt prf1 prf2 ->
   gheadp (False, prioUnknownType, Nothing) (pbc "checkProofEq.BoolExt") typ $ \typ -> case typ of
    Bool ->
     andp (checkProof (HypExt lhs : ctx) (lift 1 rhs) prf1)
          (checkProof (HypExt rhs : ctx) (lift 1 lhs) prf2)
    _ -> err "BoolExt : Bool"
  FunExt prf ->
   gheadp (False, prioUnknownType, Nothing) (pbc "checkProofEq.FunExt") typ $ \typ -> case typ of
    Map it ot ->
     checkProofEq luids ruids (VarExt it : ctx) ot (CApp (lift 1 lhs) (cl $ NotM $ App nu (Var 0) $ NotM $ ArgNil)) (CApp (lift 1 rhs) (cl $ NotM $ App nu (Var 0) $ NotM $ ArgNil)) prf
    _ -> err "FunExt : Map"

checkProofEqSimp :: [Int] -> [Int] -> Context -> MType -> CFormula -> CFormula -> MetaProofEqSimp -> MetaEnv MPB
checkProofEqSimp luids ruids ctx typ lhs' rhs' prf = gg lhs' [] rhs' []
 where
  gg lhs lstack rhs rstack =
   cheadp (prioUnknownArgs, Nothing) (pbc "checkProofEqSimp.unknownargs") (computei 0 False lhs lstack) $ \lres ->
   cheadp (prioUnknownArgs, Nothing) (pbc "checkProofEqSimp.unknownargs") (computei 0 False rhs rstack) $ \rres ->
   case (lres, rres) of
    (CFail, _) -> err "computation failed"
    (_, CFail) -> err "computation failed"
    (CDone lhs _, CDone rhs _) ->
     checkProofEqSimp2 luids ruids ctx typ lhs rhs prf
    (CDone lhs _, CBlocked rhs rstack) ->
     let
      hh rhs@(Cl env m) rstack =
       gheadp (False, prioUnifyForm, Just (BIUnifyForm ruids lhs env)) (prCFormula (length ctx) lhs' >>= \plhs -> prCFormula (length ctx) rhs' >>= \prhs -> return ("checkProofEqSimp.rig-flex-unify " ++ show ruids ++ " " ++ plhs ++ " = " ++ prhs)) m $ \_ ->
       cheadp (prioUnknownArgs, Nothing) (pbc "checkProofEqSimp.unknownargs") (computei 0 False rhs rstack) $ \res ->
       case res of
        CFail -> err "computation failed"
        CDone rhs _ ->
         checkProofEqSimp2 luids (guid rhs ruids) ctx typ lhs rhs prf
        CBlocked rhs rstack -> hh rhs rstack
     in
      hh rhs rstack
    (CBlocked lhs lstack, CDone rhs _) ->
     let
      hh lhs@(Cl env m) lstack =
       gheadp (False, prioUnifyForm, Just (BIUnifyForm luids rhs env)) (prCFormula (length ctx) lhs' >>= \plhs -> prCFormula (length ctx) rhs' >>= \prhs -> return ("checkProofEqSimp.flex-rig-unify " ++ show luids ++ " " ++ plhs ++ " = " ++ prhs)) m $ \_ ->
       cheadp (prioUnknownArgs, Nothing) (pbc "checkProofEqSimp.unknownargs") (computei 0 False lhs lstack) $ \res ->
       case res of
        CFail -> err "computation failed"
        CDone lhs _ ->
         checkProofEqSimp2 (guid lhs luids) ruids ctx typ lhs rhs prf
        CBlocked lhs lstack -> hh lhs lstack
     in
      hh lhs lstack
    (CBlocked lhs@(Cl _ (Meta m1)) lstack, CBlocked rhs@(Cl _ (Meta m2)) rstack) ->
     return $ PDoubleBlocked m1 m2 (gg lhs lstack rhs rstack)
  guid (HNC (Just uid) _ _) xs = uid : xs
  guid (HNApp (Just uid) _ _) xs = uid : xs
  guid _ xs = xs

checkProofEqSimp2 :: [Int] -> [Int] -> Context -> MType -> HNFormula -> HNFormula -> MetaProofEqSimp -> MetaEnv MPB
checkProofEqSimp2 luids ruids ctx typ lhs rhs prf =
 gheadm (True, prioProofEqSimp, Just (BIFormHead (pickhead lhs rhs))) (pbc "checkProofEqSimp") prf $ \prf ->
  case (lhs, rhs, prf) of
   (HNLam _ typ1 bdy1, HNLam _ typ2 bdy2, SimpLam EMNone prfbdy) ->
    gheadp (False, prioUnknownType, Nothing) (pbc "checkProofEqSimp.Lam") typ $ \typ -> case typ of
     Map ityp otyp ->
      andp (checkEqType ityp typ1) (
      andp (checkEqType ityp typ2)
           (checkProofEq luids ruids (VarExt ityp : ctx) otyp bdy1 bdy2 prfbdy))
     _ -> err "eq lam type mismatch"
   (HNLam _ typ1 bdy1, HNApp muid elr2 args2, SimpLam EMRight prfbdy) ->
    gheadp (False, prioUnknownType, Nothing) (pbc "checkProofEqSimp.Lam") typ $ \typ -> case typ of
     Map ityp otyp ->
      andp (checkEqType ityp typ1)
           (checkProofEq luids ruids (VarExt ityp : ctx) otyp bdy1 bdy2 prfbdy)
     _ -> err "eq lam type mismatch"
    where
     lelr2 = case elr2 of
              Var i -> Var (i + 1)
              Glob g -> Glob g
     bdy2 = CHN (HNApp muid lelr2 (map (\(ClA env x) -> ClA (Lift 1 : env) x) args2 ++ [ClA [] $ NotM $ ArgCons (NotM $ App nu (Var 0) $ NotM ArgNil) (NotM ArgNil)]))
   (HNLam _ typ1 bdy1, HNChoice muid typ2 qf2 args2, SimpLam EMRight prfbdy) ->
    gheadp (False, prioUnknownType, Nothing) (pbc "checkProofEqSimp.Lam") typ $ \typ -> case typ of
     Map ityp otyp ->
      andp (checkEqType ityp typ1)
           (checkProofEq luids ruids (VarExt ityp : ctx) otyp bdy1 bdy2 prfbdy)
     _ -> err "eq lam type mismatch"
    where
     bdy2 = CHN (HNChoice muid typ2 (lift 1 qf2) (map (\(ClA env x) -> ClA (Lift 1 : env) x) args2 ++ [ClA [] $ NotM $ ArgCons (NotM $ App nu (Var 0) $ NotM ArgNil) (NotM ArgNil)]))
   (HNApp muid elr1 args1, HNLam _ typ2 bdy2, SimpLam EMLeft prfbdy) ->
    gheadp (False, prioUnknownType, Nothing) (pbc "checkProofEqSimp.Lam") typ $ \typ -> case typ of
     Map ityp otyp ->
      andp (checkEqType ityp typ2)
           (checkProofEq luids ruids (VarExt ityp : ctx) otyp bdy1 bdy2 prfbdy)
     _ -> err "eq lam type mismatch"
    where
     lelr1 = case elr1 of
              Var i -> Var (i + 1)
              Glob g -> Glob g
     bdy1 = CHN (HNApp muid lelr1 (map (\(ClA env x) -> ClA (Lift 1 : env) x) args1 ++ [ClA [] $ NotM $ ArgCons (NotM $ App nu (Var 0) $ NotM ArgNil) (NotM ArgNil)]))
   (HNChoice muid typ1 qf1 args1, HNLam _ typ2 bdy2, SimpLam EMLeft prfbdy) ->
    gheadp (False, prioUnknownType, Nothing) (pbc "checkProofEqSimp.Lam") typ $ \typ -> case typ of
     Map ityp otyp ->
      andp (checkEqType ityp typ2)
           (checkProofEq luids ruids (VarExt ityp : ctx) otyp bdy1 bdy2 prfbdy)
     _ -> err "eq lam type mismatch"
    where
     bdy1 = CHN (HNChoice muid typ1 (lift 1 qf1) (map (\(ClA env x) -> ClA (Lift 1 : env) x) args1 ++ [ClA [] $ NotM $ ArgCons (NotM $ App nu (Var 0) $ NotM ArgNil) (NotM ArgNil)]))
   (HNC _ c1 [T typ1, F qf1], HNC _ c2 [T typ2, F qf2], SimpCons c [prf]) | c1 == c && c2 == c && (c == Forall || c == Exists) ->
    andp (checkEqType typ1 typ2)
         (checkProofEq luids ruids ctx (NotM $ Map typ1 (NotM Bool)) qf1 qf2 prf)
   (HNC _ Eq [T typ1, F lhs1, F rhs1], HNC _ Eq [T typ2, F lhs2, F rhs2], SimpCons Eq [prflhs, prfrhs]) ->
    andp (checkEqType typ1 typ2) (
          andp (checkProofEq luids ruids ctx typ1 lhs1 lhs2 prflhs)
               (checkProofEq luids ruids ctx typ1 rhs1 rhs2 prfrhs))
   (HNC _ lhsc lhsargs, HNC _ rhsc rhsargs, SimpCons c prfs) | c == lhsc && c == rhsc ->  -- Top, Bot, And, Or, Implies, Not
    chargs lhsargs rhsargs prfs
    where
     chargs [] [] [] = ok
     chargs (F f1 : fs1) (F f2 : fs2) (prf : prfs) =
      andp (checkProofEq luids ruids ctx typeBool f1 f2 prf)
           (chargs fs1 fs2 prfs)
   (HNApp _ elr1 args1, HNApp _ elr2 args2, SimpApp prfs) | eqElr elr1 elr2 ->
    elrType ctx elr1 $ \ityp ->
    chargs ityp args1 args2 prfs
   (HNChoice _ typ1 qf1 args1, HNChoice _ typ2 qf2 args2, SimpChoice prf prfs) ->
    andp (checkEqType typ1 typ2) (
    andp (checkProofEq luids ruids ctx (NotM $ Map typ1 typeBool) qf1 qf2 prf)
         (chargs typ1 args1 args2 prfs))
   _ -> err "eq head mismatch"
 where
  chargs :: MType -> [CArgs] -> [CArgs] -> MetaProofEqs -> MetaEnv MPB
  chargs typ stack1 stack2 prfs =
   cheadp (prioUnknownArgs, Nothing) (pbc "checkProofEqSimp.app/choice-arg") (getStackHead stack1) $ \stack1 ->
   cheadp (prioUnknownArgs, Nothing) (pbc "checkProofEqSimp.app/choice-arg") (getStackHead stack2) $ \stack2 ->
   case (stack1, stack2) of
    (HNNil, HNNil) ->
     gheadm (True, prioProofEqSimp, Just (BISimpArgs False)) (pbc "checkProofEqSimp.app/choice-nil") prfs $ \prfs ->
     case prfs of
      PrEqNil -> ok
      PrEqCons{} -> error "PrEqCons"
    (HNCons a1 stack1, HNCons a2 stack2) ->
     gheadm (True, prioProofEqSimp, Just (BISimpArgs True)) (pbc "checkProofEqSimp.app/choice-cons") prfs $ \prfs ->
     case prfs of
      PrEqNil -> error "PrEqNil"
      PrEqCons prf prfs ->
       gheadp (False, prioUnknownType, Nothing) (pbc "checkProofEqSimp.chargs") typ $ \typ -> case typ of
        Map ityp otyp ->
         andp (checkProofEq luids ruids ctx ityp a1 a2 prf)
              (chargs otyp stack1 stack2 prfs)
        _ -> err "eq app/choice type mismatch"
    _ -> err "checkProofEqSimp: arg list length mismatch"
  pickhead (HNLam{}) (HNLam{}) = FHLamLam
  pickhead (HNLam{}) _ = FHLamApp
  pickhead _ (HNLam{}) = FHAppLam
  pickhead (HNC _ c _) _ = FHC c
  pickhead (HNApp{}) _ = FHApp
  pickhead (HNChoice{}) _ = FHChoice

eqElr :: Elr -> Elr -> Bool
eqElr (Var v1) (Var v2) | v1 == v2 = True
eqElr (Glob gv1) (Glob gv2) | gvId gv1 == gvId gv2 = True
eqElr _ _ = False

elrType :: Context -> Elr -> (MType -> MetaEnv MPB) -> MetaEnv MPB
elrType ctx (Var v) cont = case lookupVarType ctx v of
 Just t -> cont t
 Nothing -> err "elrType: var not in scope"
elrType _ (Glob gv) cont = cont $ gvType gv

checkEqType :: MType -> MType -> MetaEnv MPB
checkEqType typ1 typ2 = do
 typ1 <- expandbind typ1
 typ2 <- expandbind typ2
 case (typ1, typ2) of
  (NotM typ1, NotM typ2) ->
   cheq typ1 typ2
  (Meta _, NotM typ2) ->
   gheadp (False, prioUnifyType, Just (BIUnifyType typ2)) (pbc "checkEqType.flex-rig") typ1 $ \typ1 ->
   cheq typ1 typ2
  (NotM typ1, Meta _) ->
   gheadp (False, prioUnifyType, Just (BIUnifyType typ1)) (pbc "checkEqType.rig-flex") typ2 $ \typ2 ->
   cheq typ1 typ2
  (Meta m1, Meta m2) ->
   return $ PDoubleBlocked m1 m2 (checkEqType typ1 typ2)

cheq typ1 typ2 = case (typ1, typ2) of
 (Ind i1, Ind i2) | i1 == i2 -> ok
 (Bool, Bool) -> ok
 (Map ti1 to1, Map ti2 to2) -> andp (checkEqType ti1 ti2) (checkEqType to1 to2)
 _ -> err "types not equal"


checkForm :: Context -> MType -> MFormula -> MetaEnv MPB
checkForm ctx typ form =
 gheadp (False, prioCheckFormUnknownType, Nothing) (pbc "checkForm.unknownType") typ $ \typ ->
 gheadp (True, prioCheckForm, Just $ BICheckForm typ) (prType (NotM typ) >>= \ptyp -> return $ "checkForm : " ++ ptyp) form $ \form -> case form of
  Lam _ atyp bdy ->
   case typ of
    Map t1 t2 ->
     andp (checkType atyp) (
     andp (checkEqType t1 atyp)
          (checkForm (VarExt atyp : ctx) t2 bdy))
    _ -> err "checkForm: function type needed"
  C _ c [T atyp, F qf] | c == Forall || c == Exists ->
   case typ of
    Bool -> andp (checkType atyp)
                 (checkForm ctx (NotM $ Map atyp typeBool) qf)
    _ -> err "quantifier : Bool"
  C _ Eq [T ctyp, F lhs, F rhs] ->
   case typ of
    Bool -> andp (checkType ctyp) (
            andp (checkForm ctx ctyp lhs)
                 (checkForm ctx ctyp rhs))
    _ -> err "eq : Bool"
  C _ c args ->  -- Top, Bot, And, Or, Implies, Not
   case typ of
    Bool -> gg args
     where
      gg [] = ok
      gg (F a : as) = andp (checkForm ctx typeBool a) (gg as)
    _ -> err "connective : Bool"
  App _ elr args ->
   elrType ctx elr $ \ityp ->
   gg typ ityp args
  Choice _ atyp qf args ->
   andp (checkType atyp) (
   andp (checkForm ctx (NotM $ Map atyp typeBool) qf)
        (gg typ atyp args))
 where
  gg typ ityp args =
   gheadp (True, prioCheckFormArgs, Nothing) (pbc "checkFormArgs") args $ \args -> case args of
    ArgNil ->
     checkEqType (NotM typ) ityp
    ArgCons a as ->
     gheadp (False, prioUnknownType, Nothing) (pbc "checkForm.gg") ityp $ \ityp -> case ityp of
      Map t1 t2 -> andp (checkForm ctx t1 a) (gg typ t2 as)
      _ -> err "checkForm: function type required"

checkType :: MType -> MetaEnv MPB
checkType typ =
 gheadp (True, prioCheckType, Nothing) (pbc "checkType") typ $ \typ ->
 case typ of
  Bool -> ok
  Ind{} -> ok
  Map t1 t2 -> andp (checkType t1) (checkType t2)


