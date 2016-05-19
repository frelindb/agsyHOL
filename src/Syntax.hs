{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module Syntax where

import Control.Monad

import NarrowingSearch


-- -----------------------

data Blk = BIEnv [GlobHyp]
         | BICtx Context
         | BIForm HNFormula
         | BIUnifyForm [Int] HNFormula Env
         | BIUnifyType Type
         | BICheckForm Type
         | BIComputed
         | BISimpArgs Bool  -- shoud be cons (otherwise nil)
         | BIFormHead FormHead

data FormHead = FHLamLam | FHLamApp | FHAppLam | FHC Cons | FHApp | FHChoice


instance Show Blk where
 show (BIEnv{}) = "BIEnv"
 show (BICtx{}) = "BICtx"
 show (BIForm{}) = "BIForm"
 show (BIUnifyForm{}) = "BIUnifyForm"
 show (BIUnifyType{}) = "BIUnifyType"
 show (BICheckForm{}) = "BICheckForm"
 show (BIComputed{}) = "BIComputed"

data GenCost = GCStop
             | GCSubProb Int GenCost
             | GCFork GenCost GenCost
             | GCLocalHyp
 deriving Show

-- -----------------------

type MMetavar a = Metavar a Blk
type MMM a = MM a Blk
type MMB a = MB a Blk
type MPB = PB Blk

-- -----------------------

data Problem = Problem {prName :: String, prIndSets :: Int, prGlobVars :: [GlobVar], prGlobHyps :: [GlobHyp], prConjectures :: [(String, MFormula)]}

type MUId = Maybe Int
nu = Nothing

data Elr = Var Int
         | Glob GlobVar

data Type = Ind Int
          | Bool
          | Map MType MType
type MType = MMM Type
type MetaType = MMetavar Type

data Cons = Top | Bot | And | Or | Implies | Not | Forall | Exists | Eq
 deriving (Eq, Show)
 -- (Lam [T _, Bind _])
 -- Top []
 -- Bot []
 -- And [F _, F _]
 -- Or [F _, F _]
 -- Implies [F _, F _]
 -- Not [F _]
 -- Forall [T _, F _]
 -- Exists [T _, F _]
 -- Eq [T _, F _, F _]
 -- (Choice [T _, F _])

data Formula = C MUId Cons [FormulaArg MFormula]
             | App MUId Elr MArgs
             | Choice MUId MType MFormula MArgs
             | Lam MUId MType MFormula
type MetaFormula = MMetavar Formula
type MFormula = MMM Formula

data FormulaArg a = F a
                  | T MType

data Args = ArgNil
          | ArgCons MFormula MArgs
type MArgs = MMM Args

data GlobVar = GlobVar {gvName :: String, gvType :: MType, gvId :: Int}

-- -----------------------

data Proof = Intro MetaIntro
           | Elim MetaHyp MetaProofElim
           | RAA MetaProof
type MetaProof = MMetavar Proof

data Intro = OrIl MetaProof
           | OrIr MetaProof
           | AndI MetaProof MetaProof
           | ExistsI MetaFormula MetaProof
           | ImpliesI MetaProof
           | NotI MetaProof
           | ForallI MetaProof
           | TopI
           | EqI MetaProofEq
type MetaIntro = MMetavar Intro

data ProofElim = Use MetaProofEqSimp
               | ElimStep MetaElimStep
type MetaProofElim = MMetavar ProofElim

data ElimStep = BotE
              | NotE MetaProof
              | OrE MetaProof MetaProof
              | NTElimStep (NTElimStep MetaProofElim)
type MetaElimStep = MMetavar ElimStep

data ProofEqElim = UseEq
                 | UseEqSym
                 | EqElimStep MetaEqElimStep
type MetaProofEqElim = MMetavar ProofEqElim

data EqElimStep = NTEqElimStep (NTElimStep MetaProofEqElim)
type MetaEqElimStep = MMetavar EqElimStep

data NTElimStep a = AndEl a
                  | AndEr a
                  | ExistsE a
                  | ImpliesE MetaProof a
                  | ForallE MetaFormula a
                  | InvBoolExtl MetaProof a
                  | InvBoolExtr MetaProof a
                  | InvFunExt MetaFormula a

data ProofEq = Simp MetaProofEqSimp
             | Step MetaHyp MetaProofEqElim MetaProofEqSimp MetaProofEq
             | BoolExt MetaProof MetaProof
             | FunExt MetaProofEq
type MetaProofEq = MMetavar ProofEq

data ProofEqs = PrEqNil
              | PrEqCons MetaProofEq MetaProofEqs
type MetaProofEqs = MMetavar ProofEqs

data ProofEqSimp = SimpCons Cons [MetaProofEq]
                 | SimpApp MetaProofEqs
                 | SimpChoice MetaProofEq MetaProofEqs
                 | SimpLam EtaMode MetaProofEq
type MetaProofEqSimp = MMetavar ProofEqSimp

data EtaMode = EMNone | EMLeft | EMRight

data HElr = HVar Int
          | HGlob GlobHyp
          | AC MetaType MetaFormula MetaProof

data Hyp = Hyp HElr CFormula
type MetaHyp = MMetavar Hyp

data GlobHyp = GlobHyp {ghName :: String, ghForm :: MFormula, ghId :: Int, ghGenCost :: GenCost}

-- -----------------------

type Context = [CtxExt]

data CtxExt = VarExt MType
            | HypExt CFormula

data CFormula = Cl Env MFormula
              | CApp CFormula CFormula  -- AC: MFormula MFormula, ExistsI: CFormula MFormula, ForallI: CFormula MFormula, ExistsE: CFormula CFormula, ForallE: CFormula MFormula
              | CNot CFormula
              | CHN HNFormula

data CArgs = ClA Env MArgs

type Env = [EnvElt]
data EnvElt = Skip
            | Sub CFormula
            | Lift Int

data HNFormula = HNC MUId Cons [FormulaArg CFormula]
               | HNApp MUId Elr [CArgs]
               | HNChoice MUId MType CFormula [CArgs]
               | HNLam MUId MType CFormula

data HNArgs = HNNil
            | HNCons CFormula [CArgs]

typeBool = NotM Bool

cl :: MFormula -> CFormula
cl f = Cl [] f

formBot = NotM (C nu Bot [])

-- -----------------------

lift :: Int -> CFormula -> CFormula
lift 0 f = f
lift n (Cl env f) = Cl (Lift n : env) f
lift n (CApp c1 c2) = CApp (lift n c1) (lift n c2)
lift n (CNot c) = CNot (lift n c)
lift n (CHN f) =
 case f of
  HNApp muid elr args -> CHN $ HNApp muid lelr (map (\(ClA env x) -> ClA (Lift n : env) x) args)
   where
    lelr = case elr of
            Var i -> Var (i + n)
            Glob g -> Glob g
  HNChoice muid typ qf args -> CHN $ HNChoice muid typ (lift n qf) (map (\(ClA env x) -> ClA (Lift n : env) x) args)

sub :: CFormula -> CFormula -> CFormula
sub sf (Cl (Skip : env) f) = Cl (Sub sf : env) f

doclos :: Env -> Int -> Either Int CFormula
doclos = f 0
 where
  f ns [] i = Left (ns + i)
  f ns (Lift n : xs) i = f (ns + n) xs i
  f ns (Sub s : _) 0 = Right (lift ns s)
  f ns (Skip : _) 0 = Left ns
  f ns (Skip : xs) i = f (ns + 1) xs (i - 1)
  f ns (Sub _ : xs) i = f ns xs (i - 1)

univar :: Env -> Int -> Maybe Int
univar cl v = f cl v 0
 where
 f [] v v' = Just (v' + v)
 f (Lift n : _) v v' | v < n = Nothing
 f (Lift n : xs) v v' = f xs (v - n) v'
 f (Sub _ : xs) v v' = f xs v (v' + 1)
 f (Skip : _) 0 v' = Just v'
 f (Skip : xs) v v' = f xs (v - 1) (v' + 1)

subsvars :: Env -> [Int]
subsvars = f 0
 where
  f n [] = []
  f n (Lift _ : xs) = f n xs
  f n (Sub _ : xs) = n : f (n + 1) xs
  f n (Skip : xs) = f (n + 1) xs

lookupVarType :: Context -> Int -> Maybe MType
lookupVarType [] _ = Nothing
lookupVarType (VarExt t : _) 0 = Just t
lookupVarType (_ : ctx) n = lookupVarType ctx (n - 1)

-- ----------------------------

probsize :: Problem -> Int
probsize pr = sum (map sgv (prGlobVars pr)) + sum (map sgh (prGlobHyps pr)) + sum (map (sf . snd) (prConjectures pr))
 where
 sgv gv = st $ gvType gv
 sgh gh = sf $ ghForm gh
 sf (NotM f) = case f of
  C _ _ args -> 1 + sum (map sa args)
  App _ _ args -> 1 + sa2 args
  Lam _ t f -> st t + sf f
 sa (F f) = sf f
 sa (T t) = st t
 sa2 (NotM ArgNil) = 0
 sa2 (NotM (ArgCons f as)) = sf f + sa2 as
 st t = 0

-- ------------------------------

instance ExpandMetas MType where
 expandmetas t =
  expandmm t $ \t -> case t of
   Map t1 t2 -> do
    t1 <- expandmetas t1
    t2 <- expandmetas t2
    return $ NotM $ Map t1 t2
   _ ->
    return $ NotM t

instance ExpandMetas MFormula where
 expandmetas f =
  expandmm f $ \f -> case f of
   C uid c as -> do
    as <- mapM (\a -> case a of
                       F f -> liftM F $ expandmetas f
                       T t -> liftM T $ expandmetas t)
               as
    return $ NotM $ C uid c as
   App uid elr as -> do
    as <- expandmetas as
    return $ NotM $ App uid elr as
   Choice uid t f as -> do
    t <- expandmetas t
    f <- expandmetas f
    as <- expandmetas as
    return $ NotM $ Choice uid t f as
   Lam uid t f -> do
    t <- expandmetas t
    f <- expandmetas f
    return $ NotM $ Lam uid t f

instance ExpandMetas MArgs where
 expandmetas f =
  expandmm f $ \f -> case f of
   ArgNil ->
    return $ NotM ArgNil
   ArgCons f fs -> do
    f <- expandmetas f
    fs <- expandmetas fs
    return $ NotM $ ArgCons f fs


instance ExpandMetas CFormula where
 expandmetas cf =
  case cf of
   Cl env f -> do
    env <- expandmetas env
    f <- expandmetas f
    return $ Cl env f
   CApp f1 f2 -> do
    f1 <- expandmetas f1
    f2 <- expandmetas f2
    return $ CApp f1 f2
   CNot f -> do
    f <- expandmetas f
    return $ CNot f
   CHN f -> do
    f <- expandmetas f
    return $ CHN f

instance ExpandMetas Env where
 expandmetas = mapM g
  where
   g (Sub f) = do
    f <- expandmetas f
    return $ Sub f
   g x =
    return x

instance ExpandMetas HNFormula where
 expandmetas f =
  case f of
   HNC uid c as -> do
    as <- mapM (\a -> case a of
                       F f -> liftM F $ expandmetas f
                       T t -> liftM T $ expandmetas t)
               as
    return $ HNC uid c as
   HNApp uid elr as -> do
    as <- mapM g as
    return $ HNApp uid elr as
   HNChoice uid t f as -> do
    t <- expandmetas t
    f <- expandmetas f
    as <- mapM g as
    return $ HNChoice uid t f as
   HNLam uid t f -> do
    t <- expandmetas t
    f <- expandmetas f
    return $ HNLam uid t f
  where
   g (ClA env as) = do
    env <- expandmetas env
    as <- expandmetas as
    return $ ClA env as


instance ExpandMetas MetaType where
 expandmetas t = do
  NotM t <- expandmetas (Meta t)
  crmeta t

instance ExpandMetas MetaFormula where
 expandmetas f = do
  NotM f <- expandmetas (Meta f)
  crmeta f

instance ExpandMetas MetaProof where
 expandmetas p =
  expandmeta p $ \p -> case p of
   Intro p -> do
    p <- expandmetas p
    crmeta $ Intro p
   Elim h p -> do
    h <- expandmetas h
    p <- expandmetas p
    crmeta $ Elim h p
   RAA p -> do
    p <- expandmetas p
    crmeta $ RAA p

instance ExpandMetas MetaIntro where
 expandmetas p =
  expandmeta p $ \p -> case p of
   OrIl p -> do
    p <- expandmetas p
    crmeta $ OrIl p
   OrIr p -> do
    p <- expandmetas p
    crmeta $ OrIr p
   AndI p1 p2 -> do
    p1 <- expandmetas p1
    p2 <- expandmetas p2
    crmeta $ AndI p1 p2
   ExistsI f p -> do
    f <- expandmetas f
    p <- expandmetas p
    crmeta $ ExistsI f p
   ImpliesI p -> do
    p <- expandmetas p
    crmeta $ ImpliesI p
   NotI p -> do
    p <- expandmetas p
    crmeta $ NotI p
   ForallI p -> do
    p <- expandmetas p
    crmeta $ ForallI p
   TopI ->
    crmeta TopI
   EqI p -> do
    p <- expandmetas p
    crmeta $ EqI p

instance ExpandMetas MetaProofElim where
 expandmetas p =
  expandmeta p $ \p -> case p of
   Use p -> do
    p <- expandmetas p
    crmeta $ Use p
   ElimStep p -> do
    p <- expandmetas p
    crmeta $ ElimStep p

instance ExpandMetas MetaElimStep where
 expandmetas p =
  expandmeta p $ \p -> case p of
   BotE ->
    crmeta BotE
   NotE p -> do
    p <- expandmetas p
    crmeta $ NotE p
   OrE p1 p2 -> do
    p1 <- expandmetas p1
    p2 <- expandmetas p2
    crmeta $ OrE p1 p2
   NTElimStep p -> do
    p <- expandmetas p
    crmeta $ NTElimStep p

instance ExpandMetas MetaProofEqElim where
 expandmetas p =
  expandmeta p $ \p -> case p of
   UseEq ->
    crmeta UseEq
   UseEqSym ->
    crmeta UseEqSym
   EqElimStep p -> do
    p <- expandmetas p
    crmeta $ EqElimStep p

instance ExpandMetas MetaEqElimStep where
 expandmetas p =
  expandmeta p $ \p -> case p of
   NTEqElimStep p -> do
    p <- expandmetas p
    crmeta $ NTEqElimStep p

instance ExpandMetas a => ExpandMetas (NTElimStep a) where
 expandmetas p =
  case p of
   AndEl p -> do
    p <- expandmetas p
    return $ AndEl p
   AndEr p -> do
    p <- expandmetas p
    return $ AndEr p
   ExistsE p -> do
    p <- expandmetas p
    return $ ExistsE p
   ImpliesE p1 p2 -> do
    p1 <- expandmetas p1
    p2 <- expandmetas p2
    return $ ImpliesE p1 p2
   ForallE f p -> do
    f <- expandmetas f
    p <- expandmetas p
    return $ ForallE f p
   InvBoolExtl p1 p2 -> do
    p1 <- expandmetas p1
    p2 <- expandmetas p2
    return $ InvBoolExtl p1 p2
   InvBoolExtr p1 p2 -> do
    p1 <- expandmetas p1
    p2 <- expandmetas p2
    return $ InvBoolExtr p1 p2
   InvFunExt f p -> do
    f <- expandmetas f
    p <- expandmetas p
    return $ InvFunExt f p
   
instance ExpandMetas MetaProofEq where
 expandmetas p =
  expandmeta p $ \p -> case p of
   Simp p -> do
    p <- expandmetas p
    crmeta $ Simp p
   Step h p1 p2 p3 -> do
    h <- expandmetas h
    p1 <- expandmetas p1
    p2 <- expandmetas p2
    p3 <- expandmetas p3
    crmeta $ Step h p1 p2 p3
   BoolExt p1 p2 -> do
    p1 <- expandmetas p1
    p2 <- expandmetas p2
    crmeta $ BoolExt p1 p2
   FunExt p -> do
    p <- expandmetas p
    crmeta $ FunExt p

instance ExpandMetas MetaProofEqs where
 expandmetas p =
  expandmeta p $ \p -> case p of
   PrEqNil ->
    crmeta PrEqNil
   PrEqCons p ps -> do
    p <- expandmetas p
    ps <- expandmetas ps
    crmeta $ PrEqCons p ps

instance ExpandMetas MetaProofEqSimp where
 expandmetas p =
  expandmeta p $ \p -> case p of
   SimpCons c ps -> do
    ps <- mapM expandmetas ps
    crmeta $ SimpCons c ps
   SimpApp ps -> do
    ps <- expandmetas ps
    crmeta $ SimpApp ps
   SimpChoice p ps -> do
    p <- expandmetas p
    ps <- expandmetas ps
    crmeta $ SimpChoice p ps
   SimpLam em p -> do
    p <- expandmetas p
    crmeta $ SimpLam em p

instance ExpandMetas MetaHyp where
 expandmetas p =
  expandmeta p $ \p -> case p of
   Hyp elr cf -> do
    elr <- case elr of
            AC typ qf p -> do
             typ <- expandmetas typ
             qf <- expandmetas qf
             p <- expandmetas p
             return $ AC typ qf p
            _ -> return elr
    cf <- expandmetas cf
    crmeta $ Hyp elr cf

