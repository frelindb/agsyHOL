module PrintProof where

import Data.IORef
import Control.Monad (liftM)

import NarrowingSearch
import Syntax


prMeta :: MMetavar a -> (a -> IO String) -> IO String
prMeta m prv = do
 b <- readIORef $ mbind m
 case b of
  Nothing -> return $ "?" ++ show (mid m)
  Just v -> prv v

prProof :: Int -> MetaProof -> IO String
prProof ctx p =
 prMeta p $ \p -> case p of
  Intro p _ -> prIntro ctx p
  Elim hyp p -> do
   hyp <- prHyp ctx hyp
   p <- prProofElim ctx p
   return $ "(elim " ++ hyp ++ " " ++ p ++ ")"
  RAA p -> do
   p <- prProof (ctx + 1) p
   return $ "(RAA (\\#" ++ show ctx ++ "." ++ p ++ "))"

prIntro :: Int -> MetaIntro -> IO String
prIntro ctx p =
 prMeta p $ \p -> case p of
  OrIl p -> do
   p <- prProof ctx p
   return $ "(Or-Il " ++ p ++ ")"
  OrIr p -> do
   p <- prProof ctx p
   return $ "(Or-Ir " ++ p ++ ")"
  AndI p1 p2 -> do
   p1 <- prProof ctx p1
   p2 <- prProof ctx p2
   return $ "(And-I " ++ p1 ++ " " ++ p2 ++ ")"
  ExistsI _ f p -> do
   f <- prForm ctx $ Meta f
   p <- prProof ctx p
   return $ "(Exists-I " ++ f ++ " " ++ p ++ ")"
  ImpliesI p -> do
   p <- prProof (ctx + 1) p
   return $ "(Implies-I (\\#" ++ show ctx ++ "." ++ p ++ "))"
  NotI p -> do
   p <- prProof (ctx + 1) p
   return $ "(Not-I (\\#" ++ show ctx ++ "." ++ p ++ "))"
  ForallI p -> do
   p <- prProof (ctx + 1) p
   return $ "(Forall-I (\\#" ++ show ctx ++ "." ++ p ++ "))"
  TopI ->
   return "Top-I"
  EqI p -> do
   p <- prProofEq ctx p
   return $ "(=-I " ++ p ++ ")"

prHyp :: Int -> MetaHyp -> IO String
prHyp ctx hyp =
 prMeta hyp $ \(Hyp elr _) ->
 case elr of
  HVar v -> return $ "#" ++ show (ctx - v - 1)
  HGlob gh -> return $ ghName gh
  AC typ qf p -> do
   typ <- prType $ Meta typ
   qf <- prForm ctx $ Meta qf
   p <- prProof ctx p
   return $ "(AC " ++ typ ++ " " ++ qf ++ " " ++ p ++ ")"

prProofElim :: Int -> MetaProofElim -> IO String
prProofElim ctx p =
 prMeta p $ \p -> case p of
  Use p -> do
   p <- prProofEqSimp ctx p
   return $ "(use " ++ p ++ ")"
  ElimStep p _ -> prElimStep ctx p

prProofEqElim :: Int -> MetaProofEqElim -> IO String
prProofEqElim ctx p =
 prMeta p $ \p -> case p of
  UseEq _ -> return "use-eq"
  UseEqSym _ -> return "use-eq-sym"
  EqElimStep p _ -> prEqElimStep ctx p

prEqElimStep :: Int -> MetaEqElimStep -> IO String
prEqElimStep ctx p =
 prMeta p $ \p -> case p of
  NTEqElimStep p -> prNTElimStep (prProofEqElim ctx) ctx p

prElimStep :: Int -> MetaElimStep -> IO String
prElimStep ctx p =
 prMeta p $ \p -> case p of
  BotE -> return "Bot-E"
  NotE p -> do
   p <- prProof ctx p
   return $ "(Not-E " ++ p ++ ")"
  OrE p1 p2 -> do
   p1 <- prProof (ctx + 1) p1
   p2 <- prProof (ctx + 1) p2
   return $ "(Or-E " ++ p1 ++ " " ++ p2 ++ ")"
  NTElimStep p -> prNTElimStep (prProofElim ctx) ctx p

prNTElimStep :: (a -> IO String) -> Int -> NTElimStep a -> IO String
prNTElimStep pr ctx p =
 case p of
  AndEl p -> do
   p <- pr p
   return $ "(And-El " ++ p ++ ")"
  AndEr p -> do
   p <- pr p
   return $ "(And-Er " ++ p ++ ")"
  ExistsE _ p -> do
   p <- pr p
   return $ "(Exists-E " ++ p ++ ")"
  ImpliesE p1 p2 -> do
   p1 <- prProof ctx p1
   p2 <- pr p2
   return $ "(Implies-E " ++ p1 ++ " " ++ p2 ++ ")"
  ForallE f p -> do
   f <- prForm ctx $ Meta f
   p <- pr p
   return $ "(Forall-E " ++ f ++ " " ++ p ++ ")"
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

prProofEq :: Int -> MetaProofEq -> IO String
prProofEq ctx p =
 prMeta p $ \p -> case p of
  Simp p -> prProofEqSimp ctx p
  Step hyp elimp simpp eqp -> do
   hyp <- prHyp ctx hyp
   elimp <- prProofEqElim ctx elimp
   simpp <- prProofEqSimp ctx simpp
   eqp <- prProofEq ctx eqp
   return $ "(step " ++ hyp ++ " " ++ elimp ++ " " ++ simpp ++ " " ++ eqp ++ ")"
  BoolExt p1 p2 -> do
   p1 <- prProof (ctx + 1) p1
   p2 <- prProof (ctx + 1) p2
   return $ "(bool-ext " ++ p1 ++ " " ++ p2 ++ ")"
  FunExt p -> do
   p <- prProofEq (ctx + 1) p
   return $ "(fun-ext " ++ p ++ ")"

prProofEqSimp :: Int -> ProofEqSimp -> IO String
prProofEqSimp ctx (Comp p _ _) =
 prMeta p $ \p -> case p of
  SimpLam em p -> do
   p <- prProofEq (ctx + 1) p
   return $ "(simp-lam " ++ pem em ++ p ++ ")"
   where
    pem EMNone = ""
    pem EMLeft = "{- eta-conv lhs -} "
    pem EMRight = "{- eta-conv rhs -} "
  SimpCons c ps -> do
   ps <- mapM (prProofEq ctx) ps
   return $ "(simp-" ++ show c ++ concat (map (" " ++) ps) ++ ")"
  SimpApp ps -> do
   ps <- prProofEqs ctx ps
   return $ "(simp-app" ++ ps ++ ")"
  SimpChoice p ps -> do
   p <- prProofEq ctx p
   ps <- prProofEqs ctx ps
   return $ "(simp-choice " ++ p ++ ps ++ ")"

prProofEqs :: Int -> MetaProofEqs -> IO String
prProofEqs ctx p =
 prMeta p $ \p -> case p of
  PrEqNil -> return ""
  PrEqCons p ps -> do
   p <- prProofEq ctx p
   ps <- prProofEqs ctx ps
   return $ " " ++ p ++ ps

prForm :: Int -> MFormula -> IO String
prForm ctx f =
 expandbind f >>= \f -> case f of
  Meta m -> return $ "?" ++ show (mid m)
  NotM (Lam muid t bdy) -> do
   t <- prType t
   bdy <- prForm (ctx + 1) bdy
   return $ "(\\#" ++ pmuid muid ++ show ctx ++ ":" ++ t ++ "." ++ bdy ++ ")"
  NotM (C muid c args) -> do
   args <- mapM (\arg -> case arg of
     F f -> prForm ctx f >>= \f -> return $ f
     T t -> prType t >>= \t -> return $ t
    ) args
   return $ "(" ++ show c ++ pmuid muid ++ concat (map (" " ++) args) ++ ")"
  NotM (App muid elr args) -> do
   args <- prArgs ctx args
   let pelr = case elr of
              Var i -> "#" ++ show (ctx - i - 1)
              Glob gv -> gvName gv
   return $ "(" ++ pelr ++ pmuid muid ++ args ++ ")"

  NotM (Choice muid typ qf args) -> do
   typ <- prType typ
   qf <- prForm ctx qf
   args <- prArgs ctx args
   return $ "(choice" ++ pmuid muid ++ " " ++ typ ++ " " ++ qf ++ args ++ ")"
 where
  pmuid _ = ""

prArgs :: Int -> MArgs -> IO String
prArgs ctx xs =
 expandbind xs >>= \xs -> case xs of
  Meta m -> return $ "[?" ++ show (mid m) ++ "]"
  NotM ArgNil -> return ""
  NotM (ArgCons x xs) -> do
   x <- prForm ctx x
   xs <- prArgs ctx xs
   return $ " " ++ x ++ xs

prType :: MType -> IO String
prType t =
 expandbind t >>= \t -> case t of
  Meta m -> return $ "?" ++ show (mid m)
  NotM (Ind i) -> return $ "$i" ++ if i >= 0 then show i else ""
  NotM Bool -> return "$o"
  NotM (Map t1 t2) -> do
   t1 <- prType t1
   t2 <- prType t2
   return $ "(" ++ t1 ++ ">"  ++ t2 ++ ")"

prProblem :: Problem -> IO String
prProblem pr = do
 globvars <- mapM prGlobVar $ prGlobVars pr
 globhyps <- mapM prGlobHyp $ prGlobHyps pr
 conjs <- mapM (\(cn, form) -> prForm 0 form >>= \form -> return (cn ++ "\n" ++ form)) $ prConjectures pr
 return $ "global variables\n" ++ unlines globvars ++
          "\nglobal hypotheses\n" ++ unlines globhyps ++
          "\nconjectures\n" ++ unlines conjs

prGlobVar :: GlobVar -> IO String
prGlobVar gv = do
 typ <- prType $ gvType gv
 return $ gvName gv ++ " : " ++ typ

prGlobHyp :: GlobHyp -> IO String
prGlobHyp gh = do
 form <- prForm 0 $ ghForm gh
 return $ ghName gh ++ " : " ++ form ++ " (" ++ show (ghGenCost gh) ++ ")"

-- ------------------------------------

prCFormula :: Int -> CFormula -> IO String
prCFormula ctx (Cl env form) =
 expandbind form >>= \form -> case form of
  Meta m -> do
   env <- prEnv env
   return $ env ++ "?" ++ show (mid m)
  NotM (Lam muid t bdy) -> do
   t <- prType t
   bdy <- prCFormula (ctx + 1) (Cl (Skip : env) bdy)
   return $ "(\\#" ++ pmuid muid ++ show ctx ++ ":" ++ t ++ "." ++ bdy ++ ")"
  NotM (C muid c args) -> do
   args <- mapM (\arg -> case arg of
     F f -> prCFormula ctx (Cl env f) >>= \f -> return $ f
     T t -> prType t >>= \t -> return $ t
    ) args
   return $ "(" ++ show c ++ pmuid muid ++ concat (map (" " ++) args) ++ ")"
  NotM (App muid elr args) -> do
   elr <- case elr of
           Var i -> case doclos env i of
            Left i -> return $ "#" ++ show (ctx - i - 1)
            Right form -> do
             form <- prCFormula ctx form
             return $ "{" ++ form ++ "}"
           Glob gv -> return $ gvName gv
   args <- prargs args
   return $ "(" ++ elr ++ pmuid muid ++ args ++ ")"
  NotM (Choice muid typ qf args) -> do
   typ <- prType typ
   qf <- prCFormula ctx (Cl env qf)
   args <- prargs args
   return $ "(choice" ++ pmuid muid ++ " " ++ typ ++ " " ++ qf ++ args ++ ")"
 where
  pmuid _ = ""

  prargs args =
   expandbind args >>= \args -> case args of 
    Meta m -> do
     env <- prEnv env
     return $ env ++ "?" ++ show (mid m)
    NotM ArgNil -> return ""
    NotM (ArgCons x xs) -> do
     x <- prCFormula ctx (Cl env x)
     xs <- prargs xs
     return $ " " ++ x ++ xs
prCFormula ctx (CApp c1 c2) = do
 c1 <- prCFormula ctx c1
 c2 <- prCFormula ctx c2
 return $ "(capp " ++ c1 ++ " " ++ c2 ++ ")"
prCFormula ctx (CNot c) = do
 c <- prCFormula ctx c
 return $ "(cnot " ++ c ++ ")"
prCFormula _ (CHN _) = return "<CHN>"

prEnv :: Env -> IO String
prEnv = g 0
 where
  g _ [] = return ""
  g i (Skip : env) = g (i + 1) env
  g i (Sub f : env) = do
   env <- g (i + 1) env
   f <- prCFormula 0 f
   return $ "[@" ++ show i ++ "=" ++ f ++ "]" ++ env
  g i (Lift n : env) = do
   env <- g i env
   return $ "[L" ++ show n ++ "]" ++ env

prCtx :: Context -> IO String
prCtx ctx = g (length ctx - 1) ctx
 where
  g _ [] = return ""
  g i (VarExt t : ctx) = do
   ctx <- g (i - 1) ctx
   t <- prType t
   return $ ctx ++ "[#" ++ show i ++ ":" ++ t ++ "]"
  g i (HypExt f : ctx) = do
   ctx <- g (i - 1) ctx
   f <- prCFormula i f
   return $ ctx ++ "[#" ++ show i ++ ":" ++ f ++ "]"

