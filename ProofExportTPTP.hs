module ProofExportTPTP where

-- printa TPTP formler
-- omvandla context plus ovrigt for varje judgement till en formel med kvantifieringar och implikationer for variabler och hypoteser
-- fyll i namnet pa deduktionssteget
-- referera till barnjudgementen
-- ge ett nummer till varje steg
-- inkludera de definitioner som anvands
-- inkludera globala variabler och hypoteser som anvands
-- inkludera conjectures
-- gor ett steg dar definitioner expanderas och formlerna likriktas (t ex X<=>Y till X=>Y&Y=>X) i varje hypotes och conjecture
-- gor ett transformeringssteg for varje hypotes och conjecture (eller ett steg for varje atomisk transformering)

import Control.Monad

import Syntax
import TPTPSyntax
import ProofExport



tptpproof :: [ThfAnnotated] -> Problem -> Problem -> [(String, MetaProof)] -> IO ()
tptpproof tptpprob nontrprob trprob prfs = do
 putStrLn "Printing TPTP proofs not implemented yet."
{-
 usedhyps <- liftM concat $ mapM (findusedglobsProof . snd) prfs
 let necessary_hyps = filter (\gh -> ghName gh `elem` usedhyps) (prGlobHyps trprob)
 usedvars <- liftM concat $ mapM findusedglobsFormula (map snd (prConjectures trprob) ++ map ghForm necessary_hyps)
 let necessary_vars = filter (\gv -> gvName gv `elem` usedvars) (prGlobVars trprob)
     trprob_sliced = trprob {prGlobVars = necessary_vars, prGlobHyps = necessary_hyps}
 putStrLn $ show usedhyps
 putStrLn $ show usedvars
 return ()
-}

