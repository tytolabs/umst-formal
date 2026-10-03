-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- History moves admitted by the one second law; twin of Lean/Urge/AdmitKleisli.lean, Coq/UrgeAdmitKleisli.v and
-- Agda/UrgeAdmitKleisli.agda. A history move carries the gate admissibility of its head move and the erasure that
-- pays for it; the move is admissible exactly when that erasure is an instance of the one predicate
-- 'UMST.Process.secondLaw'. History head moves are Kleisli arrows over thermodynamic states
-- ('UMST.Chem.Kleisli'), whose category laws hold pointwise.
--
-- Haskell carries no proof: the gate admissibility of the head move is checked by the smart constructor
-- 'mkHistoryTransition', which refuses a move the gate does not pass.
module UMST.UrgeAdmitKleisli
  ( HistorySnapshot (..)
  , HistoryTransition
  , priorSnapshot
  , postSnapshot
  , erasureProcess
  , erasedDist
  , mkHistoryTransition
  , admissibleHistoryTransition
  , admitIdentity
  ) where

import UMST.Chem.Kleisli (KleisliArrow, interactIdentity)
import UMST.Concrete (ThermodynamicState, AdmissibilityResult (..), gateCheck)
import qualified UMST.Process as P

-- | Content-addressed history snapshot: commit id and gate-checked head state.
data HistorySnapshot = HistorySnapshot { commitId :: Int, snapHead :: ThermodynamicState }
  deriving (Show)

-- | A move of the history head and the erasure that pays for it: the head move passes the gate, and the erasure
-- erases the distribution 'erasedDist' (the information the move discards).
data HistoryTransition = HistoryTransition
  { priorSnapshot :: HistorySnapshot
  , postSnapshot :: HistorySnapshot
  , erasureProcess :: P.ErasureProcess
  , erasedDist :: P.ProbDist2
  }
  deriving (Show)

-- | A history move, when the gate passes its head move (the gate is evaluated at a unit step, as in
-- "UMST.Process").
mkHistoryTransition :: HistorySnapshot -> HistorySnapshot -> P.ErasureProcess -> P.ProbDist2 -> Maybe HistoryTransition
mkHistoryTransition old new e p
  | accepted (gateCheck (snapHead old) (snapHead new) 1) = Just (HistoryTransition old new e p)
  | otherwise = Nothing

-- | A history move is admissible when its erasure is an instance of the one second law.
admissibleHistoryTransition :: HistoryTransition -> Bool
admissibleHistoryTransition t = P.secondLaw (P.Erase (erasureProcess t)) (P.Erasure (erasedDist t))

-- | Kleisli identity on history head states.
admitIdentity :: KleisliArrow
admitIdentity = interactIdentity
