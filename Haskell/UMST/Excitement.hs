-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Selection under cost, twin of Lean/Excitement.lean, Coq/Excitement.v and Agda/Excitement.agda: selection returns
-- the evidence-tagged candidate of least global free energy (ties by id) when it lowers the source's free energy, and
-- a residue otherwise. Exact over 'Rational'; the joint free energy is a parameter. Candidates are moves the gate
-- admits (Haskell carries no proof; the test suite generates admitted moves).
module UMST.Excitement
  ( Residue (..)
  , Cand (..)
  , candEnergy
  , pickMin
  , select
  ) where

-- | Why selection returns no candidate.
data Residue
  = NoCandidates
  | AllInadmissible
  | AllExcludedByCBF
  | AllExcludedByDEC
  | UntaggedConstant
  | NoStrictImprovement
  deriving (Eq, Show)

-- | A candidate move: its id, target, ledger total and whether it carries evidence.
data Cand s = Cand { cid :: Int, tgt :: s, ledger :: Rational, evidenceTagged :: Bool }
  deriving (Show)

candEnergy :: (s -> Rational) -> Cand s -> Rational
candEnergy energy c = energy (tgt c) + ledger c

pickMin :: (s -> Rational) -> Maybe (Cand s) -> Cand s -> Maybe (Cand s)
pickMin _ Nothing c = Just c
pickMin energy (Just b) c
  | fc < fb = Just c
  | fb < fc = Just b
  | cid c < cid b = Just c
  | otherwise = Just b
  where
    fc = candEnergy energy c
    fb = candEnergy energy b

-- | 'Left' is the selected candidate (Lean's @Sum.inl@), 'Right' the residue.
select :: (s -> Rational) -> s -> [Cand s] -> Either (Cand s) Residue
select _ _ [] = Right NoCandidates
select energy src cands = case filter evidenceTagged cands of
  [] -> Right (if any (not . evidenceTagged) cands then AllInadmissible else UntaggedConstant)
  tagged -> case foldl (pickMin energy) Nothing tagged of
    Nothing -> Right AllInadmissible
    Just c -> if candEnergy energy c < energy src then Left c else Right NoStrictImprovement
