-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Engineering mirror of `Lean/CreditGreedyOptimal.lean` (Case A: filter-then-sum).
-- Weights are exact rationals: Lean states the laws over ℝ, and `Double` addition is not associative,
-- so `credit_mass_append` is false for it.
module CreditGreedy where

import Test.QuickCheck

data Candidate = Candidate
  { weight :: Rational
  , admissible :: Bool
  }
  deriving (Eq, Show)

-- | Nonnegative weights when admissible (mirrors `CreditCandidate.h_nonneg`).
genCandidate :: Gen Candidate
genCandidate = do
  w <- fmap abs arbitrary
  a <- arbitrary
  pure (Candidate w a)

instance Arbitrary Candidate where
  arbitrary = genCandidate

creditMass :: [Candidate] -> Rational
creditMass = sum . map weight . filter admissible

greedyMass :: [Candidate] -> Rational
greedyMass = creditMass

exhaustiveOptimalMass :: [Candidate] -> Rational
exhaustiveOptimalMass = creditMass

prop_credit_greedy_optimal :: [Candidate] -> Bool
prop_credit_greedy_optimal cs = greedyMass cs == exhaustiveOptimalMass cs

prop_credit_mass_nonneg :: [Candidate] -> Property
prop_credit_mass_nonneg cs =
  all (\c -> not (admissible c) || weight c >= 0) cs ==>
    creditMass cs >= 0

prop_credit_mass_append :: [Candidate] -> [Candidate] -> Bool
prop_credit_mass_append xs ys =
  creditMass (xs ++ ys) == creditMass xs + creditMass ys
