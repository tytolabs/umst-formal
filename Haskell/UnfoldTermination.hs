-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Law L-E on exact rationals; twin of Lean/UnfoldTermination.lean, Coq/UnfoldTermination.v and
-- Agda/UnfoldTermination.agda. A budgeted run spends at least the enclosed Landauer floor per step and stops when the
-- next step would exceed the budget; test/UnfoldTerminationProps.hs checks its step count against floor (B / eps).
module UnfoldTermination
  ( ln2Lower
  , floorLower
  , maxSteps
  , runBudgeted
  ) where

-- | The lower end of the enclosure of ln 2 (Lean: ln2Lower_lt_log_two).
ln2Lower :: Rational
ln2Lower = 6931471803 / 10000000000

-- | The enclosed Landauer floor of a step erasing b bits at kT: b kT ln2Lower.
floorLower :: Rational -> Integer -> Rational
floorLower kT b = fromInteger b * kT * ln2Lower

-- | The L-E step bound floor (B / eps).
maxSteps :: Rational -> Rational -> Integer
maxSteps budget eps = floor (budget / eps)

-- | Run steps with the given spends while the budget allows; the number of steps taken.
runBudgeted :: Rational -> [Rational] -> Int
runBudgeted budget = go 0 0
  where
    go n _ [] = n
    go n acc (w : ws)
      | acc + w <= budget = go (n + 1) (acc + w) ws
      | otherwise = n
