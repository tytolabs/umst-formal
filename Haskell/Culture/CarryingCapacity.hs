-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- The culture carrying-capacity bound on exact rationals, with ln 2 a parameter; twin of
-- Lean/Culture/CarryingCapacity.lean, Coq/Culture/CarryingCapacity.v and Agda/Culture/CarryingCapacity.agda.
-- test/CarryingCapacityProps.hs decides the statements on random windows of lives.
module Culture.CarryingCapacity
  ( liveTicks
  , meanLiveBound
  , ln2Lower
  , ln2Upper
  ) where

-- | The live count summed over a window's ticks: the sum of the lives' durations within it.
liveTicks :: [Rational] -> Rational
liveTicks = sum

-- | The carrying-capacity bound tau (W / (l (1 - i)) + N_T / T).
meanLiveBound :: Rational -> Rational -> Rational -> Rational -> Rational -> Int -> Rational
meanLiveBound tau t w l i alive = tau * (w / (l * (1 - i)) + fromIntegral alive / t)

-- | A rational enclosure of ln 2 (Lean: log_two_mem_enclosure).
ln2Lower, ln2Upper :: Rational
ln2Lower = 6931471803 / 10000000000
ln2Upper = 6931471808 / 10000000000
