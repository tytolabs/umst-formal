-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- The cost of information; twin of Lean/CostOfInformation.lean, Coq/CostOfInformation.v and
-- Agda/CostOfInformation.agda. An erasure obeying the one predicate removes at most 1/(k_B T) nats per joule;
-- erasing b bits costs at least b k_B T ln 2 joules.
module UMST.CostOfInformation
  ( uniformN
  , diracN
  , entropyDropJoules
  , informationPerJoule
  , bitErasure
  ) where

import UMST.Process

-- | The uniform distribution on n states (n positive); it carries ln n nats.
uniformN :: Int -> ProbDist
uniformN n = ProbDist (replicate n (1 / fromIntegral n))

-- | The point distribution on n + 1 states, at the first state.
diracN :: Int -> ProbDist
diracN n = ProbDist (1 : replicate n 0)

-- | k_B T times the entropy a transformation removes, in joules.
entropyDropJoules :: HeatBath -> ProbDist -> ProbDist -> Double
entropyDropJoules b p q = kB * bathTemp b * (shannon p - shannon q)

-- | Nats removed per joule of work dissipated (the work W is in units of k_B times kelvin, k_B W in joules).
informationPerJoule :: Double -> ProbDist -> ProbDist -> Double
informationPerJoule w p q = (shannon p - shannon q) / (kB * w)

-- | The erasure of b bits: the uniform distribution on 2^b states to a point.
bitErasure :: Int -> Prior
bitErasure bits = Transformation (uniformN (2 ^ bits)) (diracN (2 ^ bits - 1))
