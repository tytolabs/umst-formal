-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- The thermodynamic uncertainty relation (A. C. Barato and U. Seifert, Phys. Rev. Lett. 114, 158101 (2015)) for the
-- biased random walk, twin of Lean/UncertaintyRelation.lean, Coq/UncertaintyRelation.v and
-- Agda/UncertaintyRelation.agda. Rates kPlus, kMinus > 0; mean current (kPlus - kMinus) t and variance
-- (kPlus + kMinus) t (Skellam 1946); entropy production (kPlus - kMinus)(ln kPlus - ln kMinus) t (Schnakenberg 1976).
-- The general TUR for any current of any finite Markov jump process is a typed absence (FORMAL-TUR-GENERAL).
module UMST.UncertaintyRelation
  ( BiasedWalk (..)
  , meanCurrent
  , varCurrent
  , entropyProduction
  , logMeanGap
  , turGap
  ) where

-- | The biased random walk by its forward and backward rates (both positive).
data BiasedWalk = BiasedWalk { kPlus :: Double, kMinus :: Double }
  deriving (Show)

meanCurrent, varCurrent, entropyProduction :: BiasedWalk -> Double -> Double
meanCurrent w t = (kPlus w - kMinus w) * t
varCurrent w t = (kPlus w + kMinus w) * t
entropyProduction w t = (kPlus w - kMinus w) * (log (kPlus w) - log (kMinus w)) * t

-- | (a + b)(a - b)(ln a - ln b) - 2 (a - b)^2: non-negative by the logarithmic-mean bound.
logMeanGap :: Double -> Double -> Double
logMeanGap a b = (a + b) * (a - b) * (log a - log b) - 2 * (a - b) * (a - b)

-- | Var(J_t) sigma_t - 2 <J_t>^2: non-negative by the TUR.
turGap :: BiasedWalk -> Double -> Double
turGap w t = varCurrent w t * entropyProduction w t - 2 * meanCurrent w t * meanCurrent w t
