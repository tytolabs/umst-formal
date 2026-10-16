-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Laws L-A, L-D and L-I on exact rationals; twin of Lean/AdaptiveSeamLensLaws.lean, Coq/AdaptiveSeamLensLaws.v and
-- Agda/AdaptiveSeamLensLaws.agda. The transfer lens restricts a fine state of 2n values to n coarse values by pairwise
-- means and prolongs by duplication (R P = id); a GENERIC pair is built from rank-two antisymmetric L and rank-one
-- positive semidefinite M. test/AdaptiveSeamLensLawsProps.hs decides the statements on random states and steps.
module AdaptiveSeamLensLaws
  ( restrict
  , prolong
  , lensPut
  , dot
  , mulVec
  , antisymOf
  , psdOf
  , orthTo
  , SeamStep (..)
  , oneIneq
  ) where

-- | The restriction: pairwise means.
restrict :: [Rational] -> [Rational]
restrict (a : b : rest) = (a + b) / 2 : restrict rest
restrict _ = []

-- | The prolongation: each coarse value duplicated.
prolong :: [Rational] -> [Rational]
prolong = concatMap (\v -> [v, v])

-- | put s v = (s - P (R s)) + P v.
lensPut :: [Rational] -> [Rational] -> [Rational]
lensPut s v = zipWith (+) (zipWith (-) s (prolong (restrict s))) (prolong v)

dot :: [Rational] -> [Rational] -> Rational
dot xs ys = sum (zipWith (*) xs ys)

mulVec :: [[Rational]] -> [Rational] -> [Rational]
mulVec m x = map (`dot` x) m

-- | u v^T - v u^T, antisymmetric.
antisymOf :: [Rational] -> [Rational] -> [[Rational]]
antisymOf u v = [[ui * vj - vi * uj | (vj, uj) <- zip v u] | (ui, vi) <- zip u v]

-- | w w^T, symmetric positive semidefinite.
psdOf :: [Rational] -> [[Rational]]
psdOf w = [[wi * wj | wj <- w] | wi <- w]

-- | The component of u orthogonal to g (exact Gram-Schmidt step).
orthTo :: [Rational] -> [Rational] -> [Rational]
orthTo g u = let gg = dot g g in if gg == 0 then u else zipWith (\ui gi -> ui - dot u g / gg * gi) u g

-- | One subsystem step: free-energy change, supplied work, information.
data SeamStep = SeamStep { sdF :: Rational, sW :: Rational, sI :: Rational }
  deriving (Show)

-- | The one inequality with c = k_B T.
oneIneq :: Rational -> SeamStep -> Bool
oneIneq c s = sdF s <= sW s + c * sI s
