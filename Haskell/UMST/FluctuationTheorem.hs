-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- The Jarzynski integral fluctuation theorem on a finite state space, twin of Lean/FluctuationTheorem.lean,
-- Coq/FluctuationTheorem.v and Agda/FluctuationTheorem.agda.
--
-- A protocol on the states [0 .. n-1] carries, for each stage k, rational Boltzmann weights @weight k x@, the
-- exponentiated work of the switch into stage k+1 (@tilt k x@ = weight (k+1) x / weight k x) and a relaxation kernel
-- @kernel k x y@ that leaves weight (k+1) invariant. Everything is exact ('Rational'), so the Jarzynski identity
-- <exp(-beta W)> = Z K / Z 0 is checked with equality, both in the transfer form ('tiltedForward') and as an explicit
-- sum over every trajectory ('pathAverage'). The Jensen bridge and the SecondLaw consequence run on 'Double' with
-- the real exponential.
module UMST.FluctuationTheorem
  ( Protocol (..)
  , tilt
  , partition
  , tiltedForward
  , kernelBalanced
  , metropolisKernel
  , pathAverage
  , ensembleMean
  , ensembleIFT
  , jarzynskiFreeEnergy
  , asFeedback
  ) where

import UMST.Process (FeedbackProcess (..), HeatBath (..))

-- | A finite driven protocol: number of states, weights per stage, kernels per stage.
data Protocol = Protocol
  { states :: Int
  , weight :: Int -> Int -> Rational
  , kernel :: Int -> Int -> Int -> Rational
  }

-- | Exponentiated work of the switch into stage k+1 at state x.
tilt :: Protocol -> Int -> Int -> Rational
tilt p k x = weight p (k + 1) x / weight p k x

-- | Partition function of stage k.
partition :: Protocol -> Int -> Rational
partition p k = sum [weight p k x | x <- [0 .. states p - 1]]

-- | Unnormalised work-tilted forward vector: u 0 = weight 0, u (k+1) y = sum_x u k x * tilt k x * kernel k x y.
tiltedForward :: Protocol -> Int -> Int -> Rational
tiltedForward p 0 y = weight p 0 y
tiltedForward p k y =
  sum [tiltedForward p (k - 1) x * tilt p (k - 1) x * kernel p (k - 1) x y | x <- [0 .. states p - 1]]

-- | Each kernel up to stage K is row-stochastic, non-negative and leaves the weight of its stage invariant.
kernelBalanced :: Protocol -> Int -> Bool
kernelBalanced p kmax = and
  [ all (>= 0) [kernel p k x y | x <- xs, y <- xs]
      && all (\x -> sum [kernel p k x y | y <- xs] == 1) xs
      && all (\y -> sum [weight p (k + 1) x * kernel p k x y | x <- xs] == weight p (k + 1) y) xs
  | k <- [0 .. kmax - 1] ]
  where xs = [0 .. states p - 1]

-- | Metropolis kernel for weights w on n states: detailed balance with w, hence w-invariant.
metropolisKernel :: Int -> (Int -> Rational) -> Int -> Int -> Rational
metropolisKernel n w x y
  | x /= y = (1 / fromIntegral n) * min 1 (w y / w x)
  | otherwise = 1 - sum [metropolisKernel n w x z | z <- [0 .. n - 1], z /= x]

-- | <exp(-beta W)> over K stages as an explicit sum over every trajectory (x_0, ..., x_K).
pathAverage :: Protocol -> Int -> Rational
pathAverage p kmax = sum [go 0 x0 (weight p 0 x0 / partition p 0) | x0 <- xs]
  where
    xs = [0 .. states p - 1]
    go k x acc
      | k == kmax = acc
      | otherwise = sum [go (k + 1) y (acc * tilt p k x * kernel p k x y) | y <- xs]

-- | Mean of W over a finite ensemble of (probability, work) pairs.
ensembleMean :: [(Double, Double)] -> Double
ensembleMean ens = sum [pr * w | (pr, w) <- ens]

-- | <exp(-beta (W - dF))> over a finite ensemble.
ensembleIFT :: Double -> Double -> [(Double, Double)] -> Double
ensembleIFT beta dF ens = sum [pr * exp (negate beta * (w - dF)) | (pr, w) <- ens]

-- | The free-energy change the ensemble's integral fluctuation theorem fixes: dF = -(1/beta) ln <exp(-beta W)>.
jarzynskiFreeEnergy :: Double -> [(Double, Double)] -> Double
jarzynskiFreeEnergy beta ens = negate (log (sum [pr * exp (negate beta * w) | (pr, w) <- ens])) / beta

-- | The ensemble read as a feedback process extracting -<W> at a bath.
asFeedback :: HeatBath -> Double -> [(Double, Double)] -> FeedbackProcess
asFeedback b dF ens = FeedbackProcess b (negate (ensembleMean ens)) dF
