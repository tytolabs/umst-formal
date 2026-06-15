-- |
-- Module      : PrimeSpectralGuidance
-- Description : Haskell parity of Lean/PrimeSpectralGuidance.lean (engineering checks)
--
-- Mirrors:
--   * spectralFilter_id
--   * spectralFilter_perturb / bounded deviation
--   * mangoldtWeightedSum linearity (additivity)
module PrimeSpectralGuidance
  ( MultiplicativeChannel(..)
  , spectralFilter
  , spectralFilter_id_check
  , spectralFilter_perturb_check
  , weightDeviationL1
  , mangoldtWeightedSum
  , mangoldtWeightedSum_add_check
  , vonMangoldtWeight
  ) where

import Data.List (foldl')

-- | Auxiliary channel: vector of values indexed 0..n-1.
newtype MultiplicativeChannel = MC { channelValues :: [Double] }
  deriving (Show, Eq)

-- | Rational surrogate: minFac when n is prime power, else 0 (engineering mirror).
vonMangoldtWeight :: Int -> Double
vonMangoldtWeight n
  | n <= 1    = 0
  | prime n   = fromIntegral n
  | isPrimePower n = fromIntegral (minFac n)
  | otherwise = 0
  where
    prime x = x >= 2 && all ((/= 0) . rem x) [2 .. floor (sqrt (fromIntegral x))]
    isPrimePower x =
      let p = minFac x
      in p > 1 && p ^ (maxPower p x) == x
    maxPower p x = go 0 x
      where
        go k y
          | y `mod` p /= 0 = k
          | otherwise      = go (k + 1) (y `div` p)
    minFac x =
      head [p | p <- [2 .. x], x `mod` p == 0]

-- | Elementwise spectral filter.
spectralFilter :: [Double] -> MultiplicativeChannel -> MultiplicativeChannel
spectralFilter weights (MC vals) =
  MC (zipWith (*) weights vals)

-- | L1 deviation from identity weights.
weightDeviationL1 :: [Double] -> Double
weightDeviationL1 ws = foldl' (\acc w -> acc + abs (w - 1)) 0 ws

-- | Identity filter leaves channel unchanged.
spectralFilter_id_check :: MultiplicativeChannel -> Bool
spectralFilter_id_check mc =
  let n = length (channelValues mc)
      ones = replicate n 1.0
      filtered = spectralFilter ones mc
      eps = 1e-12
  in all (\(a, b) -> abs (a - b) < eps) (zip (channelValues mc) (channelValues filtered))

-- | Perturbation identity: (w - 1) * s at each index.
spectralFilter_perturb_check :: [Double] -> MultiplicativeChannel -> Bool
spectralFilter_perturb_check ws (MC vals) =
  let filtered = channelValues (spectralFilter ws (MC vals))
      eps = 1e-12
  in all (\((f, v), w) -> abs (f - v - (w - 1) * v) < eps) (zip (zip filtered vals) ws)

-- | Finite von Mangoldt-weighted sum.
mangoldtWeightedSum :: [Double] -> Double
mangoldtWeightedSum fs =
  sum [vonMangoldtWeight (i + 1) * f | (i, f) <- zip [0 ..] fs]

-- | Additivity check for mangoldtWeightedSum.
mangoldtWeightedSum_add_check :: [Double] -> [Double] -> Bool
mangoldtWeightedSum_add_check f g =
  let n = max (length f) (length g)
      pad xs = xs ++ replicate (n - length xs) 0
      f' = pad f
      g' = pad g
      sumFG = zipWith (+) f' g'
      eps = 1e-9
  in abs (mangoldtWeightedSum sumFG - (mangoldtWeightedSum f' + mangoldtWeightedSum g')) < eps
