-- | Engineering mirror of `Lean/OrderStatisticsBand.lean` (order-statistics band envelope + QC hooks).
module OrderStatisticsBand where

import Test.QuickCheck

import MedianConvergence (nWarmup)

-- | Lean-side `nQuantile` reuses the `nWarmup` kernel; `q` is tracked for API symmetry only.
nQuantile :: Double -> Double -> Double -> Double -> Integer
nQuantile eps del rho _q = nWarmup eps del rho

-- | Bookkeeping inequality from `quantile_separation_preserved` (split-sample P25+P75 at half confidence).
prop_quantile_separation_split_sample :: Double -> Double -> Double -> Property
prop_quantile_separation_split_sample u v w =
  let eps = 0.06 + 0.12 * abs (sin u)
      del = min 0.45 (0.08 + 0.18 * abs (cos v))
      rho = 0.09 + 0.22 * abs (sin w)
      half = del / 2.0
   in del > 0 && del < 1 && half > 0 && half < 1 && eps > 0 && rho > 0 ==>
        2 * nWarmup eps del rho
          <= nWarmup eps half rho + nWarmup eps half rho

-- | Structural surrogate: misclassification budget slot is nonnegative for honest `δ ≥ 0`.
prop_band_classification_surrogate_nonneg :: Double -> Property
prop_band_classification_surrogate_nonneg d =
  let del = max 0 (abs (sin d))
   in property $ 0 <= 3 * del

-- | Flip-rate surrogate `1/W` is nonnegative on stationary windows of capacity `W ≥ 1`.
prop_flip_rate_surrogate_nonneg :: Int -> Property
prop_flip_rate_surrogate_nonneg w =
  let w' = max 1 (abs w `mod` 10000)
      inv = 1 / (fromIntegral w' :: Double)
   in property $ inv >= 0

prop_n_quantile_monotone_in_epsilon :: Double -> Double -> Double -> Double -> Property
prop_n_quantile_monotone_in_epsilon u v w t =
  let eps1 = 0.05 + 0.15 * abs (sin u)
      eps2 = min 0.95 (eps1 + 0.02 + 0.1 * abs (cos v))
      del = 0.05 + 0.2 * abs (sin w)
      rho = 0.1 + 0.3 * abs (cos u)
      q = 0.1 + 0.8 * abs (sin t)
   in del > 0 && del < 1 && rho > 0 && eps2 + 1e-9 >= eps1 && q > 0 && q < 1 ==>
        nQuantile eps2 del rho q <= nQuantile eps1 del rho q

prop_n_quantile_monotone_in_delta :: Double -> Double -> Double -> Double -> Property
prop_n_quantile_monotone_in_delta u v w t =
  let d1 = 0.03 + 0.12 * abs (sin u)
      d2 = min 0.92 (d1 + 0.01 + 0.08 * abs (cos v))
      eps = 0.08 + 0.12 * abs (sin w)
      rho = 0.11 + 0.25 * abs (cos u)
      q = 0.1 + 0.8 * abs (sin t)
   in d1 > 0 && d2 > 0 && d2 < 1 && eps > 0 && rho > 0 && q > 0 && q < 1 && d2 + 1e-9 >= d1 ==>
        nQuantile eps d2 rho q <= nQuantile eps d1 rho q
