-- | Engineering mirror of `Lean/MedianConvergence.lean` (median warmup budget).
module MedianConvergence where

import Test.QuickCheck

nWarmupBound :: Double -> Double -> Double -> Double
nWarmupBound eps del rhoMn =
  (2 / (eps * eps * rhoMn * rhoMn)) * log (2 / del)

nWarmup :: Double -> Double -> Double -> Integer
nWarmup eps del rhoMn =
  let b = nWarmupBound eps del rhoMn
      n = ceiling b
   in max 1 n

sqrtWindowThreshold :: Int -> Integer
sqrtWindowThreshold wCap =
  let w = max 1 wCap
      s = ceiling (sqrt (fromIntegral w :: Double) :: Double) :: Integer
   in max 3 s

prop_n_warmup_monotone_in_epsilon :: Double -> Double -> Double -> Property
prop_n_warmup_monotone_in_epsilon u v w =
  let eps1 = 0.05 + 0.15 * abs (sin u)
      eps2 = min 0.95 (eps1 + 0.02 + 0.1 * abs (cos v))
      del = 0.05 + 0.2 * abs (sin w)
      rho = 0.1 + 0.3 * abs (cos u)
   in del > 0 && del < 1 && rho > 0 && eps2 + 1e-9 >= eps1 ==>
        nWarmup eps2 del rho <= nWarmup eps1 del rho

prop_n_warmup_monotone_in_delta :: Double -> Double -> Double -> Property
prop_n_warmup_monotone_in_delta u v w =
  let d1 = 0.03 + 0.12 * abs (sin u)
      d2 = min 0.92 (d1 + 0.01 + 0.08 * abs (cos v))
      eps = 0.08 + 0.12 * abs (sin w)
      rho = 0.11 + 0.25 * abs (cos u)
   in d1 > 0 && d2 > 0 && d2 < 1 && eps > 0 && rho > 0 && d2 + 1e-9 >= d1 ==>
        nWarmup eps d2 rho <= nWarmup eps d1 rho

prop_sqrt_window_matches_engine :: Int -> Property
prop_sqrt_window_matches_engine w =
  let w' = abs w `mod` 5000
      ww = max 1 w'
      ref = max 3 (ceiling (sqrt (fromIntegral ww :: Double) :: Double) :: Integer)
   in property $ sqrtWindowThreshold w' == ref

prop_n_warmup_positive :: Double -> Double -> Double -> Property
prop_n_warmup_positive a b c =
  let eps = 0.06 + 0.1 * abs (sin a)
      del = 0.04 + 0.15 * abs (cos b)
      rho = 0.07 + 0.2 * abs (sin c)
   in del > 0 && del < 1 && eps > 0 && rho > 0 ==>
        nWarmup eps del rho >= 1

-- | Concentration budget scales like @1/ε²@ at fixed @δ, ρ_min@ (rate sanity vs closed form).
prop_bound_inverse_square_epsilon :: Property
prop_bound_inverse_square_epsilon =
  let del = 0.1
      rho = 0.3
      e1 = 0.2
      e2 = 0.4
      b1 = nWarmupBound e1 del rho
      b2 = nWarmupBound e2 del rho
   in property $ b1 >= 4 * b2 - 1e-9
