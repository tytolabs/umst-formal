-- | Engineering mirror of `Lean/RhoEstimator.lean` (Gaussian MI from Pearson ρ, bits).
module RhoEstimator where

import Test.QuickCheck

rhoClamp :: Double -> Double
rhoClamp r = max (-0.9999) (min 0.9999 r)

-- | \( \mathrm{MI}(\rho) = -\tfrac12 \log_2(1-\rho^2) \) on the clamped interior.
rhoMiBits :: Double -> Double
rhoMiBits rho =
  let r = rhoClamp rho
      z = 1 - r * r
   in if z <= 0 then 0 else -0.5 * logBase 2 z

prop_rho_mi_formula_matches_log2 :: Double -> Property
prop_rho_mi_formula_matches_log2 x =
  let rho = 0.98 * sin x
      r = rhoClamp rho
      z = 1 - r * r
      ref = -0.5 * log z / log 2
   in z > 0 ==> abs (rhoMiBits rho - ref) <= 1e-12

prop_rho_mi_nonneg_interior :: Double -> Property
prop_rho_mi_nonneg_interior x =
  let rho = 0.999 * sin x
   in property $ rhoMiBits rho >= -1e-15

prop_rho_mi_monotone_abs_rho :: Double -> Double -> Property
prop_rho_mi_monotone_abs_rho u v =
  let r1 = 0.1 + 0.4 * abs (sin u)
      r2 = min 0.999 (r1 + 0.05 + 0.1 * abs (cos v))
   in r2 + 1e-12 >= r1 ==> rhoMiBits r1 <= rhoMiBits r2 + 1e-9

prop_rho_mi_zero_at_zero :: Property
prop_rho_mi_zero_at_zero = property $ abs (rhoMiBits 0) < 1e-12

prop_rho_mi_bounded_by_rho_max :: Double -> Double -> Property
prop_rho_mi_bounded_by_rho_max a b =
  let rmax = 0.15 + 0.8 * abs (sin a)
      r = rmax * abs (sin b)
   in property $ rhoMiBits r <= rhoMiBits rmax + 1e-9
