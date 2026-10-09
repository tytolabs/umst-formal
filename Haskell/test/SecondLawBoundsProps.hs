-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of the material constants the second law bounds (twins of Lean/Constants/SecondLawElastic.lean,
-- Coq/Constants/SecondLawElastic.v and Agda/Constants/SecondLawElastic.agda).
--
-- Each property runs the runtime second law ('P.secondLaw' on the transition case) on the relaxation of a loaded
-- state to its natural state (free energy zero) and checks that the law admits the relaxation exactly when the
-- bound holds: the law accepts every positive modulus and refuses every negative one. Moduli are drawn with a
-- magnitude in [0.01, 1000] and a random sign, so the stored energies sit far outside the gate's 1e-6 tolerance.
module SecondLawBoundsProps
  ( prop_bound_stiffness_nonneg
  , prop_bound_modulus_pos
  , prop_bound_two_mode_nonneg
  , prop_bound_isotropic_poisson
  , prop_bound_isotropic_young
  , prop_bound_sls_relaxed
  , prop_bound_orthotropic_poisson
  ) where

import Test.QuickCheck

import UMST.Concrete (ThermodynamicState (..))
import qualified UMST.Process as P

-- | The second law on the passive relaxation from free energy @psi@ to the natural state.
relaxes :: Double -> Bool
relaxes psi = P.secondLaw P.Transition (P.Thermodynamic (st psi) (st 0))
  where
    st f = ThermodynamicState {density = 2400, freeEnergy = f, hydration = 0.5, strength = 30, maxStrength = 100}

-- | A modulus of magnitude in [0.01, 1000] with either sign.
genModulus :: Gen Double
genModulus = (*) <$> elements [1, -1] <*> choose (0.01, 1000)

-- | A nonzero strain or stress of magnitude in [0.1, 10] with either sign.
genLoad :: Gen Double
genLoad = (*) <$> elements [1, -1] <*> choose (0.1, 10)

-- | Every loaded state of a two-mode quadratic energy relaxes: the two unit modes and random mixed states.
twoModeRelaxes :: (Double -> Double -> Double) -> [(Double, Double)] -> Bool
twoModeRelaxes energy mixed = all (relaxes . uncurry energy) ([(1, 0), (0, 1)] ++ mixed)

-- | Stiffness: a mode storing ½·k·s² relaxes exactly when k ≥ 0 (twin of relaxation_stiffness_nonneg).
prop_bound_stiffness_nonneg :: Property
prop_bound_stiffness_nonneg = forAll genModulus $ \k -> forAll genLoad $ \s ->
  relaxes (0.5 * k * s * s) === (k >= 0)

-- | Modulus: a body at stress σ stores σ²/(2E) and relaxes exactly when E > 0 (twin of relaxation_modulus_pos).
prop_bound_modulus_pos :: Property
prop_bound_modulus_pos = forAll genModulus $ \e -> forAll genLoad $ \sigma ->
  relaxes (sigma * sigma / (2 * e)) === (e > 0)

-- | Two modes: ½·a·x² + ½·b·y² relaxes from every (x, y) exactly when a ≥ 0 and b ≥ 0 (twin of
-- twoMode_stiffness_nonneg).
prop_bound_two_mode_nonneg :: Property
prop_bound_two_mode_nonneg = forAll genModulus $ \a -> forAll genModulus $ \b ->
  forAll (vectorOf 4 ((,) <$> genLoad <*> genLoad)) $ \mixed ->
    twoModeRelaxes (\x y -> 0.5 * a * x * x + 0.5 * b * y * y) mixed === (a >= 0 && b >= 0)

-- | Poisson ratio: an isotropic solid that relaxes from every volumetric strain and shear, with 3K + G > 0, has
-- −1 ≤ ν ≤ 1/2; it relaxes exactly when K ≥ 0 and G ≥ 0 (twin of isotropic_poisson_bounds).
prop_bound_isotropic_poisson :: Property
prop_bound_isotropic_poisson = forAll genModulus $ \k -> forAll genModulus $ \g ->
  forAll (vectorOf 4 ((,) <$> genLoad <*> genLoad)) $ \mixed ->
    let ok = twoModeRelaxes (\e gam -> 0.5 * k * e * e + 0.5 * g * gam * gam) mixed
        nu = (3 * k - 2 * g) / (2 * (3 * k + g))
     in (ok === (k >= 0 && g >= 0))
          .&&. (not (ok && 3 * k + g > 0) || (nu >= -1 - 1e-12 && nu <= 0.5 + 1e-12))

-- | Young's modulus: under the same relaxation, E = 9KG/(3K + G) ≥ 0 (twin of isotropic_young_nonneg).
prop_bound_isotropic_young :: Property
prop_bound_isotropic_young = forAll genModulus $ \k -> forAll genModulus $ \g ->
  forAll (vectorOf 4 ((,) <$> genLoad <*> genLoad)) $ \mixed ->
    let ok = twoModeRelaxes (\e gam -> 0.5 * k * e * e + 0.5 * g * gam * gam) mixed
     in property (not (ok && 3 * k + g > 0) || 9 * k * g / (3 * k + g) >= 0)

-- | Standard linear solid: relaxing from every total and arm strain gives 0 ≤ G∞ ≤ G∞ + G₁ = G₀ (twin of
-- sls_relaxed_le_instantaneous).
prop_bound_sls_relaxed :: Property
prop_bound_sls_relaxed = forAll genModulus $ \ginf -> forAll genModulus $ \g1 ->
  forAll (vectorOf 4 ((,) <$> genLoad <*> genLoad)) $ \mixed ->
    let ok = twoModeRelaxes (\eps xi -> 0.5 * ginf * eps * eps + 0.5 * g1 * xi * xi) mixed
     in (ok === (ginf >= 0 && g1 >= 0)) .&&. (not ok || (0 <= ginf && ginf <= ginf + g1))

-- | Orthotropic lamina: relaxing from every plane stress state forces E₁ > 0, E₂ > 0 and ν₁₂² ≤ E₁/E₂ (twin of
-- orthotropic_poisson_sq_le); the probes are the two unit stresses, the state (ν₁₂, 1) and random states.
prop_bound_orthotropic_poisson :: Property
prop_bound_orthotropic_poisson = forAll genModulus $ \e1 -> forAll genModulus $ \e2 ->
  forAll (choose (-3, 3)) $ \nu -> forAll (vectorOf 4 ((,) <$> genLoad <*> genLoad)) $ \mixed ->
    let energy s1 s2 = s1 * s1 / (2 * e1) - nu * s1 * s2 / e1 + s2 * s2 / (2 * e2)
        ok = all (relaxes . uncurry energy) ([(1, 0), (0, 1), (nu, 1)] ++ mixed)
     in property (not ok || (e1 > 0 && e2 > 0 && nu * nu / e1 <= 1 / e2 + 1e-9))
