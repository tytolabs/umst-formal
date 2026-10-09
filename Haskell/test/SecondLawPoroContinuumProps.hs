-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of the transport, reaction and poroelastic constants the second law bounds (twins of
-- Lean/Constants/SecondLawPoroContinuum.lean with its Coq and Agda twins).
--
-- Each property runs the runtime second law ('P.secondLaw' on the transition case) on a passive step, a step that
-- dissipates energy out of the free energy or the relaxation of a loaded state to its natural state (free energy
-- zero), and checks that the law admits the step exactly when the bound holds. Constants are drawn with a magnitude
-- in [0.01, 1000] and a random sign, so the energies sit far outside the gate's 1e-6 tolerance.
module SecondLawPoroContinuumProps
  ( prop_bound_reaction_rate
  , prop_bound_reaction_rate_constant
  , prop_bound_fick_diffusivity
  , prop_bound_darcy_permeability
  , prop_bound_biot_coefficient
  , prop_bound_biot_storage
  , prop_bound_isotropic_moduli_pos
  ) where

import Test.QuickCheck

import UMST.Concrete (ThermodynamicState (..))
import qualified UMST.Process as P

-- | A state of free energy @f@ (the other fields are fixed and do not enter the transition case).
st :: Double -> ThermodynamicState
st f = ThermodynamicState {density = 2400, freeEnergy = f, hydration = 0.5, strength = 30, maxStrength = 100}

-- | The second law on the passive relaxation from free energy @psi@ to the natural state.
relaxes :: Double -> Bool
relaxes psi = P.secondLaw P.Transition (P.Thermodynamic (st psi) (st 0))

-- | The second law on a passive step from free energy @psi@ that dissipates @d@.
dissipates :: Double -> Double -> Bool
dissipates psi d = P.secondLaw P.Transition (P.Thermodynamic (st psi) (st (psi - d)))

-- | A constant of magnitude in [0.01, 1000] with either sign.
genConstant :: Gen Double
genConstant = (*) <$> elements [1, -1] <*> choose (0.01, 1000)

-- | A positive factor in [0.5, 10].
genPositive :: Gen Double
genPositive = choose (0.5, 10)

-- | A nonzero gradient or strain of magnitude in [0.5, 10] with either sign.
genLoad :: Gen Double
genLoad = (*) <$> elements [1, -1] <*> choose (0.5, 10)

-- | Reaction rate: affinity A > 0, rate r, dt > 0 dissipates A·r·dt; admitted exactly when r ≥ 0 (twin of
-- reaction_rate_nonneg).
prop_bound_reaction_rate :: Property
prop_bound_reaction_rate = forAll genPositive $ \a -> forAll genConstant $ \r -> forAll genPositive $ \dt ->
  dissipates 0 (a * r * dt) === (r >= 0)

-- | Rate constant: rate law r = k·g with g > 0; admitted exactly when k ≥ 0 (twin of reaction_rate_constant_nonneg).
prop_bound_reaction_rate_constant :: Property
prop_bound_reaction_rate_constant = forAll genPositive $ \a -> forAll genConstant $ \k -> forAll genPositive $ \g ->
  forAll genPositive $ \dt -> dissipates 0 (a * (k * g) * dt) === (k >= 0)

-- | Diffusivity: D·χ·g²·dt with χ > 0, g ≠ 0; admitted exactly when D ≥ 0 (twin of fick_diffusivity_nonneg).
prop_bound_fick_diffusivity :: Property
prop_bound_fick_diffusivity = forAll genConstant $ \d -> forAll genPositive $ \chi -> forAll genLoad $ \g ->
  forAll genPositive $ \dt -> dissipates 0 (d * chi * g * g * dt) === (d >= 0)

-- | Permeability: (κ/μ)·g²·dt with μ > 0, g ≠ 0; admitted exactly when κ ≥ 0 (twin of darcy_permeability_nonneg).
prop_bound_darcy_permeability :: Property
prop_bound_darcy_permeability = forAll genConstant $ \kappa -> forAll genPositive $ \mu -> forAll genLoad $ \g ->
  forAll genPositive $ \dt -> dissipates 0 (kappa / mu * g * g * dt) === (kappa >= 0)

-- | Biot coefficient: with K = K_s·(1 − b) and n = (b − φ)/K_s, the drained and pore modes relax exactly when
-- φ ≤ b ≤ 1 (twin of biot_coefficient_bounds). b is drawn on both sides of [φ, 1].
prop_bound_biot_coefficient :: Property
prop_bound_biot_coefficient = forAll (choose (0.01, 0.6)) $ \phi -> forAll (choose (-1, 2)) $ \b ->
  forAll (choose (1, 100)) $ \ks -> forAll genLoad $ \s ->
    let k = ks * (1 - b)
        n = (b - phi) / ks
        ok = relaxes (0.5 * k * s * s) && relaxes (0.5 * n * s * s)
        margin = 4e-6 / (s * s) -- twice the gate's 1e-6 tolerance on ½·x·s², read back on x
     in abs k > margin && abs n > margin ==> ok === (phi <= b && b <= 1)

-- | Biot storage: with φ > 0 the pore and fluid modes relax exactly when n ≥ 0 and c_f ≥ 0, and then
-- m = n + φ·c_f > 0 for c_f ≠ 0 and M = 1/m > 0 (twin of biot_storage_pos).
prop_bound_biot_storage :: Property
prop_bound_biot_storage = forAll genConstant $ \n -> forAll genConstant $ \cf -> forAll (choose (0.01, 0.6)) $ \phi ->
  forAll genLoad $ \s ->
    let ok = relaxes (0.5 * n * s * s) && relaxes (0.5 * cf * s * s)
        m = n + phi * cf
     in (ok === (n >= 0 && cf >= 0)) .&&. (not ok || (m > 0 && 1 / m > 0))

-- | Isotropic moduli: relaxing from every (e, γ) with K ≠ 0, G ≠ 0 forces K > 0, G > 0 and −1 < ν < 1/2 (twin of
-- isotropic_moduli_pos); the probes are the two unit modes and random mixed states.
prop_bound_isotropic_moduli_pos :: Property
prop_bound_isotropic_moduli_pos = forAll genConstant $ \k -> forAll genConstant $ \g ->
  forAll (vectorOf 4 ((,) <$> genLoad <*> genLoad)) $ \mixed ->
    let energy e gam = 0.5 * k * e * e + 0.5 * g * gam * gam
        ok = all (relaxes . uncurry energy) ([(1, 0), (0, 1)] ++ mixed)
        nu = (3 * k - 2 * g) / (2 * (3 * k + g))
     in (ok === (k > 0 && g > 0)) .&&. (not ok || (nu > -1 && nu < 0.5))
