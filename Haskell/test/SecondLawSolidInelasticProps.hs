-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of the inelastic-solid parameters the second law bounds (twins of
-- Lean/Constants/SecondLawSolidInelastic.lean with its Coq and Agda twins).
--
-- Each property runs the runtime second law ('P.secondLaw' on the transition case) on a passive step, the relaxation
-- of a loaded state to its natural state or a step that dissipates energy out of the free energy, and checks that
-- the law admits the step exactly when the bound holds. Parameters are drawn with a magnitude in [0.01, 1000] and a
-- random sign, or a distance in [0.01, 0.99] from an interval endpoint, so the energies sit far outside the gate's
-- 1e-6 tolerance.
module SecondLawSolidInelasticProps
  ( prop_bound_coupled_well
  , prop_bound_double_well
  , prop_bound_griffith_energy
  , prop_bound_griffith_toughness
  , prop_bound_norton
  , prop_bound_parabolic_rate
  , prop_bound_frictional_bond
  ) where

import Test.QuickCheck

import UMST.Concrete (ThermodynamicState (..))
import qualified UMST.Process as P

-- | A thermodynamic state of free energy @f@.
st :: Double -> ThermodynamicState
st f = ThermodynamicState {density = 2400, freeEnergy = f, hydration = 0.5, strength = 30, maxStrength = 100}

-- | The second law on the passive relaxation from free energy @psi@ to the natural state.
relaxes :: Double -> Bool
relaxes psi = P.secondLaw P.Transition (P.Thermodynamic (st psi) (st 0))

-- | The second law on a passive step from free energy @psi@ that dissipates @d@.
dissipates :: Double -> Double -> Bool
dissipates psi d = P.secondLaw P.Transition (P.Thermodynamic (st psi) (st (psi - d)))

-- | A parameter of magnitude in [0.01, 1000] with either sign.
genSigned :: Gen Double
genSigned = (*) <$> elements [1, -1] <*> choose (0.01, 1000)

-- | A positive measure (a rate, an area, a time step, a stress) in [0.1, 10].
genPositive :: Gen Double
genPositive = choose (0.1, 10)

-- | A cross coupling at a distance in [0.01, 0.99] from −1 or from 1, on either side.
genCross :: Gen Double
genCross = (\e s d -> e + s * d) <$> elements [1, -1] <*> elements [1, -1] <*> choose (0.01, 0.99)

-- | Coupled well: ½·k·(x² + y² + 2c·x·y) with k > 0 relaxes from (1, 1), (1, −1) and random states exactly when
-- −1 ≤ c ≤ 1 (twin of coupledWell_bounds).
prop_bound_coupled_well :: Property
prop_bound_coupled_well = forAll (choose (0.01, 1000)) $ \k -> forAll genCross $ \c ->
  forAll (vectorOf 4 ((,) <$> choose (-3, 3) <*> choose (-3, 3))) $ \mixed ->
    let energy x y = 0.5 * k * (x * x + y * y + 2 * c * x * y)
     in all (relaxes . uncurry energy) ([(1, 0), (1, 1), (1, -1)] ++ mixed) === (c >= -1 && c <= 1)

-- | Double well: k·φ²·(1 − φ)² at φ in (0.1, 0.9) relaxes exactly when k ≥ 0 (twin of doubleWell_modulus_nonneg).
prop_bound_double_well :: Property
prop_bound_double_well = forAll genSigned $ \k -> forAll (choose (0.1, 0.9)) $ \phi ->
  relaxes (k * (phi * phi * (1 - phi) * (1 - phi))) === (k >= 0)

-- | Griffith fracture energy: a crack extension ΔA > 0 dissipating G_c·ΔA is admitted exactly when G_c ≥ 0 (twin of
-- griffith_fracture_energy_nonneg).
prop_bound_griffith_energy :: Property
prop_bound_griffith_energy = forAll genSigned $ \gc -> forAll genPositive $ \dA ->
  forAll (choose (-100, 100)) $ \psi -> dissipates psi (gc * dA) === (gc >= 0)

-- | Fracture toughness: when the crack extension and the elastic relaxation are both admitted, E·G_c ≥ 0 and the
-- toughness √(E·G_c) squares back to E·G_c (twin of griffith_toughness_nonneg).
prop_bound_griffith_toughness :: Property
prop_bound_griffith_toughness = forAll genSigned $ \gc -> forAll genSigned $ \e -> forAll genPositive $ \dA ->
  forAll genPositive $ \sigma ->
    let ok = dissipates 0 (gc * dA) && relaxes (sigma * sigma / (2 * e))
        k = sqrt (e * gc)
     in (ok === (gc >= 0 && e > 0)) .&&. (not ok || (k >= 0 && abs (k * k - e * gc) <= 1e-9 * (1 + e * gc)))

-- | Norton creep: σ·(A·σⁿ)·dt at σ in [1, 2], any n in [1, 8], is admitted exactly when A ≥ 0 (twin of
-- norton_coefficient_nonneg).
prop_bound_norton :: Property
prop_bound_norton = forAll genSigned $ \a -> forAll (choose (1, 2)) $ \sigma -> forAll (choose (1, 8)) $ \n ->
  forAll genPositive $ \dt -> dissipates 0 (sigma * (a * sigma ** n) * dt) === (a >= 0)

-- | Parabolic scaling: a·(k_p/(2x))·dt with affinity a > 0 and thickness x > 0 is admitted exactly when k_p ≥ 0
-- (twin of parabolic_rate_nonneg).
prop_bound_parabolic_rate :: Property
prop_bound_parabolic_rate = forAll genSigned $ \kp -> forAll genPositive $ \a -> forAll (choose (0.1, 1)) $ \x ->
  forAll genPositive $ \dt -> dissipates 0 (a * (kp / (2 * x)) * dt) === (kp >= 0)

-- | Frictional bond: b·√f_c·s with f_c > 0 and slip area s > 0 is admitted exactly when b ≥ 0 (twin of
-- frictional_bond_nonneg).
prop_bound_frictional_bond :: Property
prop_bound_frictional_bond = forAll genSigned $ \b -> forAll (choose (10, 100)) $ \fc -> forAll genPositive $ \s ->
  dissipates 0 (b * sqrt fc * s) === (b >= 0)
