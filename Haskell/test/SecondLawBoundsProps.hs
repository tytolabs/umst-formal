-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of the material constants the second law bounds (twins of Lean/Constants/SecondLawElastic.lean,
-- Lean/Constants/SecondLawDissipation.lean and ConvexPhiChannels' restitution bound, with their Coq and Agda twins).
--
-- Each property runs the runtime second law ('P.secondLaw' on the transition case) on a passive step, the
-- relaxation of a loaded state to its natural state (free energy zero) or a step that dissipates energy out of the
-- free energy, and checks that the law admits the step exactly when the bound holds: the law accepts every
-- positive modulus or coefficient and refuses every negative one. Moduli are drawn with a
-- magnitude in [0.01, 1000] and a random sign, so the stored energies sit far outside the gate's 1e-6 tolerance.
module SecondLawBoundsProps
  ( prop_bound_stiffness_nonneg
  , prop_bound_modulus_pos
  , prop_bound_two_mode_nonneg
  , prop_bound_isotropic_poisson
  , prop_bound_isotropic_young
  , prop_bound_sls_relaxed
  , prop_bound_orthotropic_poisson
  , prop_bound_dissipation_coefficient
  , prop_bound_viscosity
  , prop_bound_bingham
  , prop_bound_loss_modulus
  , prop_bound_restitution
  , prop_bound_restitution_energy_loss
  ) where

import Test.QuickCheck

import UMST.Concrete (ThermodynamicState (..))
import qualified UMST.Process as P

-- | The second law on the passive relaxation from free energy @psi@ to the natural state.
relaxes :: Double -> Bool
relaxes psi = P.secondLaw P.Transition (P.Thermodynamic (st psi) (st 0))
  where
    st f = ThermodynamicState {density = 2400, freeEnergy = f, hydration = 0.5, strength = 30, maxStrength = 100}

-- | The second law on a passive step from free energy @psi@ that dissipates @d@.
dissipates :: Double -> Double -> Bool
dissipates psi d = P.secondLaw P.Transition (P.Thermodynamic (st psi) (st (psi - d)))
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

-- | Dissipation coefficient: a step dissipating c·q (q > 0) is admitted exactly when c ≥ 0 (twin of
-- dissipation_coefficient_nonneg).
prop_bound_dissipation_coefficient :: Property
prop_bound_dissipation_coefficient = forAll genModulus $ \c -> forAll (choose (0.1, 10)) $ \q ->
  forAll (choose (-100, 100)) $ \psi -> dissipates psi (c * q) === (c >= 0)

-- | Viscosity: a dashpot at rate r ≠ 0 over dt > 0 dissipates η·r²·dt and is admitted exactly when η ≥ 0 (twin of
-- viscosity_nonneg).
prop_bound_viscosity :: Property
prop_bound_viscosity = forAll genModulus $ \eta -> forAll genLoad $ \r -> forAll (choose (0.01, 1)) $ \dt ->
  dissipates 0 (eta * r * r * dt) === (eta >= 0)

-- | Bingham fluid: dissipating (τ₀·|r| + η_p·r²)·dt is admitted at every rate exactly when τ₀ ≥ 0 and η_p ≥ 0 (twin
-- of bingham_nonneg). The probes are the unit rate and the rates the proof uses to undo a negative coefficient:
-- r = −τ₀/(2η_p) for τ₀ < 0 < η_p and r = 2τ₀/(−η_p) for η_p < 0 < τ₀.
prop_bound_bingham :: Property
prop_bound_bingham = forAll genModulus $ \tau0 -> forAll genModulus $ \etaP -> forAll (choose (0.01, 1)) $ \dt ->
  let step r = dissipates 0 ((tau0 * abs r + etaP * r * r) * dt)
      undoRates = [r | r <- [-tau0 / (2 * etaP), 2 * tau0 / negate etaP], r > 0]
   in all step (1 : undoRates) === (tau0 >= 0 && etaP >= 0)

-- | Loss modulus: a cycle of amplitude ε₀ ≠ 0 dissipating π·E″·ε₀² is admitted exactly when E″ ≥ 0, and then the
-- loss factor E″/E′ is nonnegative for E′ > 0 (twin of lossModulus_nonneg).
prop_bound_loss_modulus :: Property
prop_bound_loss_modulus = forAll genModulus $ \e2 -> forAll (choose (0.01, 1000)) $ \e1 -> forAll genLoad $ \eps0 ->
  let ok = dissipates 0 (e2 * (pi * eps0 * eps0))
   in (ok === (e2 >= 0)) .&&. (not ok || e2 / e1 >= 0)

-- | A passive impact with reduced mass μ, speed v and restitution e: free energy ½·μ·v² before, ½·μ·(e·v)² after.
impact :: Double -> Double -> Double -> Bool
impact mu v e = P.secondLaw P.Transition (P.Thermodynamic (st (0.5 * mu * v * v)) (st (0.5 * mu * (e * v) * (e * v))))
  where
    st f = ThermodynamicState {density = 2400, freeEnergy = f, hydration = 0.5, strength = 30, maxStrength = 100}

-- | Restitution 1 ± d with d in [0.01, 0.99]: inside [0, 2] and away from the bound e = 1.
genRestitution :: Gen Double
genRestitution = (\s d -> 1 + s * d) <$> elements [1, -1] <*> choose (0.01, 0.99)

-- | Passive restitution: an impact with e ≥ 0 is admitted exactly when e ≤ 1 (twin of restitution_le_one).
prop_bound_restitution :: Property
prop_bound_restitution = forAll (choose (0.01, 1000)) $ \mu -> forAll genLoad $ \v -> forAll genRestitution $ \e ->
  impact mu v e === (e <= 1)

-- | The kinetic energy lost in an admitted impact, ½·μ·v²·(1 − e²), is nonnegative (twin of
-- restitution_energy_loss_nonneg).
prop_bound_restitution_energy_loss :: Property
prop_bound_restitution_energy_loss = forAll (choose (0.01, 1000)) $ \mu -> forAll genLoad $ \v ->
  forAll genRestitution $ \e -> property (not (impact mu v e) || 0.5 * mu * v * v * (1 - e * e) >= 0)
