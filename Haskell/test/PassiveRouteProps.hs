-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- | Property tests of the passive route (twins of Lean/Convex/PassiveRoute.lean and the passive cartridge law of
-- Lean/ConvexPhiDissipation.lean, with their Coq and Agda twins).
--
-- Each property builds a passive step from a state and its dissipation (the free energy falls by the dissipation
-- and nothing else changes) and runs the runtime second law ('P.secondLaw' on the transition case, through
-- 'UMST.PassiveRoute'). Free energies and dissipations are rationals with numerator in [0, 1000] and denominator in
-- [1, 100], so a nonzero dissipation has magnitude at least 0.01, far outside the gate's 1e-6 tolerance.
module PassiveRouteProps
  ( prop_passive_secondLaw_iff
  , prop_passive_dissipation_nonneg_of_secondLaw
  , prop_passive_inequality_secondLaw
  , prop_passive_refused_of_neg
  , prop_passive_relaxation_stored_nonneg
  , prop_convex_phi_dissipation_nonneg
  , prop_gsm_cartridge_passive_secondLaw
  , passiveRouteProps
  ) where

import Test.QuickCheck

import UMST.Concrete (ThermodynamicState (..))
import UMST.GsmMonoid (GsmPotential (..), power, quadAbsPotential)
import UMST.PassiveRoute

-- | A non-negative rational with numerator in [0, 1000] and denominator in [1, 100].
genNonNeg :: Gen Rational
genNonNeg = (\n d -> fromIntegral n / fromIntegral d) <$> choose (0 :: Integer, 1000) <*> choose (1 :: Integer, 100)

-- | A positive rational of magnitude at least 1/100.
genPos :: Gen Rational
genPos = (\n d -> fromIntegral n / fromIntegral d) <$> choose (1 :: Integer, 1000) <*> choose (1 :: Integer, 100)

-- | A rational of either sign.
genQ :: Gen Rational
genQ = (*) <$> elements [1, -1] <*> genNonNeg

-- | A state of free energy @f@.
st :: Rational -> ThermodynamicState
st f = ThermodynamicState {density = 2400, freeEnergy = fromRational f, hydration = 0.5, strength = 30, maxStrength = 100}

-- | The passive route: on a passive step the second law holds exactly when the dissipation is non-negative (twin of
-- passive_secondLaw_iff).
prop_passive_secondLaw_iff :: Property
prop_passive_secondLaw_iff = forAll genQ $ \psi -> forAll genQ $ \d ->
  passiveSecondLaw (st psi) (fromRational d) === (d >= 0)

-- | A step the second law admits names a non-negative dissipation through its balance, the released free energy
-- (twin of dissipation_nonneg_of_secondLaw).
prop_passive_dissipation_nonneg_of_secondLaw :: Property
prop_passive_dissipation_nonneg_of_secondLaw = forAll genQ $ \psi0 -> forAll genQ $ \psi1 ->
  let old = st psi0
      new = st psi1
   in stepSecondLaw old new === (releasedFreeEnergy old new >= 0)

-- | Inequality form: a step with Δψ + d ≤ 0 and d ≥ 0 passes the second law (twin of passive_inequality_secondLaw).
prop_passive_inequality_secondLaw :: Property
prop_passive_inequality_secondLaw = forAll genQ $ \psi -> forAll genNonNeg $ \d -> forAll genNonNeg $ \slack ->
  property (stepSecondLaw (st psi) (st (psi - d - slack)))

-- | A passive step with negative dissipation is refused (twin of passive_refused_of_neg).
prop_passive_refused_of_neg :: Property
prop_passive_refused_of_neg = forAll genQ $ \psi -> forAll genPos $ \d ->
  property (not (passiveSecondLaw (st psi) (fromRational (negate d))))

-- | A relaxation to the natural state dissipates the stored energy and is admitted exactly when it is non-negative
-- (twin of relaxation_stored_nonneg).
prop_passive_relaxation_stored_nonneg :: Property
prop_passive_relaxation_stored_nonneg = forAll genQ $ \psi -> relaxationSecondLaw (st psi) === (psi >= 0)

-- | A convex potential φ(x) = a·x² + b·|x| (a, b ≥ 0) satisfies φ(x) ≤ x·φ′(x) and dissipates non-negatively (twins
-- of convex_phi_le_dissipationPower and convex_phi_dissipation_nonneg).
prop_convex_phi_dissipation_nonneg :: Property
prop_convex_phi_dissipation_nonneg = forAll genNonNeg $ \a -> forAll genNonNeg $ \b -> forAll genQ $ \x ->
  let p = quadAbsPotential a b in phi p x <= power p x .&&. power p x >= 0

-- | The passive cartridge law: the passive step dissipating a convex potential's power passes the second law (twin
-- of gsmCartridge_passive_secondLaw).
prop_gsm_cartridge_passive_secondLaw :: Property
prop_gsm_cartridge_passive_secondLaw = forAll genNonNeg $ \a -> forAll genNonNeg $ \b -> forAll genQ $ \x ->
  forAll genQ $ \psi -> property (gsmCartridgePassiveSecondLaw (quadAbsPotential a b) x (st psi))

-- | The properties with their names, for the runner.
passiveRouteProps :: [(String, Property)]
passiveRouteProps =
  [ ("passive_secondLaw_iff", prop_passive_secondLaw_iff)
  , ("passive_dissipation_nonneg_of_secondLaw", prop_passive_dissipation_nonneg_of_secondLaw)
  , ("passive_inequality_secondLaw", prop_passive_inequality_secondLaw)
  , ("passive_refused_of_neg", prop_passive_refused_of_neg)
  , ("passive_relaxation_stored_nonneg", prop_passive_relaxation_stored_nonneg)
  , ("convex_phi_dissipation_nonneg", prop_convex_phi_dissipation_nonneg)
  , ("gsm_cartridge_passive_secondLaw", prop_gsm_cartridge_passive_secondLaw)
  ]
