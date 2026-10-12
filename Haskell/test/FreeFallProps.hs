-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of the free fall as a passive transition of the second law (twins of Lean/FreeFall.lean,
-- Coq/FreeFall.v and Agda/FreeFall.agda).
--
-- Gravity is the gradient of a scalar potential on the configuration manifold; the free energy of a body of mass m
-- at height z is the linear, hence convex, potential m·g·z. Each property runs the runtime second law
-- ('P.secondLaw' on the transition case) on a fall from rest, an impact and a rebound, and checks the lemma's
-- consequences. Energies sit at least one percent from each bound and far above the gate's 1e-6 tolerance.
-- Typed absence: the k_B·T·ln 2 cost per extracted frame bit is the measureFeedback case, follow-up cell
-- FORMAL-FREEFALL-MEASURE-FEEDBACK.
module FreeFallProps
  ( prop_free_fall_gravity_bound
  , prop_free_fall_rebound_chain
  , prop_free_fall_restitution_heights
  ) where

import Test.QuickCheck

import UMST.Concrete (ThermodynamicState (..))
import qualified UMST.OneInequality as O
import qualified UMST.Process as P

st :: Double -> ThermodynamicState
st f = ThermodynamicState {density = 2400, freeEnergy = f, hydration = 0.5, strength = 30, maxStrength = 100}

-- | The second law on the passive step from free energy @a@ to free energy @b@.
admits :: Double -> Double -> Bool
admits a b = P.secondLaw P.Transition (P.Thermodynamic (st a) (st b))

genMass, genField, genHeight :: Gen Double
genMass = choose (1, 10)
genField = choose (5, 20)
genHeight = choose (0.5, 10)

-- | Squared speed as the ratio 1 ± d of the frictionless value 2·g·h, d in [0.01, 0.5].
genRatio :: Gen Double
genRatio = (\s d -> 1 + s * d) <$> elements [1, -1] <*> choose (0.01, 0.5)

-- | A fall from rest through h is admitted exactly when v² ≤ 2·g·h, and then D ≥ 0, ½·m·v² ≤ W_in and g ≥ v²/(2·h)
-- (twin of freeFall_gravity_lower_bound).
prop_free_fall_gravity_bound :: Property
prop_free_fall_gravity_bound = forAll genMass $ \m -> forAll genField $ \g -> forAll genHeight $ \h ->
  forAll genRatio $ \r ->
    let w = m * g * h
        v2 = r * 2 * g * h
        ke = 0.5 * m * v2
        ok = admits w ke
     in (ok === (r <= 1)) .&&. property (not ok || (w - ke >= 0 && ke <= w && v2 <= 2 * g * h && v2 / (2 * h) <= g))

-- | Fall, impact and rebound admitted step by step compose as one chain of the one inequality, and the rebound
-- height stays within the drop (twin of freeFallRebound_chain_oneInequality and freeFallRebound_height_le).
prop_free_fall_rebound_chain :: Property
prop_free_fall_rebound_chain = forAll genMass $ \m -> forAll genField $ \g -> forAll genHeight $ \hd ->
  forAll (choose (0.5, 0.99)) $ \rf -> forAll (choose (0.1, 0.9)) $ \e -> forAll (choose (0.5, 0.99)) $ \rr ->
    let f0 = m * g * hd
        f1 = rf * f0
        f2 = e * e * f1
        f3 = rr * f2
        hr = f3 / (m * g)
        b = P.HeatBath 300
        chained = O.chain (O.chain (O.transitionStepAt b (st f0) (st f1)) (O.transitionStepAt b (st f1) (st f2)))
                          (O.transitionStepAt b (st f2) (st f3))
     in admits f0 f1 && admits f1 f2 && admits f2 f3 ==> (O.oneInequality chained && hr <= hd)

-- | With no dissipation in flight, e² = h_r / h_d and g cancels: the ratio is the same in every field (twin of
-- freeFallRebound_restitution).
prop_free_fall_restitution_heights :: Property
prop_free_fall_restitution_heights = forAll genHeight $ \hd -> forAll (choose (0, 1)) $ \e ->
  forAll genField $ \g1 -> forAll genField $ \g2 ->
    let hrIn g = (0.5 * (2 * g * hd) * e * e) / g
        ratio g = hrIn g / hd
        close x y = abs (x - y) <= 1e-9
     in close (ratio g1) (e * e) .&&. close (ratio g2) (e * e) .&&. property (ratio g1 <= 1)
