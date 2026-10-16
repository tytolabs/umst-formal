-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "FractureAT2" (FRACTURE-AT2-FORMAL) on random exact rationals: damage in [0, 1], positive c, and
-- non-negative strain energy.
module FractureAT2Props
  ( prop_at2_damage_update
  , prop_at2_energy_nonincreasing
  , prop_at2_balance_eq_total
  , prop_at2_degradation_release_nonneg
  , prop_at2_griffith_iff
  , prop_at2_loading_refused
  , prop_at2_damage_step_secondLaw
  , fractureAT2Props
  ) where

import Test.QuickCheck
import FractureAT2
import UMST.Concrete (ThermodynamicState (..))
import UMST.Process (Process (..), Prior (..), secondLaw)

genUnit :: Gen Rational
genUnit = do
  d <- choose (1, 40)
  n <- choose (0, d)
  pure (fromIntegral n / fromIntegral (d :: Integer))

genPos :: Gen Rational
genPos = do
  d <- choose (1, 20)
  n <- choose (1, 80 :: Integer)
  pure (fromIntegral n / fromIntegral (d :: Integer))

-- | Non-negative strain energies, zero included.
genNonNeg :: Gen Rational
genNonNeg = do
  x <- genPos
  pure (max 0 (x - 1 / 20))

-- | Twin of at2_damage_update: irreversible, in [0, 1], and no damage x >= phi in [0, 1] has lower energy.
prop_at2_damage_update :: Property
prop_at2_damage_update = forAll genPos $ \c -> forAll genNonNeg $ \psie -> forAll genUnit $ \phi ->
  forAll genUnit $ \u ->
    let phi' = damageUpdate c psie phi
        x = phi + u * (1 - phi)
    in phi <= phi' && 0 <= phi' && phi' <= 1 && totalEnergy c psie phi' <= totalEnergy c psie x

-- | Twin of at2_energy_nonincreasing, on the whole domain [0, 1].
prop_at2_energy_nonincreasing :: Property
prop_at2_energy_nonincreasing = forAll genPos $ \c -> forAll genNonNeg $ \psie -> forAll genUnit $ \phi ->
  totalEnergy c psie (damageUpdate c psie phi) <= totalEnergy c psie phi

-- | Twin of at2_balance_eq_total.
prop_at2_balance_eq_total :: Property
prop_at2_balance_eq_total = forAll genPos $ \c -> forAll genNonNeg $ \psie -> forAll genUnit $ \phi ->
  forAll genUnit $ \phi' ->
    (stored psie phi' - stored psie phi) + crackSpent c phi phi' == totalEnergy c psie phi' - totalEnergy c psie phi

-- | Twin of at2_degradation_release_nonneg.
prop_at2_degradation_release_nonneg :: Property
prop_at2_degradation_release_nonneg = forAll genNonNeg $ \psie -> forAll genUnit $ \phi -> forAll genUnit $ \u ->
  let phi' = phi + u * (1 - phi) in 0 <= stored psie phi - stored psie phi'

-- | Twin of at2_griffith_iff.
prop_at2_griffith_iff :: Property
prop_at2_griffith_iff = forAll genPos $ \c -> forAll genNonNeg $ \psie -> forAll genUnit $ \phi ->
  forAll genUnit $ \u ->
    let phi' = phi + u * (1 - phi)
    in ((stored psie phi' - stored psie phi) + crackSpent c phi phi' <= 0)
         == (crackSpent c phi phi' <= stored psie phi - stored psie phi')

-- | Twin of at2_loading_refused: a loading step below full damage raises the stored energy.
prop_at2_loading_refused :: Property
prop_at2_loading_refused = forAll genNonNeg $ \psie -> forAll genPos $ \dpsi -> forAll genUnit $ \phi ->
  phi < 1 ==> stored (psie + dpsi) phi > stored psie phi

-- | Twin of at2_damage_step_secondLaw: umst-formal's executable predicate admits the damage step at unchanged
-- density (the state in Double at this runtime edge).
prop_at2_damage_step_secondLaw :: Property
prop_at2_damage_step_secondLaw = forAll genPos $ \c -> forAll genNonNeg $ \psie -> forAll genUnit $ \phi ->
  let st e = ThermodynamicState 2400 (fromRational e) 0 0 0
  in secondLaw Transition (Thermodynamic (st (stored psie phi)) (st (stored psie (damageUpdate c psie phi))))

fractureAT2Props :: [(String, Property)]
fractureAT2Props =
  [ ("prop_at2_damage_update", prop_at2_damage_update)
  , ("prop_at2_energy_nonincreasing", prop_at2_energy_nonincreasing)
  , ("prop_at2_balance_eq_total", prop_at2_balance_eq_total)
  , ("prop_at2_degradation_release_nonneg", prop_at2_degradation_release_nonneg)
  , ("prop_at2_griffith_iff", prop_at2_griffith_iff)
  , ("prop_at2_loading_refused", prop_at2_loading_refused)
  , ("prop_at2_damage_step_secondLaw", prop_at2_damage_step_secondLaw)
  ]
