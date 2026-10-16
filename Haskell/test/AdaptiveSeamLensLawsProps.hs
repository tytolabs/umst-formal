-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "AdaptiveSeamLensLaws" (FORMAL-SEAM-AND-LENS-LAWS): transfer lenses on random fine states, seams
-- between random admissible steps and GENERIC pairs on random gradients, on exact rationals.
module AdaptiveSeamLensLawsProps
  ( prop_lens_getPut
  , prop_lens_putGet
  , prop_seam_creates_no_energy
  , prop_seam_refused
  , prop_generic_energy_rate
  , prop_generic_entropy_rate_nonneg
  , adaptiveSeamLensLawsProps
  ) where

import Test.QuickCheck
import AdaptiveSeamLensLaws

genQ :: Gen Rational
genQ = do
  d <- choose (1, 9)
  n <- choose (-40, 40)
  pure (fromIntegral (n :: Integer) / fromIntegral (d :: Integer))

genVec :: Int -> Gen [Rational]
genVec n = vectorOf n genQ

prop_lens_getPut :: Property
prop_lens_getPut = forAll (choose (0, 6)) $ \n -> forAll (genVec (2 * n)) $ \s ->
  lensPut s (restrict s) == s

prop_lens_putGet :: Property
prop_lens_putGet = forAll (choose (0, 6)) $ \n -> forAll (genVec (2 * n)) $ \s -> forAll (genVec n) $ \v ->
  restrict (lensPut s v) == v

-- | Admissible steps whose supplied works cancel and whose informations cancel.
prop_seam_creates_no_energy :: Property
prop_seam_creates_no_energy = forAll ((,,,,) <$> (abs <$> genQ) <*> genQ <*> genQ <*> (abs <$> genQ) <*> (abs <$> genQ)) $
  \(c, w, i, a, b) ->
    let s1 = SeamStep (w + c * i - a) w i
        s2 = SeamStep (negate w + c * negate i - b) (negate w) (negate i)
    in oneIneq c s1 && oneIneq c s2 && sdF s1 + sdF s2 <= 0

-- | A composite whose free energy rises under a power-preserving seam breaks one subsystem's inequality.
prop_seam_refused :: Property
prop_seam_refused = forAll ((,,,,) <$> (abs <$> genQ) <*> genQ <*> genQ <*> genQ <*> genQ) $ \(c, w, i, f1, f2) ->
  let s1 = SeamStep f1 w i
      s2 = SeamStep f2 (negate w) (negate i)
  in f1 + f2 > 0 ==> not (oneIneq c s1 && oneIneq c s2)

genGeneric :: Gen ([Rational], [Rational], [[Rational]], [[Rational]])
genGeneric = do
  n <- choose (2, 5)
  gE <- genVec n
  gS <- genVec n
  u <- genVec n
  v <- genVec n
  w <- genVec n
  pure (gE, gS, antisymOf (orthTo gS u) (orthTo gS v), psdOf (orthTo gE w))

prop_generic_energy_rate :: Property
prop_generic_energy_rate = forAll genGeneric $ \(gE, gS, l, m) ->
  dot gE (zipWith (+) (mulVec l gE) (mulVec m gS)) == 0

prop_generic_entropy_rate_nonneg :: Property
prop_generic_entropy_rate_nonneg = forAll genGeneric $ \(gE, gS, l, m) ->
  dot gS (zipWith (+) (mulVec l gE) (mulVec m gS)) >= 0

adaptiveSeamLensLawsProps :: [(String, Property)]
adaptiveSeamLensLawsProps =
  [ ("prop_lens_getPut", prop_lens_getPut)
  , ("prop_lens_putGet", prop_lens_putGet)
  , ("prop_seam_creates_no_energy", prop_seam_creates_no_energy)
  , ("prop_seam_refused", prop_seam_refused)
  , ("prop_generic_energy_rate", prop_generic_energy_rate)
  , ("prop_generic_entropy_rate_nonneg", prop_generic_entropy_rate_nonneg)
  ]
