-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "Culture.CarryingCapacity" (FORMAL-CULTURE-CARRYING-CAPACITY): random windows of lives under an age
-- cap, with death costs paid within a budget, on exact rationals.
module CarryingCapacityProps
  ( prop_liveTicks_le
  , prop_deathCost_le
  , prop_meanLive_le
  , prop_meanLive_le_of_enclosure
  , carryingCapacityProps
  ) where

import Test.QuickCheck
import Culture.CarryingCapacity

genQ :: Integer -> Gen Rational
genQ hi = do
  d <- choose (1, 12)
  n <- choose (0, hi * d)
  pure (fromIntegral n / fromIntegral (d :: Integer))

-- | A window: the age cap, the dead and the alive lives' durations (each at most tau).
genWindow :: Gen (Rational, [Rational], [Rational])
genWindow = do
  tau <- genQ 10
  dead <- listOf (genQ 10 >>= \x -> pure (min tau x))
  alive <- listOf (genQ 10 >>= \x -> pure (min tau x))
  pure (tau, dead, alive)

-- | Twin of liveTicks_le.
prop_liveTicks_le :: Property
prop_liveTicks_le = forAll genWindow $ \(tau, dead, alive) ->
  liveTicks (dead ++ alive) <= tau * fromIntegral (length dead + length alive)

-- | Twin of deathCost_le: erasure at least D l, recovery at most i D l, net within T W.
prop_deathCost_le :: Property
prop_deathCost_le = forAll (choose (0, 50 :: Int)) $ \d -> forAll (genQ 1) $ \i0 -> forAll (genQ 3) $ \extra ->
  forAll (genQ 1) $ \r ->
    let l = ln2Lower
        i = min i0 (9 / 10)
        dd = fromIntegral d
        werase = dd * l + extra
        wrec = r * i * dd * l
        tw = werase - wrec
    in dd * l * (1 - i) <= tw

-- | Twin of meanLive_le: a death count that the budget pays bounds the mean live count.
prop_meanLive_le :: Property
prop_meanLive_le = forAll genWindow $ \(tau, dead, alive) -> forAll (choose (1, 40 :: Int)) $ \tn ->
  forAll (genQ 1) $ \i0 -> forAll (genQ 2) $ \slack ->
    let t = fromIntegral tn
        i = min i0 (9 / 10)
        l = ln2Lower
        w = (fromIntegral (length dead) * l * (1 - i) + slack) / t
    in liveTicks (dead ++ alive) / t <= meanLiveBound tau t w l i (length alive)

-- | Twin of meanLive_le_of_enclosure: the bound at the lower end of the enclosure, for any l in it.
prop_meanLive_le_of_enclosure :: Property
prop_meanLive_le_of_enclosure = forAll genWindow $ \(tau, dead, alive) -> forAll (choose (1, 40 :: Int)) $ \tn ->
  forAll (genQ 1) $ \i0 -> forAll (genQ 1) $ \u ->
    let t = fromIntegral tn
        i = min i0 (9 / 10)
        l = ln2Lower + u * (ln2Upper - ln2Lower)
        w = fromIntegral (length dead) * l * (1 - i) / t
    in liveTicks (dead ++ alive) / t <= meanLiveBound tau t w ln2Lower i (length alive)

carryingCapacityProps :: [(String, Property)]
carryingCapacityProps =
  [ ("prop_liveTicks_le", prop_liveTicks_le)
  , ("prop_deathCost_le", prop_deathCost_le)
  , ("prop_meanLive_le", prop_meanLive_le)
  , ("prop_meanLive_le_of_enclosure", prop_meanLive_le_of_enclosure)
  ]
