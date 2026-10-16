-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "UnfoldTermination" (FORMAL-UNFOLD-TERMINATION-LANDAUER): budgeted runs whose steps each spend at
-- least the enclosed Landauer floor, on exact rationals.
module UnfoldTerminationProps
  ( prop_steps_mul_le
  , prop_steps_le_floor
  , prop_erase_spend_ge_enclosure
  , unfoldTerminationProps
  ) where

import Test.QuickCheck
import UnfoldTermination

genPos :: Gen Rational
genPos = do
  d <- choose (1, 12)
  n <- choose (1, 60 * d)
  pure (fromIntegral n / fromIntegral (d :: Integer))

-- | A run: kT, bits per step b, the budget, and spends each at least the floor.
genRun :: Gen (Rational, Integer, Rational, [Rational])
genRun = do
  kT <- genPos
  b <- choose (1, 8)
  budget <- (* 20) <$> genPos
  extras <- listOf (choose (0, 30 :: Integer))
  let eps = floorLower kT b
  pure (kT, b, budget, map (\e -> eps + fromInteger e / 10) extras)

-- | Twin of steps_mul_le: n eps <= B for the steps a budgeted run takes.
prop_steps_mul_le :: Property
prop_steps_mul_le = forAll genRun $ \(kT, b, budget, ws) ->
  let n = runBudgeted budget ws
  in fromIntegral n * floorLower kT b <= budget && sum (take n ws) <= budget

-- | Twin of steps_le_floor.
prop_steps_le_floor :: Property
prop_steps_le_floor = forAll genRun $ \(kT, b, budget, ws) ->
  toInteger (runBudgeted budget ws) <= maxSteps budget (floorLower kT b)

-- | Twin of erase_spend_ge_enclosure: bits >= b and l >= ln2Lower give b kT ln2Lower <= bits kT l.
prop_erase_spend_ge_enclosure :: Property
prop_erase_spend_ge_enclosure = forAll genPos $ \kT -> forAll (choose (1, 8)) $ \b -> forAll (choose (0, 8)) $ \db ->
  forAll (choose (0, 100 :: Integer)) $ \dl ->
    let bits = b + db
        l = ln2Lower + fromInteger dl / 10000000000
    in floorLower kT b <= fromInteger bits * kT * l

unfoldTerminationProps :: [(String, Property)]
unfoldTerminationProps =
  [ ("prop_steps_mul_le", prop_steps_mul_le)
  , ("prop_steps_le_floor", prop_steps_le_floor)
  , ("prop_erase_spend_ge_enclosure", prop_erase_spend_ge_enclosure)
  ]
