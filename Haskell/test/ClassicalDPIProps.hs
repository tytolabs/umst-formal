-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "ClassicalDPI" (FORMAL-CLASSICAL-DPI-DETERMINISTIC-SUMMARY) on random joints and summaries.
-- Mutual information is a Double here; the roundingBound 1e-9 bounds the rounding of tables of at most 6 by 6 cells.
module ClassicalDPIProps
  ( prop_mutualInformation_summary_le
  , prop_logSum_two
  , prop_colFun_merge_le
  , classicalDPIProps
  ) where

import Test.QuickCheck
import ClassicalDPI

roundingBound :: Double
roundingBound = 1e-9

genJoint :: Gen (Int, Joint)
genJoint = do
  n <- choose (1, 6)
  m <- choose (1, 6)
  cells <- vectorOf (n * m) (choose (0, 9 :: Int))
  let cells' = if sum cells == 0 then 1 : drop 1 cells else cells
      massSum = fromIntegral (sum cells') :: Double
      rows = chunk m [fromIntegral c / massSum | c <- cells']
  pure (m, rows)
  where
    chunk _ [] = []
    chunk w xs = take w xs : chunk w (drop w xs)

-- | Twin of mutualInformation_summary_le.
prop_mutualInformation_summary_le :: Property
prop_mutualInformation_summary_le = forAll genJoint $ \(m, j) -> forAll (choose (1, m)) $ \k ->
  forAll (vectorOf m (choose (0, k - 1))) $ \fTable ->
    mutualInformation (summary k (fTable !!) j) <= mutualInformation j + roundingBound

-- | Twin of logSum_two.
prop_logSum_two :: Property
prop_logSum_two = forAll (choose (0, 9 :: Int)) $ \a -> forAll (choose (0, 9 :: Int)) $ \b ->
  forAll (choose (1, 9 :: Int)) $ \s -> forAll (choose (1, 9 :: Int)) $ \t ->
    logSumGap (fromIntegral a) (fromIntegral b) (fromIntegral s) (fromIntegral t) >= negate roundingBound

-- | Twin of colFun_sum_le: merging non-negative columns does not raise the summed column functional.
prop_colFun_merge_le :: Property
prop_colFun_merge_le = forAll (choose (1, 6)) $ \n -> forAll (listOf1 (vectorOf n (choose (0, 9 :: Int)))) $ \cols ->
  let cs = map (map fromIntegral) cols :: [[Double]]
      merged = foldr1 (zipWith (+)) cs
  in colFun merged <= sum (map colFun cs) + roundingBound

classicalDPIProps :: [(String, Property)]
classicalDPIProps =
  [ ("prop_mutualInformation_summary_le", prop_mutualInformation_summary_le)
  , ("prop_logSum_two", prop_logSum_two)
  , ("prop_colFun_merge_le", prop_colFun_merge_le)
  ]
