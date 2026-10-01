-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Engineering mirror of `Lean/Dignity.lean` (thermodynamic–epistemic dignity step).
module Dignity where

import Test.QuickCheck

dMax :: Double
dMax = 10.0

kB :: Double
kB = 1.380649e-23

landauerJoulesPerBit :: Double -> Double
landauerJoulesPerBit t = kB * max t 0 * log 2

honestSpend :: Double -> Double -> Double -> Bool
honestSpend tK mi e = landauerJoulesPerBit tK * mi <= e

dignityStep :: Double -> Double -> Double -> Double -> Double
dignityStep tK current mi e =
  if honestSpend tK mi e
    then min dMax (current + mi)
    else current

prop_dignity_try_range :: Double -> Property
prop_dignity_try_range x =
  let ok = x >= 0 && x <= dMax
      mk = if ok then Just x else Nothing
   in classify ok "in-range" (mk == Nothing || abs (maybe 0 id mk - x) <= 1e-15)

-- The step properties build their inputs inside the Lean hypotheses (temperature positive, dignity in
-- [0, dMax], mutual information nonnegative, the spend honest or sub-Landauer) instead of filtering random
-- Doubles with `==>`, which discarded almost every case. Floating rounding is monotone, so the
-- conclusions hold exactly.

-- | Temperature in kelvin, positive.
kelvin :: Double -> Double
kelvin t = 1 + abs t

-- | A dignity value in [0, dMax].
dignity :: Double -> Double
dignity d = min dMax (abs d)

prop_dignity_step_honest_non_decreasing :: Double -> Double -> Double -> Double -> Bool
prop_dignity_step_honest_non_decreasing t0 d0 mi0 slack =
  let tK = kelvin t0
      d = dignity d0
      mi = abs mi0
      e = landauerJoulesPerBit tK * mi + abs slack
      d' = dignityStep tK d mi e
   in honestSpend tK mi e && d' >= d && d' <= dMax

prop_dignity_step_sub_landauer_fixed :: Double -> Double -> Double -> Double -> Bool
prop_dignity_step_sub_landauer_fixed t0 d0 mi0 frac =
  let tK = kelvin t0
      d = dignity d0
      mi = 1 + abs mi0
      e = landauerJoulesPerBit tK * mi * (abs (sin frac) * 0.5)
   in not (honestSpend tK mi e) && dignityStep tK d mi e == d

prop_dignity_step_monotone_mi :: Double -> Double -> Double -> Double -> Double -> Bool
prop_dignity_step_monotone_mi t0 d0 a b slack =
  let tK = kelvin t0
      d = dignity d0
      mi1 = abs a
      mi2 = mi1 + abs b
      e = landauerJoulesPerBit tK * mi2 + abs slack
   in honestSpend tK mi1 e
        && honestSpend tK mi2 e
        && dignityStep tK d mi1 e <= dignityStep tK d mi2 e

prop_dignity_list_sum_nonneg :: [Double] -> Property
prop_dignity_list_sum_nonneg xs =
  let ys = map (max 0 . min dMax) xs
      s = sum ys
   in property (s >= 0 - 1e-12 && s <= fromIntegral (length ys) * dMax + 1e-9)
