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

prop_dignity_step_honest_non_decreasing :: Double -> Double -> Double -> Double -> Property
prop_dignity_step_honest_non_decreasing tK d mi e =
  tK > 0 && d >= 0 && d <= dMax && mi >= 0 && e >= 0 && honestSpend tK mi e ==>
    let d' = dignityStep tK d mi e
     in d' + 1e-12 >= d && d' <= dMax + 1e-12

prop_dignity_step_sub_landauer_fixed :: Double -> Double -> Double -> Double -> Property
prop_dignity_step_sub_landauer_fixed tK d mi e =
  tK > 0 && d >= 0 && d <= dMax && mi >= 0 && e >= 0 && not (honestSpend tK mi e) ==>
    abs (dignityStep tK d mi e - d) <= 1e-15

prop_dignity_step_monotone_mi :: Double -> Double -> Double -> Double -> Double -> Property
prop_dignity_step_monotone_mi tK d mi1 mi2 e =
  tK > 0
    && d >= 0
    && d <= dMax
    && mi1 >= 0
    && mi2 >= 0
    && mi1 <= mi2
    && e >= 0
    && honestSpend tK mi1 e
    && honestSpend tK mi2 e ==>
      let v1 = dignityStep tK d mi1 e
          v2 = dignityStep tK d mi2 e
       in v1 - 1e-12 <= v2 + 1e-12

prop_dignity_list_sum_nonneg :: [Double] -> Property
prop_dignity_list_sum_nonneg xs =
  let ys = map (max 0 . min dMax) xs
      s = sum ys
   in property (s >= 0 - 1e-12 && s <= fromIntegral (length ys) * dMax + 1e-9)
