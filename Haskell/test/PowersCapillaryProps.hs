-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of Powers' capillary porosity in closed form and its rounded coefficients (twins of
-- Lean/Concrete/PowersCapillary.lean, Coq/Concrete/PowersCapillary.v and Agda/Concrete/PowersCapillary.agda).
-- Every quantity is an exact rational, so each law is checked with equality.
module PowersCapillaryProps
  ( prop_powers_capillary_porosity_eq
  , prop_powers_capillary_water_coeff
  , prop_powers_paste_offset_coeff
  , prop_powers_cement_volume_coeff
  , prop_powers_capillary_water_coeff_err
  , prop_powers_paste_offset_coeff_err
  , powersCapillaryProps
  ) where

import Test.QuickCheck

import qualified UMST.Constants.SI as SI

-- | A non-negative rational in [0, 1] with denominator 1000.
genUnit :: Gen Rational
genUnit = (\n -> fromInteger n / 1000) <$> choose (0, 1000 :: Integer)

-- | Initial water fraction of a paste at water-cement ratio w (by mass).
waterFraction :: Rational -> Rational
waterFraction w = w * SI.densityRatio / (w * SI.densityRatio + 1)

-- | Capillary water plus chemical-shrinkage voids at water-cement ratio w and degree of hydration a.
capillaryPorosity :: Rational -> Rational -> Rational
capillaryPorosity w a =
  let p = waterFraction w
   in (p - SI.capillaryConsumption * (1 - p) * a) + SI.shrinkageVolume * (1 - p) * a

-- | x rounded at scale k: floor (k * x + 1/2) / k.
roundAt :: Integer -> Rational -> Rational
roundAt k x = fromInteger (floor (fromInteger k * x + 1 / 2)) / fromInteger k

prop_powers_capillary_porosity_eq :: Property
prop_powers_capillary_porosity_eq = forAll ((* 2) <$> genUnit) $ \w -> forAll genUnit $ \a ->
  capillaryPorosity w a == (w - SI.criticalWcSpace * a) / (w + 1 / SI.densityRatio)

prop_powers_capillary_water_coeff :: Property
prop_powers_capillary_water_coeff = once $ roundAt 100 SI.criticalWcSpace == 36 / 100

prop_powers_paste_offset_coeff :: Property
prop_powers_paste_offset_coeff = once $ roundAt 100 (1 / SI.densityRatio) == 32 / 100

prop_powers_cement_volume_coeff :: Property
prop_powers_cement_volume_coeff = once $ roundAt 1000 (1 / SI.densityRatio) == 317 / 1000

prop_powers_capillary_water_coeff_err :: Property
prop_powers_capillary_water_coeff_err = once $ abs (roundAt 100 SI.criticalWcSpace - SI.criticalWcSpace) <= 1 / 200

prop_powers_paste_offset_coeff_err :: Property
prop_powers_paste_offset_coeff_err =
  once $ abs (roundAt 100 (1 / SI.densityRatio) - 1 / SI.densityRatio) <= 1 / 200

-- | Property name and property, in statement order.
powersCapillaryProps :: [(String, Property)]
powersCapillaryProps =
  [ ("powers_capillary_porosity_eq", prop_powers_capillary_porosity_eq)
  , ("powers_capillary_water_coeff", prop_powers_capillary_water_coeff)
  , ("powers_paste_offset_coeff", prop_powers_paste_offset_coeff)
  , ("powers_cement_volume_coeff", prop_powers_cement_volume_coeff)
  , ("powers_capillary_water_coeff_err", prop_powers_capillary_water_coeff_err)
  , ("powers_paste_offset_coeff_err", prop_powers_paste_offset_coeff_err)
  ]
