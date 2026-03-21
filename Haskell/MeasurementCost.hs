-- |
-- Module      : MeasurementCost
-- Description : Thermodynamic cost bounds for measurement (mirror of Lean/MeasurementCost.lean)
--
-- Exposes the Landauer energy bound for discrete joint distributions.

module MeasurementCost
  ( kBoltzmannSI
  , entropyBits
  , mutualInformationBits
  , measurementEnergyLowerBound
  ) where

import InfoTheory

-- | SI Boltzmann constant (J/K)
kBoltzmannSI :: Double
kBoltzmannSI = 1.380649e-23

-- | Shannon entropy in bits
entropyBits :: [Double] -> Double
entropyBits dist = - sum [ p * logBase 2 p | p <- dist, p > 0 ]

-- | Mutual information I(X;Y) = H(X) + H(Y) - H(X,Y) in bits
mutualInformationBits :: [[Double]] -> Double
mutualInformationBits joint =
  let px = marginalFirst joint
      py = marginalSecond joint
      hX = entropyBits px
      hY = entropyBits py
      hXY = entropyBits (concat joint)
  in hX + hY - hXY

-- | Minimum energy (Joules) required to acquire 'joint' correlation at temp T.
--   Since we computed MI in bits, the factor is T * k_B * ln(2).
measurementEnergyLowerBound :: Double -> [[Double]] -> Double
measurementEnergyLowerBound temp joint =
  let miBits = mutualInformationBits joint
  in miBits * kBoltzmannSI * temp * log 2
