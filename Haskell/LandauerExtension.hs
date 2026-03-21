-- |
-- Module      : LandauerExtension
-- Description : Extended Landauer bounds (Haskell parity of Lean/LandauerExtension.lean)
--
-- Mirrors the 5 extension theorems:
--   * 'landauerBound_temp_scaling' : bound scales linearly in T
--   * 'landauerEnergy_mono'        : energy scale is monotone in T
--   * 'landauerBound_nBit'         : combined bound for n independent bits
--   * 'landauerBound_additive'     : sum of two bounds is a combined lower bound
--   * 'landauerEnergy_300K_pos'    : SI bound at 300 K is strictly positive
module LandauerExtension
  ( kBoltzmann
  , ln2
  , landauerBitEnergy
  , landauerEnergyMono
  , landauerBound_nBit
  , landauerBound_additive
  , landauerEnergy_300K_pos
  ) where

-- | SI Boltzmann constant (J/K)
kBoltzmann :: Double
kBoltzmann = 1.380649e-23

ln2 :: Double
ln2 = log 2

-- | One Landauer bit-energy at temperature T (J)
landauerBitEnergy :: Double -> Double
landauerBitEnergy t = kBoltzmann * t * ln2

-- | Energy scale is monotone in T: T1 <= T2  =>  E(T1) <= E(T2)
landauerEnergyMono :: Double -> Double -> Bool
landauerEnergyMono t1 t2
  | t1 <= t2  = landauerBitEnergy t1 <= landauerBitEnergy t2
  | otherwise = True   -- vacuously

-- | Combined lower bound for n independent bits at temperature T (J)
landauerBound_nBit :: Int -> Double -> Double
landauerBound_nBit n t = fromIntegral n * landauerBitEnergy t

-- | Sum of two individual dissipation lower bounds
landauerBound_additive :: Double -> Double -> Double
landauerBound_additive t1 t2 = landauerBitEnergy t1 + landauerBitEnergy t2

-- | The Landauer bit-energy at 300 K is strictly positive
landauerEnergy_300K_pos :: Bool
landauerEnergy_300K_pos = landauerBitEnergy 300 > 0
