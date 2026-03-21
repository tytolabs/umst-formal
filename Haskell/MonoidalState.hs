-- |
-- Module      : MonoidalState
-- Description : Weighted combination of ThermodynamicState
--               (Haskell parity of Lean/MonoidalState.lean)
--
-- Mirrors the Lean theorems:
--   * combine_one / combine_zero (unit laws)
--   * combine_half (midpoint)
--   * density interpolation
--   * free-energy convexity
--   * hydration-floor preservation
module MonoidalState
  ( ThermodynamicState(..)
  , combine
  , zeroState
  , combine_one_check
  , combine_zero_check
  , combine_density_between
  , combine_freeEnergy_le
  , combine_hydration_ge
  ) where

-- | A material state with 4 rational fields.
data ThermodynamicState = TS
  { density    :: Double
  , freeEnergy :: Double
  , hydration  :: Double
  , strength   :: Double
  } deriving (Show, Eq)

-- | Zero state (monoidal unit).
zeroState :: ThermodynamicState
zeroState = TS 0 0 0 0

-- | Weighted combination: w · s1 + (1 - w) · s2, componentwise.
combine :: Double -> ThermodynamicState -> ThermodynamicState -> ThermodynamicState
combine w s1 s2 = TS
  { density    = w * density s1    + (1 - w) * density s2
  , freeEnergy = w * freeEnergy s1 + (1 - w) * freeEnergy s2
  , hydration  = w * hydration s1  + (1 - w) * hydration s2
  , strength   = w * strength s1   + (1 - w) * strength s2
  }

-- | Check: combine 1 s1 s2 ≈ s1
combine_one_check :: ThermodynamicState -> ThermodynamicState -> Bool
combine_one_check s1 s2 =
  let c = combine 1.0 s1 s2
      eps = 1e-12
  in abs (density c - density s1) < eps &&
     abs (freeEnergy c - freeEnergy s1) < eps &&
     abs (hydration c - hydration s1) < eps &&
     abs (strength c - strength s1) < eps

-- | Check: combine 0 s1 s2 ≈ s2
combine_zero_check :: ThermodynamicState -> ThermodynamicState -> Bool
combine_zero_check s1 s2 =
  let c = combine 0.0 s1 s2
      eps = 1e-12
  in abs (density c - density s2) < eps &&
     abs (freeEnergy c - freeEnergy s2) < eps &&
     abs (hydration c - hydration s2) < eps &&
     abs (strength c - strength s2) < eps

-- | Combined density is between s1 and s2 densities for w in [0,1].
combine_density_between :: Double -> ThermodynamicState -> ThermodynamicState -> Bool
combine_density_between w s1 s2
  | w < 0 || w > 1 = True  -- vacuously
  | otherwise =
      let lo = min (density s1) (density s2)
          hi = max (density s1) (density s2)
          cd = density (combine w s1 s2)
      in cd >= lo - 1e-12 && cd <= hi + 1e-12

-- | Free energy of combination does not exceed max of inputs.
combine_freeEnergy_le :: Double -> ThermodynamicState -> ThermodynamicState -> Bool
combine_freeEnergy_le w s1 s2
  | w < 0 || w > 1 = True
  | otherwise =
      let psiMax = max (freeEnergy s1) (freeEnergy s2)
          cpsi = freeEnergy (combine w s1 s2)
      in cpsi <= psiMax + 1e-12

-- | Hydration of combination ≥ min of inputs.
combine_hydration_ge :: Double -> ThermodynamicState -> ThermodynamicState -> Bool
combine_hydration_ge w s1 s2
  | w < 0 || w > 1 = True
  | otherwise =
      let aMin = min (hydration s1) (hydration s2)
          ca = hydration (combine w s1 s2)
      in ca >= aMin - 1e-12
