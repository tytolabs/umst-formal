-- |
-- Module      : UMST.Core
-- Description : Universal thermodynamic bounds (all cartridges).
module UMST.Core
  ( massTolerance
  , coreMassOk
  , coreDissipationOk
  ) where

-- | Maximum allowable density change per time step (kg/m³).
-- SSOT: δMass = 100 across Agda / Coq / Lean / Rust.
massTolerance :: Double
massTolerance = 100.0

-- | Universal mass-conservation check (metric ball).
coreMassOk :: Double -> Double -> Double -> Bool
coreMassOk tol rhoOld rhoNew =
  abs (rhoNew - rhoOld) < massTolerance + tol

-- | Universal Clausius–Duhem sign check (dissipation non-negative).
coreDissipationOk :: Double -> Double -> Bool
coreDissipationOk tol diss = diss >= negate tol
