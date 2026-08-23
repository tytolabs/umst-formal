-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Chem.Constants.TemperatureGraph
-- Description : Meso/acting chemistry — temperature as Interact-graph function.
--
-- Under Landauer, @1/T = ∂S/∂U@ on admissible Interact-graph edges — temperature
-- is a graph function, not a floating pin.  Mirrors
-- @Lean/Chem/Constants/TemperatureGraph@ and @Coq/Chem/Constants/TemperatureGraph@
-- on @umst-formal/meso_acting@, anchored in @Chem.SecondLaw@ via gate admissibility.
--
-- @physics_green@ stays false — thermo witnesses remain Unwired until FORMAL BAR.
module UMST.Chem.Constants.TemperatureGraph
  ( -- * Carriers
    InteractGraphEdge
    -- * Conjugate witnesses (finite difference on meso carrier)
  , entropyWitness
  , internalEnergyWitness
  , inverseTemperatureBeta
  , temperatureKelvinOnEdge
    -- * Interact-graph function
  , temperatureGraphFunction
  , temperatureGraphWellTyped
  , inverseTemperatureConjugateEq
    -- * Honesty (mirror @UMST.Chem.Kleisli@)
  , chemPhysicsGreen
  , chemPhysicsGreenFalse
  , temperatureGraphProductionWired
  , temperatureGraphProductionWiredFalse
  , temperatureGraphModuleWitness
  ) where

import UMST.Chem.Kleisli (admissibleStep)
import UMST.Concrete (ThermodynamicState (..), tolerance)

-- | Admissible one-step edge in the Interact graph.
type InteractGraphEdge = (ThermodynamicState, ThermodynamicState)

-- | Entropy witness from hydration irreversibility (meso monotone proxy — not caloric S).
entropyWitness :: ThermodynamicState -> Double
entropyWitness s = hydration s

-- | Internal energy density witness (J/m³) from the Helmholtz carrier.
internalEnergyWitness :: ThermodynamicState -> Double
internalEnergyWitness s = density s * negate (freeEnergy s)

-- | Second-law conjugate β = ∂S/∂U ≈ ΔS/ΔU; refuses ∂U ≈ 0 or β ≤ 0.
inverseTemperatureBeta :: ThermodynamicState -> ThermodynamicState -> Maybe Double
inverseTemperatureBeta old new =
  let dU = internalEnergyWitness new - internalEnergyWitness old
      dS = entropyWitness new - entropyWitness old
   in if abs dU < tolerance
        then Nothing
        else if dU > 0 && dS >= 0
          then Just (dS / dU)
          else Nothing

-- | Temperature in kelvin on an edge: T = 1/β when β > 0.
temperatureKelvinOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
temperatureKelvinOnEdge old new = do
  beta <- inverseTemperatureBeta old new
  if beta > tolerance then Just (recip beta) else Nothing

-- | Interact-graph temperature field: defined only on admissible edges.
temperatureGraphFunction :: ThermodynamicState -> ThermodynamicState -> Maybe Double
temperatureGraphFunction old new
  | admissibleStep old new = temperatureKelvinOnEdge old new
  | otherwise              = Nothing

-- | Well-typed edge: admissible step with optional positive temperature.
temperatureGraphWellTyped :: ThermodynamicState -> ThermodynamicState -> Bool
temperatureGraphWellTyped old new =
  not (admissibleStep old new) || case temperatureGraphFunction old new of
    Nothing -> True
    Just t  -> t > 0

-- | Conjugate identity: when T is defined, @1/T@ matches β on the edge.
inverseTemperatureConjugateEq :: ThermodynamicState -> ThermodynamicState -> Bool
inverseTemperatureConjugateEq old new =
  case (temperatureGraphFunction old new, inverseTemperatureBeta old new) of
    (Just t, Just beta) -> abs (recip t - beta) < tolerance
    _                   -> True

-- | Physics GREEN unauthorized on this scaffold.
chemPhysicsGreen :: Bool
chemPhysicsGreen = False

-- | Lean/Coq: @chem_physics_green_false@.
chemPhysicsGreenFalse :: Bool
chemPhysicsGreenFalse = not chemPhysicsGreen

-- | Production wiring stays open (CAT-00 lift only).
temperatureGraphProductionWired :: Bool
temperatureGraphProductionWired = False

-- | Lean/Coq: @temperature_graph_production_wired_false@.
temperatureGraphProductionWiredFalse :: Bool
temperatureGraphProductionWiredFalse = not temperatureGraphProductionWired

-- | Catalog witness: meso chemistry temperature graph module present.
temperatureGraphModuleWitness :: Bool
temperatureGraphModuleWitness = True
