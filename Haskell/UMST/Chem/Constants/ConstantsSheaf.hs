-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Chem.Constants.ConstantsSheaf
-- Description : Meso/acting chemistry — T, P, μ as interdependent Interact-graph sections.
--
-- Under @physicalSecondLaw@ and Gibbs–Duhem, temperature, pressure, and chemical
-- potential are coupled sections on admissible Interact-graph edges — not isolated
-- floats.  Mirrors @Lean/Chem/Constants/ConstantsSheaf@ and
-- @Coq/Chem/Constants/ConstantsSheaf@ on @umst-formal/meso_acting@.
--
-- @physics_green@ stays false — thermo witnesses remain Unwired until FORMAL BAR.
module UMST.Chem.Constants.ConstantsSheaf
  ( -- * Carriers
    InteractGraphEdge
    -- * Conjugate witnesses (finite difference on meso carrier)
  , entropyWitness
  , internalEnergyWitness
  , specificVolumeWitness
  , gibbsWitness
  , compositionWitness
    -- * T section (1/T = ∂S/∂U)
  , inverseTemperatureBeta
  , temperatureSectionOnEdge
    -- * P section (−∂U/∂V)
  , pressureSectionOnEdge
    -- * μ section (∂G/∂n)
  , chemicalPotentialSectionOnEdge
    -- * Interdependent constants sheaf
  , constantsSheafOnEdge
  , constantsSheafWellTyped
  , gibbsDuhemInterdependenceEq
    -- * Honesty (mirror @UMST.Chem.Kleisli@)
  , chemPhysicsGreen
  , chemPhysicsGreenFalse
  , constantsSheafProductionWired
  , constantsSheafProductionWiredFalse
  , constantsSheafModuleWitness
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

-- | Specific volume witness (m³/kg) — mechanical conjugate carrier for P.
specificVolumeWitness :: ThermodynamicState -> Double
specificVolumeWitness s = recip (density s)

-- | Gibbs free energy density witness (J/m³) for μ = ∂G/∂n sections.
gibbsWitness :: ThermodynamicState -> Double
gibbsWitness s = density s * freeEnergy s

-- | Composition extent witness (meso hydration proxy for species amount n).
compositionWitness :: ThermodynamicState -> Double
compositionWitness s = hydration s

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

-- | Temperature section on an edge: T = 1/β when β > 0.
temperatureSectionOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
temperatureSectionOnEdge old new = do
  beta <- inverseTemperatureBeta old new
  if beta > tolerance then Just (recip beta) else Nothing

-- | Pressure section P = −∂U/∂V ≈ −ΔU/ΔV; refuses ∂V ≈ 0.
pressureSectionOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
pressureSectionOnEdge old new =
  let dU = internalEnergyWitness new - internalEnergyWitness old
      dV = specificVolumeWitness new - specificVolumeWitness old
   in if abs dV < tolerance
        then Nothing
        else Just (negate (dU / dV))

-- | Chemical potential section μ = ∂G/∂n ≈ ΔG/Δn; refuses ∂n ≈ 0.
chemicalPotentialSectionOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
chemicalPotentialSectionOnEdge old new =
  let dG = gibbsWitness new - gibbsWitness old
      dn = compositionWitness new - compositionWitness old
   in if abs dn < tolerance
        then Nothing
        else Just (dG / dn)

-- | Coupled T, P, μ sections on an admissible Interact-graph edge.
constantsSheafOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe (Double, Double, Double)
constantsSheafOnEdge old new
  | admissibleStep old new = do
    t <- temperatureSectionOnEdge old new
    p <- pressureSectionOnEdge old new
    mu <- chemicalPotentialSectionOnEdge old new
    pure (t, p, mu)
  | otherwise = Nothing

-- | Well-typed edge: admissible step with optional positive T and finite P, μ.
constantsSheafWellTyped :: ThermodynamicState -> ThermodynamicState -> Bool
constantsSheafWellTyped old new =
  not (admissibleStep old new) || case constantsSheafOnEdge old new of
    Nothing -> True
    Just (t, _, _) -> t > 0

-- | Gibbs–Duhem finite-difference: ΔG ≈ P ΔV + μ Δn − T ΔS on coupled sections.
gibbsDuhemInterdependenceEq :: ThermodynamicState -> ThermodynamicState -> Bool
gibbsDuhemInterdependenceEq old new =
  case constantsSheafOnEdge old new of
    Nothing -> True
    Just (t, p, mu) ->
      let dG = gibbsWitness new - gibbsWitness old
          dV = specificVolumeWitness new - specificVolumeWitness old
          dN = compositionWitness new - compositionWitness old
          dS = entropyWitness new - entropyWitness old
          predicted = p * dV + mu * dN - t * dS
       in abs (dG - predicted) < tolerance * max 1 (abs dG + abs predicted)

-- | Physics GREEN unauthorized on this scaffold.
chemPhysicsGreen :: Bool
chemPhysicsGreen = False

-- | Lean/Coq: @chem_physics_green_false@.
chemPhysicsGreenFalse :: Bool
chemPhysicsGreenFalse = not chemPhysicsGreen

-- | Production wiring stays open (CAT-00 lift only).
constantsSheafProductionWired :: Bool
constantsSheafProductionWired = False

-- | Lean/Coq: @constants_sheaf_production_wired_false@.
constantsSheafProductionWiredFalse :: Bool
constantsSheafProductionWiredFalse = not constantsSheafProductionWired

-- | Catalog witness: meso chemistry constants sheaf module present.
constantsSheafModuleWitness :: Bool
constantsSheafModuleWitness = True
