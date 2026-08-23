-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Chem.Environment.EnvironmentContinuum
-- Description : Meso/acting chemistry — environment as Interact-graph sheaf.
--
-- Under @physicalSecondLaw@, vacuum / contained / messy are **named sections** on
-- admissible Interact-graph edges — a simultaneous triple, not an XOR regime pick.
-- Mirrors @Lean/Chem/Environment/EnvironmentContinuum@ and
-- @Coq/Chem/Environment/EnvironmentContinuum@ on @umst-formal/meso_acting@.
--
-- @physics_green@ stays false — thermo witnesses remain Unwired until FORMAL BAR.
module UMST.Chem.Environment.EnvironmentContinuum
  ( -- * Carriers
    InteractGraphEdge
  , EnvironmentContinuumSections
  , EnvironmentSectionRegime (..)
    -- * Conjugate witnesses (finite difference on meso carrier)
  , entropyWitness
  , gateDissipationWitness
  , hydrationIrreversibilityWitness
    -- * Named sections (vacuum | contained | messy — not XOR)
  , vacuumSectionOnEdge
  , containedSectionOnEdge
  , messySectionOnEdge
    -- * Environment sheaf from physicalSecondLaw
  , environmentSheafOnEdge
  , environmentContinuumWellTyped
  , environmentSectionsNamedNotXor
  , environmentContinuumSecondLawEq
    -- * Honesty (mirror @UMST.Chem.Kleisli@)
  , chemPhysicsGreen
  , chemPhysicsGreenFalse
  , environmentContinuumProductionWired
  , environmentContinuumProductionWiredFalse
  , environmentContinuumModuleWitness
  , environmentRegimeCardinality
  , environmentSectionRegimeTags
  ) where

import UMST.Chem.Kleisli (admissibleStep)
import UMST.Concrete
  ( AdmissibilityResult (..)
  , ThermodynamicState (..)
  , gateCheck
  , tolerance
  )

-- | Admissible one-step edge in the Interact graph.
type InteractGraphEdge = (ThermodynamicState, ThermodynamicState)

-- | Named environment sections on an edge — simultaneous triple, not XOR.
type EnvironmentContinuumSections = (Double, Double, Double)

-- | Named environment regime tags (vacuum | contained | messy).
data EnvironmentSectionRegime = VacuumSection | ContainedSection | MessySection
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Nominal chemistry step Δt for gate evaluation (seconds).
chemStepDt :: Double
chemStepDt = 3600.0

-- | Stable tags for the three named environment sections.
environmentSectionRegimeTags :: [String]
environmentSectionRegimeTags = ["vacuum", "contained", "messy"]

-- | Cardinality of named environment sections (not XOR — all three named).
environmentRegimeCardinality :: Int
environmentRegimeCardinality = length environmentSectionRegimeTags

-- | Entropy witness from hydration irreversibility (meso monotone proxy — not caloric S).
entropyWitness :: ThermodynamicState -> Double
entropyWitness s = hydration s

-- | Gate dissipation witness (J/m³/s) from contained Interact admissibility.
gateDissipationWitness :: ThermodynamicState -> ThermodynamicState -> Double
gateDissipationWitness old new = dissipation (gateCheck old new chemStepDt)

-- | Hydration irreversibility witness for messy Ore/Refine neighbor coupling.
hydrationIrreversibilityWitness :: ThermodynamicState -> Double
hydrationIrreversibilityWitness s = hydration s

-- | Vacuum section: second-law entropy production ΔS at monoidal unit (no neighbor channel).
vacuumSectionOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
vacuumSectionOnEdge old new
  | admissibleStep old new =
      let dS = entropyWitness new - entropyWitness old
       in if dS >= negate tolerance
            then Just (max 0 dS)
            else Nothing
  | otherwise = Nothing

-- | Contained section: gate dissipation on Kleisli Interact walls.
containedSectionOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
containedSectionOnEdge old new
  | admissibleStep old new =
      let diss = gateDissipationWitness old new
       in if diss >= negate tolerance
            then Just (max 0 diss)
            else Nothing
  | otherwise = Nothing

-- | Messy section: hydration irreversibility Δn proxy for Ore/Refine neighbor impact.
messySectionOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
messySectionOnEdge old new
  | admissibleStep old new =
      let dH =
            hydrationIrreversibilityWitness new
              - hydrationIrreversibilityWitness old
       in if dH >= negate tolerance
            then Just (max 0 dH)
            else Nothing
  | otherwise = Nothing

-- | Coupled vacuum, contained, messy sections on an admissible Interact-graph edge.
environmentSheafOnEdge
  :: ThermodynamicState -> ThermodynamicState -> Maybe EnvironmentContinuumSections
environmentSheafOnEdge old new
  | admissibleStep old new = do
    v <- vacuumSectionOnEdge old new
    c <- containedSectionOnEdge old new
    m <- messySectionOnEdge old new
    pure (v, c, m)
  | otherwise = Nothing

-- | Well-typed edge: admissible step with optional non-negative named sections.
environmentContinuumWellTyped :: ThermodynamicState -> ThermodynamicState -> Bool
environmentContinuumWellTyped old new =
  not (admissibleStep old new) || case environmentSheafOnEdge old new of
    Nothing -> True
    Just (v, c, m) -> v >= 0 && c >= 0 && m >= 0

-- | Sections are a named triple (vacuum | contained | messy), not XOR regime selection.
environmentSectionsNamedNotXor :: Bool
environmentSectionsNamedNotXor =
  environmentRegimeCardinality == 3
    && length environmentSectionRegimeTags == 3
    && environmentSectionRegimeTags == ["vacuum", "contained", "messy"]

-- | Second-law coherence: contained dissipation matches gate witness on coupled sections.
environmentContinuumSecondLawEq :: ThermodynamicState -> ThermodynamicState -> Bool
environmentContinuumSecondLawEq old new =
  case environmentSheafOnEdge old new of
    Nothing -> True
    Just (_, c, _) ->
      abs (c - gateDissipationWitness old new) < tolerance * max 1 (abs c + 1)

-- | Physics GREEN unauthorized on this scaffold.
chemPhysicsGreen :: Bool
chemPhysicsGreen = False

-- | Lean/Coq: @chem_physics_green_false@.
chemPhysicsGreenFalse :: Bool
chemPhysicsGreenFalse = not chemPhysicsGreen

-- | Production wiring stays open (CAT-00 lift only).
environmentContinuumProductionWired :: Bool
environmentContinuumProductionWired = False

-- | Lean/Coq: @environment_continuum_production_wired_false@.
environmentContinuumProductionWiredFalse :: Bool
environmentContinuumProductionWiredFalse = not environmentContinuumProductionWired

-- | Catalog witness: meso chemistry environment continuum module present.
environmentContinuumModuleWitness :: Bool
environmentContinuumModuleWitness = True
