-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Chem.Environment.EnvSampleSections
-- Description : Meso/acting chemistry — named Env sample sections (probe layer).
--
-- Vacuum / contained / messy are **named sample sections** of one Env sheaf on
-- admissible Interact-graph edges — a simultaneous triple, not XOR worlds and
-- not a third axiom.  Sample-probe layer on @EnvironmentContinuum@.
-- Mirrors @Lean/Chem/Environment/EnvSampleSections@ and
-- @Coq/Chem/Environment/EnvSampleSections@ on @umst-formal/meso_acting@.
--
module UMST.Chem.Environment.EnvSampleSections
  ( -- * Carriers (reused from continuum sheaf)
    InteractGraphEdge
  , EnvironmentSampleSections
  , EnvironmentSectionRegime (..)
    -- * Named sample probes (vacuum | contained | messy — not XOR)
  , vacuumSampleSectionOnEdge
  , containedSampleSectionOnEdge
  , messySampleSectionOnEdge
  , sampleSectionOnEdge
    -- * Simultaneous triple on one admissible edge
  , envSampleSectionsOnEdge
  , envSampleSectionsWellTyped
  , envSampleSectionsTripleOnEdgeWitness
  , envSampleSectionsRegimeDistinct
    -- * Honesty (mirror @UMST.Chem.Kleisli@)
  , environmentSectionRegimeTags
  , environmentRegimeCardinality
  ) where

import UMST.Chem.Environment.EnvironmentContinuum
  ( EnvironmentContinuumSections
  , EnvironmentSectionRegime (..)
  , InteractGraphEdge
  , containedSectionOnEdge
  , environmentRegimeCardinality
  , environmentSectionRegimeTags
  , environmentSheafOnEdge
  , messySectionOnEdge
  , vacuumSectionOnEdge
  )
import UMST.Chem.Kleisli (admissibleStep)
import UMST.Concrete (ThermodynamicState (..))

-- | Named environment sample sections on an edge — simultaneous triple, not XOR.
type EnvironmentSampleSections = EnvironmentContinuumSections

-- | Vacuum sample probe: entropy production ΔS at monoidal unit.
vacuumSampleSectionOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
vacuumSampleSectionOnEdge = vacuumSectionOnEdge

-- | Contained sample probe: gate dissipation on Kleisli Interact walls.
containedSampleSectionOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
containedSampleSectionOnEdge = containedSectionOnEdge

-- | Messy sample probe: hydration irreversibility Δn for Ore/Refine neighbors.
messySampleSectionOnEdge :: ThermodynamicState -> ThermodynamicState -> Maybe Double
messySampleSectionOnEdge = messySectionOnEdge

-- | Regime-tagged sample probe — named section accessor, not XOR regime pick.
sampleSectionOnEdge
  :: EnvironmentSectionRegime -> ThermodynamicState -> ThermodynamicState -> Maybe Double
sampleSectionOnEdge regime old new =
  case regime of
    VacuumSection   -> vacuumSampleSectionOnEdge old new
    ContainedSection -> containedSampleSectionOnEdge old new
    MessySection    -> messySampleSectionOnEdge old new

-- | Coupled vacuum, contained, messy sample sections on one admissible edge.
envSampleSectionsOnEdge
  :: ThermodynamicState -> ThermodynamicState -> Maybe EnvironmentSampleSections
envSampleSectionsOnEdge = environmentSheafOnEdge

-- | Well-typed edge: admissible step with optional non-negative sample sections.
envSampleSectionsWellTyped :: ThermodynamicState -> ThermodynamicState -> Bool
envSampleSectionsWellTyped old new =
  not (admissibleStep old new) || case envSampleSectionsOnEdge old new of
    Nothing -> True
    Just (v, c, m) -> v >= 0 && c >= 0 && m >= 0

-- | Named regime tags are pairwise distinct (not collapsed to one sample world).
envSampleSectionsRegimeDistinct :: Bool
envSampleSectionsRegimeDistinct =
  VacuumSection /= ContainedSection
    && VacuumSection /= MessySection
    && ContainedSection /= MessySection

-- | On admissible edges, all three named probes return a triple — not a sum pick.
envSampleSectionsTripleOnEdgeWitness :: ThermodynamicState -> ThermodynamicState -> Bool
envSampleSectionsTripleOnEdgeWitness old new =
  case envSampleSectionsOnEdge old new of
    Just (v, c, m) ->
      v >= 0
        && c >= 0
        && m >= 0
        && vacuumSampleSectionOnEdge old new == Just v
        && containedSampleSectionOnEdge old new == Just c
        && messySampleSectionOnEdge old new == Just m
    Nothing -> not (admissibleStep old new)

