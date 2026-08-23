-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem.Environment.EnvSampleSections — meso/acting sample probes.
--
-- CHEM-L0-FORMAL-01 / CHEM-NS-W0-AXIOM (umst-formal acting fiber only).
-- Vacuum / contained / messy are **named sample sections** of one Env sheaf on
-- admissible Interact-graph edges — a simultaneous triple, not XOR worlds and
-- not a third axiom.  Sample-probe layer on @EnvironmentContinuum@.
--
-- Imports EnvironmentContinuum only; ZERO new postulates.
-- physics_green: false — thermo witnesses remain Unwired until FORMAL BAR.
------------------------------------------------------------------------

module Chem.Environment.EnvSampleSections where

open import Chem.Environment.EnvironmentContinuum
open import Chem.KleisliInteract using (admissible-refl)
open import Concrete.Gate using (ThermodynamicState; gate)
open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ)
open import Data.Rational as ℚ using (ℚ; 1ℚ; normalize)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Regime tags (named sections — not XOR regime selection)
------------------------------------------------------------------------

EnvironmentSectionRegime : Set
EnvironmentSectionRegime = EnvironmentVertex

environmentSectionRegimeTags : List EnvironmentSectionRegime
environmentSectionRegimeTags = envVacuum ∷ envContained ∷ envMessy ∷ []

environmentRegimeCardinality : ℕ
environmentRegimeCardinality = length environmentSectionRegimeTags

------------------------------------------------------------------------
-- Named sample probes (vacuum | contained | messy — not XOR)
------------------------------------------------------------------------

EnvironmentSampleSections : Set
EnvironmentSampleSections = ℚ × ℚ × ℚ

vacuumSampleProbe : EnvironmentContinuumSheaf → ℚ
vacuumSampleProbe = vacuumSection

containedSampleProbe : EnvironmentContinuumSheaf → ℚ
containedSampleProbe = containedSection

messySampleProbe : EnvironmentContinuumSheaf → ℚ
messySampleProbe = messySection

sampleSectionAtRegime :
  EnvironmentSectionRegime → EnvironmentContinuumSheaf → ℚ
sampleSectionAtRegime envVacuum = vacuumSampleProbe
sampleSectionAtRegime envContained = containedSampleProbe
sampleSectionAtRegime envMessy = messySampleProbe

------------------------------------------------------------------------
-- Simultaneous triple on one Env sheaf (not XOR sample-space pick)
------------------------------------------------------------------------

envSampleSectionsTriple : EnvironmentContinuumSheaf → EnvironmentSampleSections
envSampleSectionsTriple S =
  ( vacuumSampleProbe S
  , containedSampleProbe S
  , messySampleProbe S
  )

envSampleSectionsTripleComponents :
  ∀ S →
  envSampleSectionsTriple S
  ≡ ( vacuumSampleProbe S
    , containedSampleProbe S
    , messySampleProbe S
    )
envSampleSectionsTripleComponents S = refl

------------------------------------------------------------------------
-- Edge sample probes (reuse continuum sheaf on admissible edges)
------------------------------------------------------------------------

envSampleSectionsOnEdge :
  EnvironmentContinuumSheaf → InteractGraphEdge → Maybe EnvironmentSampleSections
envSampleSectionsOnEdge = environmentSheafOnEdge

vacuumSampleSectionOnEdge :
  EnvironmentContinuumSheaf → InteractGraphEdge → Maybe ℚ
vacuumSampleSectionOnEdge S e with envSampleSectionsOnEdge S e
... | just (v , _ , _) = just v
... | nothing = nothing

containedSampleSectionOnEdge :
  EnvironmentContinuumSheaf → InteractGraphEdge → Maybe ℚ
containedSampleSectionOnEdge S e with envSampleSectionsOnEdge S e
... | just (_ , c , _) = just c
... | nothing = nothing

messySampleSectionOnEdge :
  EnvironmentContinuumSheaf → InteractGraphEdge → Maybe ℚ
messySampleSectionOnEdge S e with envSampleSectionsOnEdge S e
... | just (_ , _ , m) = just m
... | nothing = nothing

sampleSectionOnEdge :
  EnvironmentSectionRegime → EnvironmentContinuumSheaf → InteractGraphEdge → Maybe ℚ
sampleSectionOnEdge envVacuum S e = vacuumSampleSectionOnEdge S e
sampleSectionOnEdge envContained S e = containedSampleSectionOnEdge S e
sampleSectionOnEdge envMessy S e = messySampleSectionOnEdge S e

------------------------------------------------------------------------
-- Named sections are simultaneous — not XOR regime selection
------------------------------------------------------------------------

envSampleSectionsNamedNotXor : ⊤
envSampleSectionsNamedNotXor = tt

envSampleSectionsRegimeDistinct :
  (envVacuum ≢ envContained)
  × (envVacuum ≢ envMessy)
  × (envContained ≢ envMessy)
envSampleSectionsRegimeDistinct =
  ( vacuumNotContained
  , vacuumNotMessy
  , containedNotMessy
  )

envSampleSectionsOnEdgeJust :
  ∀ (S : EnvironmentContinuumSheaf) (s : ThermodynamicState) →
  envSampleSectionsOnEdge S (s , s)
  ≡ just (vacuumSection S , containedSection S , messySection S)
envSampleSectionsOnEdgeJust S s with gate s s
... | yes prf = refl
... | no ¬prf = ⊥-elim (¬prf (admissible-refl s))
  where open import Data.Empty using (⊥-elim)

------------------------------------------------------------------------
-- Fixture sheaf: simultaneous named sample triple on one Env sheaf
------------------------------------------------------------------------

envSampleFixtureField : EnvironmentSectionField
envSampleFixtureField envVacuum = 1ℚ
envSampleFixtureField envContained = normalize 2 1
envSampleFixtureField envMessy = normalize 3 1

envSampleFixtureSheaf : EnvironmentContinuumSheaf
envSampleFixtureSheaf = record { dissipationWitness = envSampleFixtureField }

envSampleSectionsFixtureTriple :
  envSampleSectionsTriple envSampleFixtureSheaf
  ≡ (1ℚ , normalize 2 1 , normalize 3 1)
envSampleSectionsFixtureTriple = refl

envSampleSectionsFixtureWitness : ⊤
envSampleSectionsFixtureWitness = tt

------------------------------------------------------------------------
-- Honesty fence (physics_green false — not measured env pins)
------------------------------------------------------------------------

chem-env-sample-sections-physics-green : Bool
chem-env-sample-sections-physics-green = false

chem-env-sample-sections-physics-green-false :
  chem-env-sample-sections-physics-green ≡ false
chem-env-sample-sections-physics-green-false = refl

env-sample-sections-production-wired : Bool
env-sample-sections-production-wired = false

env-sample-sections-production-wired-false :
  env-sample-sections-production-wired ≡ false
env-sample-sections-production-wired-false = refl

------------------------------------------------------------------------
-- Module witness (meso acting env sample sections anchor)
------------------------------------------------------------------------

envSampleSectionsModuleWitness : ⊤
envSampleSectionsModuleWitness = tt
