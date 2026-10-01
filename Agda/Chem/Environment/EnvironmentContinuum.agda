-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem.Environment.EnvironmentContinuum — meso/acting env sheaf.
--
-- CHEM-L0-FORMAL-01 / CHEM-NS-W0-AXIOM (umst-formal acting fiber only).
-- Environment continuum as Interact-graph sheaf sections vacuum | contained |
-- messy — named *sections*, not XOR regime pick.  Anchored in sole
-- `Chem.Conservation` mass ball only;
--
------------------------------------------------------------------------


module Chem.Environment.EnvironmentContinuum where
open import Chem.Conservation
open import Concrete.Gate
open Concrete.Gate using
  ( ThermodynamicState
  ; Admissible
  ; gate
  ; concrete-thermodynamic-system
  ; MassCond
  ; DissipCond
  )
open ThermodynamicState
open Admissible
open import Core.Gate using (CoreAdmissible)
open import Data.Bool using (Bool; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; _≤_; _-_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- SECTION 1: Environment continuum carrier (vacuum | contained | messy)
------------------------------------------------------------------------

data EnvironmentVertex : Set where
  envVacuum    : EnvironmentVertex
  envContained : EnvironmentVertex
  envMessy     : EnvironmentVertex

EnvironmentSectionField : Set
EnvironmentSectionField = EnvironmentVertex → ℚ

record EnvironmentContinuumSheaf : Set where
  field
    dissipationWitness : EnvironmentSectionField

open EnvironmentContinuumSheaf

------------------------------------------------------------------------
-- Named sections (simultaneous accessors — not XOR regime selection)
------------------------------------------------------------------------

vacuumSection : EnvironmentContinuumSheaf → ℚ
vacuumSection S = dissipationWitness S envVacuum

containedSection : EnvironmentContinuumSheaf → ℚ
containedSection S = dissipationWitness S envContained

messySection : EnvironmentContinuumSheaf → ℚ
messySection S = dissipationWitness S envMessy

sectionsSimultaneous :
  ∀ S →
  (vacuumSection S , containedSection S , messySection S)
  ≡ ( dissipationWitness S envVacuum
    , dissipationWitness S envContained
    , dissipationWitness S envMessy
    )
sectionsSimultaneous S = refl

------------------------------------------------------------------------
-- Surroundings morphism tags (named per vertex — not XOR)
------------------------------------------------------------------------

data SurroundingsMorphismTag : Set where
  tagVacuumUnit        : SurroundingsMorphismTag
  tagContainedInteract : SurroundingsMorphismTag
  tagMessyOreRefine    : SurroundingsMorphismTag

surroundingsTag : EnvironmentVertex → SurroundingsMorphismTag
surroundingsTag envVacuum = tagVacuumUnit
surroundingsTag envContained = tagContainedInteract
surroundingsTag envMessy = tagMessyOreRefine

vacuumNotContained : envVacuum ≢ envContained
vacuumNotContained ()

vacuumNotMessy : envVacuum ≢ envMessy
vacuumNotMessy ()

containedNotMessy : envContained ≢ envMessy
containedNotMessy ()

environmentVertexCardinality :
  ∀ v → v ≡ envVacuum ⊎ v ≡ envContained ⊎ v ≡ envMessy
environmentVertexCardinality envVacuum = inj₁ refl
environmentVertexCardinality envContained = inj₂ (inj₁ refl)
environmentVertexCardinality envMessy = inj₂ (inj₂ refl)

------------------------------------------------------------------------
-- SECTION 2: Interact-graph edge carrier
------------------------------------------------------------------------

InteractGraphEdge : Set
InteractGraphEdge = ThermodynamicState × ThermodynamicState

------------------------------------------------------------------------
-- SECTION 3: Conservation bridge (mass ball — zero new postulates)
------------------------------------------------------------------------

concreteCoreAdmissible :
  ∀ (old new : ThermodynamicState) → Admissible old new →
  CoreAdmissible concrete-thermodynamic-system old new
concreteCoreAdmissible old new adm = record
  { mass-conserved = mass-conserved adm
  ; dissipation-nonneg = dissipation-nonneg adm
  }

chemMassFromAdmissible :
  ∀ (old new : ThermodynamicState) → Admissible old new →
  ChemMassCond concrete-thermodynamic-system old new
chemMassFromAdmissible old new adm =
  mass-from-core-admissible
    concrete-thermodynamic-system old new
    (concreteCoreAdmissible old new adm)

chemDissipFromAdmissible :
  ∀ (old new : ThermodynamicState) → Admissible old new →
  ChemDissipCond concrete-thermodynamic-system old new
chemDissipFromAdmissible old new adm =
  dissip-from-core-admissible
    concrete-thermodynamic-system old new
    (concreteCoreAdmissible old new adm)

massCondFromAdmissible :
  ∀ (old new : ThermodynamicState) → Admissible old new → MassCond old new
massCondFromAdmissible old new adm = mass-conserved adm

dissipCondFromAdmissible :
  ∀ (old new : ThermodynamicState) → Admissible old new → DissipCond old new
dissipCondFromAdmissible old new adm = dissipation-nonneg adm

------------------------------------------------------------------------
-- SECTION 5: Environment sheaf on admissible edges (all sections named)
------------------------------------------------------------------------

environmentSheafOnEdge :
  EnvironmentContinuumSheaf → InteractGraphEdge → Maybe (ℚ × ℚ × ℚ)
environmentSheafOnEdge S (old , new) with gate old new
... | yes prf = just (vacuumSection S , containedSection S , messySection S)
... | no ¬prf = nothing

------------------------------------------------------------------------
------------------------------------------------------------------------

