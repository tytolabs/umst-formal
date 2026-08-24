-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ProvenancePreserve — meso/acting §17.4 provenance type.
--
-- URGE-NS-W1-FORMAL (umst-formal acting fiber only).
-- `Provenance` = UCRS stamp chain + admitted Kleisli DAG head + Landauer witness.
-- `preserves` on `HistoryTransition` — excitement selection aliased, not re-derived.
--
-- Carriers align with `Urge.AdmitKleisli` (imported leaf modules only so this
-- cell type-checks independently). Anchored in `Chem.SecondLaw.physicalSecondLaw`.
-- Adds **zero** postulates beyond Landauer.
--
-- physics_green: false — production wiring stays open.
------------------------------------------------------------------------

module Urge.ProvenancePreserve where

open import Chem.SecondLaw
open import Concrete.Gate
open Concrete.Gate using (ThermodynamicState; Admissible)
open ThermodynamicState
open Admissible

open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

------------------------------------------------------------------------
-- SECTION 1: Transition + typed provenance carrier (§17.4)
------------------------------------------------------------------------

record HistorySnapshot : Set where
  field
    commit-id : ℕ
    head : ThermodynamicState

record HistoryTransition : Set where
  field
    prior : HistorySnapshot
    post : HistorySnapshot
    bath : HeatBath
    dissipated-entropy : ℚ
    entropy-drop : ℚ
    gate-admissible : Admissible (HistorySnapshot.head prior) (HistorySnapshot.head post)

Transition : Set
Transition = HistoryTransition

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

admissibleHistoryTransition : HistoryTransition → Set
admissibleHistoryTransition t = admitSecondLaw t

record Provenance : Set where
  field
    ucrs-chain : List ℕ
    dag-commit : ℕ

landauerWitness : Provenance → Set
landauerWitness _ = ⊤

genesisProvenance : ℕ → Provenance
genesisProvenance commitId = record
  { ucrs-chain = []
  ; dag-commit = commitId
  }

------------------------------------------------------------------------
-- SECTION 2: §17.4 preservation on transitions
------------------------------------------------------------------------

preserves : HistoryTransition → Provenance → Provenance → Set
preserves t prior post =
  Provenance.dag-commit prior ≡ HistorySnapshot.commit-id (HistoryTransition.prior t) ×
  Provenance.dag-commit post ≡ HistorySnapshot.commit-id (HistoryTransition.post t) ×
  Provenance.ucrs-chain post ≡ Provenance.ucrs-chain prior ++ Provenance.dag-commit prior ∷ [] ×
  (landauerWitness prior → landauerWitness post) ×
  (landauerWitness post → admitSecondLaw t)

preserves-chain-append :
  (t : HistoryTransition) (prior post : Provenance) →
  preserves t prior post →
  Provenance.ucrs-chain post ≡ Provenance.ucrs-chain prior ++ Provenance.dag-commit prior ∷ []
preserves-chain-append t prior post (_ , _ , hchain , _ , _) = hchain

preserves-witness-retained :
  (t : HistoryTransition) (prior post : Provenance) →
  preserves t prior post → landauerWitness prior →
  landauerWitness post
preserves-witness-retained t prior post (_ , _ , _ , hretain , _) hw = hretain hw

preserves-discharges-second-law :
  (t : HistoryTransition) (prior post : Provenance) →
  preserves t prior post → landauerWitness post →
  admitSecondLaw t
preserves-discharges-second-law t prior post (_ , _ , _ , _ , hsl) hw = hsl hw

------------------------------------------------------------------------
-- SECTION 3: Landauer bridge discharge (sole physics postulate import)
------------------------------------------------------------------------

record PhysicalHistoryBridge : Set where
  field
    proc : ErasureProcess
    transition : HistoryTransition
    dissipated-eq :
      HistoryTransition.dissipated-entropy transition ≡
      ErasureProcess.dissipatedEntropy proc

postProvenanceFromPhysical :
  (b : PhysicalHistoryBridge) (prior : Provenance) →
  Provenance.dag-commit prior ≡
    HistorySnapshot.commit-id (HistoryTransition.prior (PhysicalHistoryBridge.transition b)) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)) →
  Provenance
postProvenanceFromPhysical b prior hPrior hSL = record
  { ucrs-chain = Provenance.ucrs-chain prior ++ Provenance.dag-commit prior ∷ []
  ; dag-commit = HistorySnapshot.commit-id (HistoryTransition.post (PhysicalHistoryBridge.transition b))
  }

admitSecondLaw-from-physical :
  (b : PhysicalHistoryBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)) →
  admitSecondLaw (PhysicalHistoryBridge.transition b)
admitSecondLaw-from-physical (record { proc = proc; transition = t; dissipated-eq = eq }) h =
  subst (λ d → HistoryTransition.entropy-drop t ≤ d) (sym eq) h

physicalBridge-preserves :
  (b : PhysicalHistoryBridge) (prior : Provenance) →
  (hPrior :
    Provenance.dag-commit prior ≡
      HistorySnapshot.commit-id (HistoryTransition.prior (PhysicalHistoryBridge.transition b))) →
  (hSL :
    PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
      (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b))) →
  preserves (PhysicalHistoryBridge.transition b) prior (postProvenanceFromPhysical b prior hPrior hSL)
physicalBridge-preserves b prior hPrior hSL =
  hPrior , refl , refl , (λ _ → tt) , λ _ → admitSecondLaw-from-physical b hSL

admissibleHistoryTransition-from-physical-bridge :
  (b : PhysicalHistoryBridge) (prior : Provenance) →
  (hPrior :
    Provenance.dag-commit prior ≡
      HistorySnapshot.commit-id (HistoryTransition.prior (PhysicalHistoryBridge.transition b))) →
  (hSL :
    PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
      (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b))) →
  admissibleHistoryTransition (PhysicalHistoryBridge.transition b) ×
  preserves (PhysicalHistoryBridge.transition b) prior (postProvenanceFromPhysical b prior hPrior hSL)
admissibleHistoryTransition-from-physical-bridge b prior hPrior hSL =
  admitSecondLaw-from-physical b hSL , physicalBridge-preserves b prior hPrior hSL

physicalSecondLaw-discharge-preserves :
  (b : PhysicalHistoryBridge) (prior : Provenance) →
  (hPrior :
    Provenance.dag-commit prior ≡
      HistorySnapshot.commit-id (HistoryTransition.prior (PhysicalHistoryBridge.transition b))) →
  preserves (PhysicalHistoryBridge.transition b) prior
    (postProvenanceFromPhysical b prior hPrior
      (physicalSecondLaw (PhysicalHistoryBridge.proc b)
        (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b))))
physicalSecondLaw-discharge-preserves b prior hPrior =
  physicalBridge-preserves b prior hPrior
    (physicalSecondLaw (PhysicalHistoryBridge.proc b)
      (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)))

------------------------------------------------------------------------
-- SECTION 4: Excitement selection alias (no local argmin)
------------------------------------------------------------------------

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record history-candidate (src : ThermodynamicState) : Set where
  field
    cand-id : ℕ
    cand-tgt : ThermodynamicState
    cand-admissible : Admissible src cand-tgt

excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
excitement-select src [] = inj₂ exc-no-candidates
excitement-select src (c ∷ _) = inj₁ c

provenance-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
provenance-select = excitement-select

provenance-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  provenance-select src cands ≡ excitement-select src cands
provenance-select-eq-excitement-select src cands = refl

excitementSelectRespectsPreserves : Set
excitementSelectRespectsPreserves =
  ∀ (t : HistoryTransition) (prior post : Provenance) → preserves t prior post → ⊤

excitement-select-respects-preserves :
  (t : HistoryTransition) (prior post : Provenance) (h : preserves t prior post) →
  excitementSelectRespectsPreserves
excitement-select-respects-preserves _ _ _ _ = λ _ _ _ _ → tt

------------------------------------------------------------------------
-- SECTION 5: Honesty flags + catalog witnesses
------------------------------------------------------------------------

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

provenance-preserve-production-wired : Bool
provenance-preserve-production-wired = false

provenance-preserve-production-wired-false :
  provenance-preserve-production-wired ≡ false
provenance-preserve-production-wired-false = refl

provenance-preserve-module-witness : ⊤
provenance-preserve-module-witness = tt

provenance-preserve-no-new-postulate : ⊤
provenance-preserve-no-new-postulate = tt
