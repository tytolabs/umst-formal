-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.FrugalMi — meso/acting §4 frugal MI observation.
--
-- URGE-FORMAL-MESO-AGDA-FRUGAL-MI (umst-formal acting fiber only).
-- §4: frugal MI observation of local+mesh state as acting coalgebra —
-- not Landauer proof and not UCRS Landauer-kernel fork. Compose
-- `frugal-mi-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.FrugalMi where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _+_; _-_; _≤_; _<_)
open import Data.Rational.Properties as ℚ-Props using (≤-refl; ≤-trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 1: Local+mesh state carriers (§4 acting coalgebra mirror)
------------------------------------------------------------------------

record LocalState : Set where
  field
    commit-head : ℕ
    entropy-bits : ℚ

record MeshState : Set where
  field
    replica-seq : ℕ
    gossip-entropy-bits : ℚ

record LocalMeshState : Set where
  field
    local : LocalState
    mesh : MeshState

data LocalMeshCoalgebra : Set where
  local-only : LocalState → LocalMeshCoalgebra
  mesh-only : MeshState → LocalMeshCoalgebra
  paired : LocalMeshState → LocalMeshCoalgebra

deconstruct : LocalMeshState → LocalMeshCoalgebra
deconstruct s = paired s

requires-paired : LocalMeshCoalgebra → Set
requires-paired (paired _) = ⊤
requires-paired (local-only _) = ⊥
requires-paired (mesh-only _) = ⊥

------------------------------------------------------------------------
-- SECTION 2: Pairwise MI bits — I(local; mesh) = H(local) + H(mesh) − H(joint)
------------------------------------------------------------------------

pairwise-mi-bits : ℚ → ℚ → ℚ → ℚ
pairwise-mi-bits h-local h-mesh joint = h-local + h-mesh - joint

mi-positive : ℚ → Set
mi-positive mi = 0ℚ < mi

mi-nonnegative : ℚ → Set
mi-nonnegative mi = 0ℚ ≤ mi

------------------------------------------------------------------------
-- SECTION 3: Frugal MI observation witness (acting coalgebra, not Landauer proof)
------------------------------------------------------------------------

record FrugalMiObservation : Set where
  field
    required-bits : ℚ
    observed-bits : ℚ

mi-witness-ok : FrugalMiObservation → Set
mi-witness-ok obs =
  0ℚ < FrugalMiObservation.observed-bits obs ×
  FrugalMiObservation.required-bits obs ≤ FrugalMiObservation.observed-bits obs

mi-witness-intro :
  (obs : FrugalMiObservation) →
  0ℚ < FrugalMiObservation.observed-bits obs →
  FrugalMiObservation.required-bits obs ≤ FrugalMiObservation.observed-bits obs →
  mi-witness-ok obs
mi-witness-intro obs hp hpaid = hp , hpaid

------------------------------------------------------------------------
-- SECTION 4: Excitement select hook (compose — no second ℚ argmin)
------------------------------------------------------------------------

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record observation-candidate : Set where
  field
    cand-id : ℕ
    cand-mi-bits : ℚ
    paired-ok : Bool

frugal-mi-excitement-select :
  (src : ℚ) → List observation-candidate →
  observation-candidate ⊎ excitement-residue
frugal-mi-excitement-select src List.[] = inj₂ exc-no-candidates
frugal-mi-excitement-select src (c List.∷ _) = inj₁ c

urge-frugal-mi-select :
  (src : ℚ) → List observation-candidate →
  observation-candidate ⊎ excitement-residue
urge-frugal-mi-select = frugal-mi-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

------------------------------------------------------------------------
-- SECTION 5: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data FrugalMiRefusal : Set where
  landauer-proof-theater : FrugalMiRefusal
  landauer-kernel-fork : FrugalMiRefusal
  mutual-information-zero : FrugalMiRefusal
  mesh-absent-when-paired-required : FrugalMiRefusal
  inconsistent-entropies : FrugalMiRefusal
  witness-deficit : FrugalMiRefusal
  second-argmin : FrugalMiRefusal

data FrugalMiOutcome : Set where
  observed : FrugalMiObservation → FrugalMiOutcome
  refused : FrugalMiRefusal → FrugalMiOutcome

refuse-landauer-proof : FrugalMiRefusal
refuse-landauer-proof = landauer-proof-theater

refuse-landauer-kernel-fork : FrugalMiRefusal
refuse-landauer-kernel-fork = landauer-kernel-fork

refuse-mutual-information-zero : FrugalMiRefusal
refuse-mutual-information-zero = mutual-information-zero

refuse-mesh-absent : FrugalMiRefusal
refuse-mesh-absent = mesh-absent-when-paired-required

refuse-inconsistent-entropies : FrugalMiRefusal
refuse-inconsistent-entropies = inconsistent-entropies

refuse-witness-deficit : FrugalMiRefusal
refuse-witness-deficit = witness-deficit

refuse-second-argmin : FrugalMiRefusal
refuse-second-argmin = second-argmin

------------------------------------------------------------------------
-- SECTION 6: Gate frugal MI observation (§4 acting coalgebra path)
------------------------------------------------------------------------

gate-observe-frugal-mi-admit :
  (obs : FrugalMiObservation) →
  mi-witness-ok obs →
  FrugalMiOutcome
gate-observe-frugal-mi-admit obs _ = observed obs

gate-observe-frugal-mi-refuse-unpaid :
  (obs : FrugalMiObservation) →
  ¬ mi-witness-ok obs →
  FrugalMiRefusal
gate-observe-frugal-mi-refuse-unpaid obs _ = witness-deficit

gate-observe-frugal-mi-refuse-mesh-absent :
  (coal : LocalMeshCoalgebra) →
  ¬ requires-paired coal →
  FrugalMiRefusal
gate-observe-frugal-mi-refuse-mesh-absent coal _ = mesh-absent-when-paired-required

gate-observe-frugal-mi-refuse-mi-zero :
  (mi : ℚ) →
  ¬ mi-positive mi →
  FrugalMiRefusal
gate-observe-frugal-mi-refuse-mi-zero mi _ = mutual-information-zero

classify-frugal-mi :
  (coal : LocalMeshCoalgebra) →
  (mi : ℚ) →
  mi-positive mi →
  (obs : FrugalMiObservation) →
  mi-witness-ok obs →
  FrugalMiOutcome
classify-frugal-mi (paired s) mi hmi obs hobs =
  gate-observe-frugal-mi-admit obs hobs
classify-frugal-mi (local-only _) mi hmi obs hobs =
  refused mesh-absent-when-paired-required
classify-frugal-mi (mesh-only _) mi hmi obs hobs =
  refused mesh-absent-when-paired-required

------------------------------------------------------------------------
-- SECTION 7: History bridge + Landauer cite (observation ≠ Landauer proof)
------------------------------------------------------------------------

record HistoryTransition : Set where
  field
    bath : HeatBath
    dissipated-entropy : ℚ
    entropy-drop : ℚ

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

admitSecondLaw-from-landauer :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
  PhysicalSecondLaw proc entropyDecrease →
  ∀ (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
admitSecondLaw-from-landauer proc ΔS hSL t hent hdiss =
  let step1 : HistoryTransition.entropy-drop t ≤ ErasureProcess.dissipatedEntropy proc
      step1 = subst (λ d → d ≤ ErasureProcess.dissipatedEntropy proc) (sym hent) hSL
  in subst (λ d → HistoryTransition.entropy-drop t ≤ d) (sym hdiss) step1

frugal-mi-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
frugal-mi-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 8: Honesty flags (zero new postulates)
------------------------------------------------------------------------

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

frugal-mi-production-wired : Bool
frugal-mi-production-wired = false

frugal-mi-production-wired-false :
  frugal-mi-production-wired ≡ false
frugal-mi-production-wired-false = refl

frugal-mi-marker : ℕ
frugal-mi-marker = 1

frugal-mi-marker-eq : frugal-mi-marker ≡ 1
frugal-mi-marker-eq = refl

frugal-mi-module-witness : ⊤
frugal-mi-module-witness = tt

landauer-proof-refused :
  refuse-landauer-proof ≡ landauer-proof-theater
landauer-proof-refused = refl

landauer-kernel-fork-refused :
  refuse-landauer-kernel-fork ≡ landauer-kernel-fork
landauer-kernel-fork-refused = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

urge-frugal-mi-select-eq-excitement :
  ∀ (src : ℚ) (cs : List observation-candidate) →
  urge-frugal-mi-select src cs ≡ frugal-mi-excitement-select src cs
urge-frugal-mi-select-eq-excitement src cs = refl

deconstruct-eq-paired :
  ∀ (s : LocalMeshState) → deconstruct s ≡ paired s
deconstruct-eq-paired s = refl
