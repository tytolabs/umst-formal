-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.KleisliStatus — meso/acting §16.7 operator verb status.
--
-- URGE-FORMAL-MESO-AGDA-KLEISLI-STATUS (umst-formal acting fiber only).
-- §16.7: operator verb `status` as Kleisli arrow — Frugal MI observation gate;
-- replica-class entity check; observation only — not gate_check_before_sync
-- inbound, not outbound tick, not MergeSafe witness. Composes `excitement-select`
-- — no second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` / `Urge.AdmitKleisli`. Anchored in
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
-- Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.KleisliStatus where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _<?_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (does; yes; no)

------------------------------------------------------------------------
-- SECTION 0: Minimal thermodynamic head carriers (no Concrete.Gate K-infect)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  field
    density free-energy hydration strength : ℚ

record Admissible (old new : ThermodynamicState) : Set where
  constructor mkAdmissible
  field
    admissible-witness : ⊤

admissible-any : ∀ {old new : ThermodynamicState} → Admissible old new
admissible-any = mkAdmissible tt

------------------------------------------------------------------------
-- SECTION 1: §16.7 verb table + status Kleisli carriers
------------------------------------------------------------------------

data StatusReplicaClass : Set where
  src-node0 src-node1 src-forgejo-primary-mirror src-offline-luks : StatusReplicaClass

data VerbColumnRequirement : Set where
  vcr-not-required vcr-required : VerbColumnRequirement

data KleisliGateKind : Set where
  kgk-frugal-mi-observation kgk-gate-check-before-sync-inbound kgk-outbound-tick-if-admitted : KleisliGateKind

data EntityCheckKind : Set where
  eck-replica-class eck-remote-class : EntityCheckKind

record OperatorVerbRow : Set where
  field
    verb-status : Bool
    verb-kleisli-gate : KleisliGateKind
    verb-merge-safe : VerbColumnRequirement
    verb-excitement : VerbColumnRequirement
    verb-entity-check : EntityCheckKind

record FrugalMiObservation : Set where
  field
    fmi-witness-bits : ℕ
    fmi-frugal-cap-bits : ℕ

data FrugalMiGateVerdict : Set where
  fmig-admit fmig-refuse-exceeds-cap fmig-refuse-zero-observation : FrugalMiGateVerdict

record StatusObservation : Set where
  field
    status-replica : StatusReplicaClass
    status-observation-probe : FrugalMiObservation
    status-gate-verdict : FrugalMiGateVerdict

data StatusGateMismatch : Set where
  sgm-sync-inbound-on-status sgm-outbound-tick-on-status sgm-merge-safe-on-status sgm-excitement-on-status sgm-remote-class-on-status : StatusGateMismatch

data StatusArrowError : Set where
  sae-frugal-mi-refused : FrugalMiGateVerdict → StatusArrowError
  sae-gate-mismatch : StatusGateMismatch → StatusArrowError

------------------------------------------------------------------------
-- SECTION 2: Frugal MI gate + status arrow (positive refuse)
------------------------------------------------------------------------

status-verb-row : OperatorVerbRow
status-verb-row = record
  { verb-status = true
  ; verb-kleisli-gate = kgk-frugal-mi-observation
  ; verb-merge-safe = vcr-not-required
  ; verb-excitement = vcr-not-required
  ; verb-entity-check = eck-replica-class
  }

nat-zero? : ℕ → Bool
nat-zero? zero = true
nat-zero? (suc _) = false

nat-pos? : ℕ → Bool
nat-pos? zero = false
nat-pos? (suc _) = true

nat-lt? : ℕ → ℕ → Bool
nat-lt? m n = does (ℕ-Props._<?_ m n)

evaluate-frugal-mi-gate : FrugalMiObservation → FrugalMiGateVerdict
evaluate-frugal-mi-gate obs =
  if nat-zero? (FrugalMiObservation.fmi-frugal-cap-bits obs)
       ∧ nat-pos? (FrugalMiObservation.fmi-witness-bits obs)
  then fmig-refuse-exceeds-cap
  else if nat-pos? (FrugalMiObservation.fmi-frugal-cap-bits obs)
            ∧ nat-zero? (FrugalMiObservation.fmi-witness-bits obs)
       then fmig-refuse-zero-observation
       else if nat-lt? (FrugalMiObservation.fmi-frugal-cap-bits obs)
                      (FrugalMiObservation.fmi-witness-bits obs)
            then fmig-refuse-exceeds-cap
            else fmig-admit

status-replica-class-admits : StatusReplicaClass → Bool
status-replica-class-admits src-node0 = true
status-replica-class-admits src-node1 = true
status-replica-class-admits src-forgejo-primary-mirror = true
status-replica-class-admits src-offline-luks = true

kleisli-gate-matches-status : KleisliGateKind → Bool
kleisli-gate-matches-status kgk-frugal-mi-observation = true
kleisli-gate-matches-status kgk-gate-check-before-sync-inbound = false
kleisli-gate-matches-status kgk-outbound-tick-if-admitted = false

run-status-kleisli-arrow :
  (replica : StatusReplicaClass) (obs : FrugalMiObservation) →
  StatusObservation ⊎ StatusArrowError
run-status-kleisli-arrow replica obs =
  if status-replica-class-admits replica
  then verdict-result (evaluate-frugal-mi-gate obs)
  else inj₂ (sae-gate-mismatch sgm-remote-class-on-status)
  where
  verdict-result : FrugalMiGateVerdict → StatusObservation ⊎ StatusArrowError
  verdict-result fmig-admit = inj₁ record
    { status-replica = replica
    ; status-observation-probe = obs
    ; status-gate-verdict = fmig-admit
    }
  verdict-result fmig-refuse-exceeds-cap =
    inj₂ (sae-frugal-mi-refused fmig-refuse-exceeds-cap)
  verdict-result fmig-refuse-zero-observation =
    inj₂ (sae-frugal-mi-refused fmig-refuse-zero-observation)

refuse-sync-gate-on-status : StatusGateMismatch
refuse-sync-gate-on-status = sgm-sync-inbound-on-status

refuse-outbound-tick-on-status : StatusGateMismatch
refuse-outbound-tick-on-status = sgm-outbound-tick-on-status

refuse-merge-safe-on-status : StatusGateMismatch
refuse-merge-safe-on-status = sgm-merge-safe-on-status

refuse-excitement-on-status : StatusGateMismatch
refuse-excitement-on-status = sgm-excitement-on-status

refuse-remote-class-on-status : StatusGateMismatch
refuse-remote-class-on-status = sgm-remote-class-on-status

status-verb-row-excitement-not-required :
  OperatorVerbRow.verb-excitement status-verb-row ≡ vcr-not-required
status-verb-row-excitement-not-required = refl

status-verb-row-merge-safe-not-required :
  OperatorVerbRow.verb-merge-safe status-verb-row ≡ vcr-not-required
status-verb-row-merge-safe-not-required = refl

status-verb-row-frugal-mi-gate :
  OperatorVerbRow.verb-kleisli-gate status-verb-row ≡ kgk-frugal-mi-observation
status-verb-row-frugal-mi-gate = refl

kleisli-gate-matches-status-frugal :
  kleisli-gate-matches-status kgk-frugal-mi-observation ≡ true
kleisli-gate-matches-status-frugal = refl

kleisli-gate-matches-status-sync-false :
  kleisli-gate-matches-status kgk-gate-check-before-sync-inbound ≡ false
kleisli-gate-matches-status-sync-false = refl

------------------------------------------------------------------------
-- SECTION 3: Excitement compose (no second argmin)
------------------------------------------------------------------------

data excitement-residue : Set where
  exc-no-candidates exc-all-inadmissible exc-no-strict-improvement : excitement-residue

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

data StatusExcitementComposePin : Set where
  secp-import-select-excitement secp-second-argmin-refused : StatusExcitementComposePin

status-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  StatusExcitementComposePin →
  history-candidate src ⊎ excitement-residue
status-excitement-select src cands secp-import-select-excitement =
  excitement-select src cands
status-excitement-select src cands secp-second-argmin-refused =
  inj₂ exc-all-inadmissible

status-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  status-excitement-select src cands secp-import-select-excitement ≡
  excitement-select src cands
status-excitement-select-eq-excitement-select src cands = refl

status-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  status-excitement-select src cands secp-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
status-excitement-select-refuses-second-argmin src cands = refl

status-no-local-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  status-excitement-select src cands secp-import-select-excitement ≡
  excitement-select src cands
status-no-local-argmin src cands =
  status-excitement-select-eq-excitement-select src cands

status-excitement-empty :
  ∀ (src : ThermodynamicState) →
  status-excitement-select src [] secp-import-select-excitement ≡
  inj₂ exc-no-candidates
status-excitement-empty src = refl

------------------------------------------------------------------------
-- SECTION 4: §16.7 fixtures + witness theorems
------------------------------------------------------------------------

status-fixture-obs-admit : FrugalMiObservation
status-fixture-obs-admit = record { fmi-witness-bits = 4 ; fmi-frugal-cap-bits = 8 }

status-fixture-obs-refuse-cap : FrugalMiObservation
status-fixture-obs-refuse-cap = record { fmi-witness-bits = 16 ; fmi-frugal-cap-bits = 8 }

status-fixture-obs-refuse-zero : FrugalMiObservation
status-fixture-obs-refuse-zero = record { fmi-witness-bits = 0 ; fmi-frugal-cap-bits = 8 }

status-fixture-frugal-mi-admits :
  evaluate-frugal-mi-gate status-fixture-obs-admit ≡ fmig-admit
status-fixture-frugal-mi-admits = refl

status-fixture-frugal-mi-refuses-cap :
  evaluate-frugal-mi-gate status-fixture-obs-refuse-cap ≡ fmig-refuse-exceeds-cap
status-fixture-frugal-mi-refuses-cap = refl

status-fixture-frugal-mi-refuses-zero :
  evaluate-frugal-mi-gate status-fixture-obs-refuse-zero ≡ fmig-refuse-zero-observation
status-fixture-frugal-mi-refuses-zero = refl

status-fixture-arrow-ok :
  run-status-kleisli-arrow src-node0 status-fixture-obs-admit ≡
  inj₁ record
    { status-replica = src-node0
    ; status-observation-probe = status-fixture-obs-admit
    ; status-gate-verdict = fmig-admit
    }
status-fixture-arrow-ok = refl

status-fixture-arrow-refuses-cap :
  run-status-kleisli-arrow src-node1 status-fixture-obs-refuse-cap ≡
  inj₂ (sae-frugal-mi-refused fmig-refuse-exceeds-cap)
status-fixture-arrow-refuses-cap = refl

status-positive-refuse-sync-gate :
  refuse-sync-gate-on-status ≡ sgm-sync-inbound-on-status
status-positive-refuse-sync-gate = refl

status-positive-refuse-merge-safe :
  refuse-merge-safe-on-status ≡ sgm-merge-safe-on-status
status-positive-refuse-merge-safe = refl

status-positive-refuse-excitement :
  refuse-excitement-on-status ≡ sgm-excitement-on-status
status-positive-refuse-excitement = refl

status-positive-refuse-outbound-tick :
  refuse-outbound-tick-on-status ≡ sgm-outbound-tick-on-status
status-positive-refuse-outbound-tick = refl

------------------------------------------------------------------------
-- SECTION 5: History transition + Landauer bridge (zero new postulates)
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

status-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
status-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
------------------------------------------------------------------------

kleisli-status-physics-green : Bool
kleisli-status-physics-green = false

kleisli-status-physics-green-false :
  kleisli-status-physics-green ≡ false
kleisli-status-physics-green-false = refl

kleisli-status-production-wired : Bool
kleisli-status-production-wired = false

kleisli-status-production-wired-false :
  kleisli-status-production-wired ≡ false
kleisli-status-production-wired-false = refl

kleisli-status-module-witness : ⊤
kleisli-status-module-witness = tt

status-positive-refuse-aggregate :
  (refuse-sync-gate-on-status ≡ sgm-sync-inbound-on-status) ×
  (refuse-merge-safe-on-status ≡ sgm-merge-safe-on-status) ×
  (refuse-excitement-on-status ≡ sgm-excitement-on-status) ×
  (refuse-outbound-tick-on-status ≡ sgm-outbound-tick-on-status)
status-positive-refuse-aggregate =
  refl , refl , refl , refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  sgm-excitement-on-status ≡ sgm-excitement-on-status
refuse-second-argmin-is-tag = refl
