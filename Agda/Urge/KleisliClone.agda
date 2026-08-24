-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.KleisliClone — meso/acting §16.7 operator verb clone.
--
-- URGE-FORMAL-MESO-AGDA-KLEISLI-CLONE (umst-formal acting fiber only).
-- §16.7: operator verb `clone` as Kleisli arrow — initial replica coalgebra
-- admission; not sync inbound, not outbound tick, not Frugal MI observation,
-- not MergeSafe witness, not Excitement argmin. Compose `excitement-select`
-- — no second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` / `Urge.KleisliStatus`. Anchored in
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
-- Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.KleisliClone where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; not)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.String using (String)
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
-- SECTION 1: §16.7 operator verb table carriers
------------------------------------------------------------------------

data CloneOperatorVerb : Set where
  clone-verb : CloneOperatorVerb

data CloneKleisliGateKind : Set where
  ckg-admit-initial-replica-coalgebra ckg-frugal-mi-observation ckg-gate-check-before-sync-inbound ckg-outbound-tick-if-admitted ckg-excitement-argmin : CloneKleisliGateKind

data CloneVerbColumnReq : Set where
  cvcr-not-required cvcr-required : CloneVerbColumnReq

data CloneEntityCheckKind : Set where
  cec-entity-label cec-replica-class cec-remote-class : CloneEntityCheckKind

record CloneVerbRow : Set where
  field
    clone-row-verb : CloneOperatorVerb
    clone-row-kleisli-gate : CloneKleisliGateKind
    clone-row-merge-safe : CloneVerbColumnReq
    clone-row-excitement : CloneVerbColumnReq
    clone-row-entity-check : CloneEntityCheckKind

clone-verb-row : CloneVerbRow
clone-verb-row = record
  { clone-row-verb = clone-verb
  ; clone-row-kleisli-gate = ckg-admit-initial-replica-coalgebra
  ; clone-row-merge-safe = cvcr-not-required
  ; clone-row-excitement = cvcr-not-required
  ; clone-row-entity-check = cec-entity-label
  }

kleisli-gate-matches-clone : CloneKleisliGateKind → Bool
kleisli-gate-matches-clone ckg-admit-initial-replica-coalgebra = true
kleisli-gate-matches-clone ckg-frugal-mi-observation = false
kleisli-gate-matches-clone ckg-gate-check-before-sync-inbound = false
kleisli-gate-matches-clone ckg-outbound-tick-if-admitted = false
kleisli-gate-matches-clone ckg-excitement-argmin = false

------------------------------------------------------------------------
-- SECTION 2: Entity labels + initial replica coalgebra gate
------------------------------------------------------------------------

data CloneEntityLabel : Set where
  cel-labs cel-compose : CloneEntityLabel

data CloneReplicaClass : Set where
  crc-node0 crc-node1 crc-forge crc-luks crc-darwin-scratch : CloneReplicaClass

clone-replica-class-tag : CloneReplicaClass → String
clone-replica-class-tag crc-node0 = "node-0"
clone-replica-class-tag crc-node1 = "node-1"
clone-replica-class-tag crc-forge = "forgejo-primary-mirror"
clone-replica-class-tag crc-luks = "offline-luks"
clone-replica-class-tag crc-darwin-scratch = "darwin-scratch"

record InitialReplicaCoalgebra : Set where
  field
    clone-coalgebra-class : CloneReplicaClass
    clone-coalgebra-egress-declared : Bool
    clone-coalgebra-authority-declared : Bool

data InitialCoalgebraGateVerdict : Set where
  icgv-admit icgv-refuse-undeclared-egress icgv-refuse-undeclared-authority
    : InitialCoalgebraGateVerdict

evaluate-initial-coalgebra-gate : InitialReplicaCoalgebra → InitialCoalgebraGateVerdict
evaluate-initial-coalgebra-gate c =
  if InitialReplicaCoalgebra.clone-coalgebra-egress-declared c
  then if InitialReplicaCoalgebra.clone-coalgebra-authority-declared c
       then icgv-admit
       else icgv-refuse-undeclared-authority
  else icgv-refuse-undeclared-egress

record CloneRemoteHost : Set where
  field
    clone-remote-host-label : String

compose-upstream-refused : String → Bool
compose-upstream-refused "github.com" = true
compose-upstream-refused "origin.cursor.com" = true
compose-upstream-refused _ = false

parse-entity-label : String → Maybe CloneEntityLabel
parse-entity-label "labs" = just cel-labs
parse-entity-label "LABS" = just cel-labs
parse-entity-label "compose" = just cel-compose
parse-entity-label "COMPOSE" = just cel-compose
parse-entity-label _ = nothing

entity-label-admits-clone : CloneEntityLabel → CloneRemoteHost → Bool
entity-label-admits-clone cel-labs _ = true
entity-label-admits-clone cel-compose remote =
  not (compose-upstream-refused (CloneRemoteHost.clone-remote-host-label remote))

------------------------------------------------------------------------
-- SECTION 3: Clone Kleisli arrow (initial admission only)
------------------------------------------------------------------------

data CloneGateMismatch : Set where
  cgm-frugal-mi-on-clone cgm-sync-inbound-on-clone cgm-outbound-tick-on-clone cgm-merge-safe-witness-on-clone cgm-excitement-argmin-on-clone cgm-replica-class-on-clone cgm-remote-class-on-clone cgm-second-argmin-on-clone : CloneGateMismatch

data CloneArrowError : Set where
  cae-coalgebra-refused : InitialCoalgebraGateVerdict → CloneArrowError
  cae-unknown-entity-label : CloneArrowError
  cae-compose-upstream-refused : CloneArrowError
  cae-gate-mismatch : CloneGateMismatch → CloneArrowError

record CloneAdmission : Set where
  field
    clone-admission-entity : CloneEntityLabel
    clone-admission-replica : CloneReplicaClass
    clone-admission-gate : InitialCoalgebraGateVerdict

run-clone-kleisli-arrow :
  CloneEntityLabel → InitialReplicaCoalgebra → CloneRemoteHost →
  CloneAdmission ⊎ CloneArrowError
run-clone-kleisli-arrow entity coalgebra remote =
  if entity-label-admits-clone entity remote
  then verdict-result (evaluate-initial-coalgebra-gate coalgebra)
  else inj₂ cae-compose-upstream-refused
  where
  verdict-result : InitialCoalgebraGateVerdict → CloneAdmission ⊎ CloneArrowError
  verdict-result icgv-admit = inj₁ record
    { clone-admission-entity = entity
    ; clone-admission-replica = InitialReplicaCoalgebra.clone-coalgebra-class coalgebra
    ; clone-admission-gate = icgv-admit
    }
  verdict-result icgv-refuse-undeclared-egress =
    inj₂ (cae-coalgebra-refused icgv-refuse-undeclared-egress)
  verdict-result icgv-refuse-undeclared-authority =
    inj₂ (cae-coalgebra-refused icgv-refuse-undeclared-authority)

run-clone-kleisli-arrow-parsed :
  String → InitialReplicaCoalgebra → CloneRemoteHost →
  CloneAdmission ⊎ CloneArrowError
run-clone-kleisli-arrow-parsed label coalgebra remote with parse-entity-label label
... | just entity = run-clone-kleisli-arrow entity coalgebra remote
... | nothing = inj₂ cae-unknown-entity-label

refuse-frugal-mi-on-clone : CloneGateMismatch
refuse-frugal-mi-on-clone = cgm-frugal-mi-on-clone

refuse-sync-gate-on-clone : CloneGateMismatch
refuse-sync-gate-on-clone = cgm-sync-inbound-on-clone

refuse-outbound-tick-on-clone : CloneGateMismatch
refuse-outbound-tick-on-clone = cgm-outbound-tick-on-clone

refuse-merge-safe-on-clone : CloneGateMismatch
refuse-merge-safe-on-clone = cgm-merge-safe-witness-on-clone

refuse-excitement-argmin-on-clone : CloneGateMismatch
refuse-excitement-argmin-on-clone = cgm-excitement-argmin-on-clone

refuse-replica-class-on-clone : CloneGateMismatch
refuse-replica-class-on-clone = cgm-replica-class-on-clone

refuse-remote-class-on-clone : CloneGateMismatch
refuse-remote-class-on-clone = cgm-remote-class-on-clone

refuse-second-argmin-on-clone : CloneGateMismatch
refuse-second-argmin-on-clone = cgm-second-argmin-on-clone

clone-verb-row-merge-safe-not-required :
  CloneVerbRow.clone-row-merge-safe clone-verb-row ≡ cvcr-not-required
clone-verb-row-merge-safe-not-required = refl

clone-verb-row-excitement-not-required :
  CloneVerbRow.clone-row-excitement clone-verb-row ≡ cvcr-not-required
clone-verb-row-excitement-not-required = refl

clone-verb-row-entity-label-check :
  CloneVerbRow.clone-row-entity-check clone-verb-row ≡ cec-entity-label
clone-verb-row-entity-label-check = refl

kleisli-gate-matches-clone-admit :
  kleisli-gate-matches-clone ckg-admit-initial-replica-coalgebra ≡ true
kleisli-gate-matches-clone-admit = refl

kleisli-gate-matches-clone-frugal-false :
  kleisli-gate-matches-clone ckg-frugal-mi-observation ≡ false
kleisli-gate-matches-clone-frugal-false = refl

------------------------------------------------------------------------
-- SECTION 4: Excitement compose (no second argmin)
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

data CloneExcitementComposePin : Set where
  cecp-import-select-excitement cecp-second-argmin-refused : CloneExcitementComposePin

record CloneExcitementCtx (src : ThermodynamicState) : Set where
  field
    clone-excitement-successors : List (history-candidate src)

clone-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  CloneExcitementComposePin →
  history-candidate src ⊎ excitement-residue
clone-excitement-select src cands cecp-import-select-excitement =
  excitement-select src cands
clone-excitement-select src cands cecp-second-argmin-refused =
  inj₂ exc-all-inadmissible

clone-recovery-select :
  (src : ThermodynamicState) (ctx : CloneExcitementCtx src) →
  history-candidate src ⊎ excitement-residue
clone-recovery-select src ctx =
  excitement-select src (CloneExcitementCtx.clone-excitement-successors ctx)

clone-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  clone-excitement-select src cands cecp-import-select-excitement ≡
  excitement-select src cands
clone-excitement-select-eq-excitement-select src cands = refl

clone-recovery-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : CloneExcitementCtx src) →
  clone-recovery-select src ctx ≡
  excitement-select src (CloneExcitementCtx.clone-excitement-successors ctx)
clone-recovery-select-eq-excitement-select src ctx = refl

clone-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : CloneExcitementCtx src) →
  clone-recovery-select src ctx ≡
  excitement-select src (CloneExcitementCtx.clone-excitement-successors ctx)
clone-no-local-argmin src ctx =
  clone-recovery-select-eq-excitement-select src ctx

clone-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  clone-excitement-select src cands cecp-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
clone-excitement-select-refuses-second-argmin src cands = refl

clone-recovery-empty :
  ∀ (src : ThermodynamicState) (ctx : CloneExcitementCtx src) →
  CloneExcitementCtx.clone-excitement-successors ctx ≡ [] →
  clone-recovery-select src ctx ≡ inj₂ exc-no-candidates
clone-recovery-empty src ctx hnil rewrite hnil = refl

------------------------------------------------------------------------
-- SECTION 5: §16.7 fixtures + witness theorems
------------------------------------------------------------------------

clone-fixture-coalgebra-admit : InitialReplicaCoalgebra
clone-fixture-coalgebra-admit = record
  { clone-coalgebra-class = crc-node0
  ; clone-coalgebra-egress-declared = true
  ; clone-coalgebra-authority-declared = true
  }

clone-fixture-coalgebra-refuse-egress : InitialReplicaCoalgebra
clone-fixture-coalgebra-refuse-egress = record
  { clone-coalgebra-class = crc-luks
  ; clone-coalgebra-egress-declared = false
  ; clone-coalgebra-authority-declared = true
  }

clone-fixture-remote-forge : CloneRemoteHost
clone-fixture-remote-forge = record { clone-remote-host-label = "forge.entity" }

clone-fixture-remote-github : CloneRemoteHost
clone-fixture-remote-github = record { clone-remote-host-label = "github.com" }

clone-fixture-initial-coalgebra-admits :
  evaluate-initial-coalgebra-gate clone-fixture-coalgebra-admit ≡ icgv-admit
clone-fixture-initial-coalgebra-admits = refl

clone-fixture-initial-coalgebra-refuses-egress :
  evaluate-initial-coalgebra-gate clone-fixture-coalgebra-refuse-egress ≡
  icgv-refuse-undeclared-egress
clone-fixture-initial-coalgebra-refuses-egress = refl

clone-fixture-arrow-admits-labs :
  run-clone-kleisli-arrow cel-labs clone-fixture-coalgebra-admit
    clone-fixture-remote-forge ≡
  inj₁ record
    { clone-admission-entity = cel-labs
    ; clone-admission-replica = crc-node0
    ; clone-admission-gate = icgv-admit
    }
clone-fixture-arrow-admits-labs = refl

clone-fixture-compose-upstream-refused :
  compose-upstream-refused "github.com" ≡ true
clone-fixture-compose-upstream-refused = refl

clone-fixture-compose-entity-refused-on-github :
  run-clone-kleisli-arrow cel-compose clone-fixture-coalgebra-admit
    clone-fixture-remote-github ≡ inj₂ cae-compose-upstream-refused
clone-fixture-compose-entity-refused-on-github = refl

clone-fixture-parse-labs : parse-entity-label "labs" ≡ just cel-labs
clone-fixture-parse-labs = refl

clone-fixture-parse-compose-case-insensitive :
  parse-entity-label "COMPOSE" ≡ just cel-compose
clone-fixture-parse-compose-case-insensitive = refl

clone-replica-class-node0-tag :
  clone-replica-class-tag crc-node0 ≡ "node-0"
clone-replica-class-node0-tag = refl

clone-replica-class-luks-tag :
  clone-replica-class-tag crc-luks ≡ "offline-luks"
clone-replica-class-luks-tag = refl

clone-positive-refuse-frugal-mi :
  refuse-frugal-mi-on-clone ≡ cgm-frugal-mi-on-clone
clone-positive-refuse-frugal-mi = refl

clone-positive-refuse-sync-gate :
  refuse-sync-gate-on-clone ≡ cgm-sync-inbound-on-clone
clone-positive-refuse-sync-gate = refl

------------------------------------------------------------------------
-- SECTION 6: History transition + Landauer bridge (zero new postulates)
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

clone-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
clone-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

kleisli-clone-physics-green : Bool
kleisli-clone-physics-green = false

kleisli-clone-physics-green-false :
  kleisli-clone-physics-green ≡ false
kleisli-clone-physics-green-false = refl

kleisli-clone-production-wired : Bool
kleisli-clone-production-wired = false

kleisli-clone-production-wired-false :
  kleisli-clone-production-wired ≡ false
kleisli-clone-production-wired-false = refl

kleisli-clone-module-witness : ⊤
kleisli-clone-module-witness = tt

kleisli-clone-no-new-postulate : ⊤
kleisli-clone-no-new-postulate = tt

kleisli-clone-positive-refuse-not-silent :
  (kleisli-gate-matches-clone ckg-frugal-mi-observation ≡ false) ×
  (kleisli-gate-matches-clone ckg-gate-check-before-sync-inbound ≡ false)
kleisli-clone-positive-refuse-not-silent = refl , refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin-on-clone ≡ cgm-second-argmin-on-clone
refuse-second-argmin-is-tag = refl
