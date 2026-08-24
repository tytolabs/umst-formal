-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.UmstTomlRemotes — meso/acting §13.6 root `umst.toml`.
--
-- URGE-FORMAL-MESO-AGDA-UMST-TOML-REMOTES (umst-formal acting fiber only).
-- §13.6: `[urge.remote.*]` in root `umst.toml` types; typed parse of proposed
-- remote policy rows; pre-push positive refuse — not only `!physics_green`.
-- Compose `umst-toml-remotes-select` / `excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.UmstTomlRemotes where

open import Urge.EntityRemote

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; not; _∧_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.String using (String; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 1: Root `umst.toml` `[urge.remote.*]` carriers
------------------------------------------------------------------------

record urge-remote-toml-row : Set where
  field
    urtr-section : String
    urtr-entity : urge-entity
    urtr-classification : remote-classification
    urtr-canonical : canonical-remote
    urtr-mirror : mirror-remote

record umst-toml-remotes-document : Set where
  field
    utrd-rows : List urge-remote-toml-row

data toml-remote-parse-error : Set where
  trpe-no-remote-sections : toml-remote-parse-error
  trpe-missing-field : String → String → toml-remote-parse-error
  trpe-unknown-value : String → String → String → toml-remote-parse-error

data umst-toml-remotes-import-refusal : Set where
  utmir-second-argmin : umst-toml-remotes-import-refusal

data umst-toml-remotes-verdict : Set where
  utmv-document-ok utmv-parse-refused utmv-inadmissible : umst-toml-remotes-verdict

------------------------------------------------------------------------
-- SECTION 2: Row ↔ policy bridge + pre-push evaluation
------------------------------------------------------------------------

urge-remote-toml-section-key : urge-remote-toml-row → String
urge-remote-toml-section-key row =
  urge-remote-section-prefix ++ urge-remote-toml-row.urtr-section row

urge-remote-toml-row-to-policy : urge-remote-toml-row → urge-remote-policy
urge-remote-toml-row-to-policy row = record
  { erp-section = urge-remote-toml-row.urtr-section row
  ; erp-entity = urge-remote-toml-row.urtr-entity row
  ; erp-classification = urge-remote-toml-row.urtr-classification row
  ; erp-canonical = urge-remote-toml-row.urtr-canonical row
  ; erp-mirror = urge-remote-toml-row.urtr-mirror row
  }

evaluate-toml-pre-push :
  (row : urge-remote-toml-row) (host : entity-remote-host) →
  entity-pre-push-verdict ⊎ entity-pre-push-refusal
evaluate-toml-pre-push row host =
  evaluate-entity-pre-push (urge-remote-toml-row-to-policy row) host

record umst-toml-remotes-conjunct : Set where
  field
    utrc-conj-gate-ok utrc-conj-document-typed utrc-conj-excitement-preserves : Bool

umst-toml-remotes-conjunct-admits : umst-toml-remotes-conjunct → Bool
umst-toml-remotes-conjunct-admits c =
  umst-toml-remotes-conjunct.utrc-conj-gate-ok c ∧
  umst-toml-remotes-conjunct.utrc-conj-document-typed c ∧
  umst-toml-remotes-conjunct.utrc-conj-excitement-preserves c

evaluate-umst-toml-remotes-operation :
  (is-parse-refused : Bool) → umst-toml-remotes-verdict
evaluate-umst-toml-remotes-operation true = utmv-parse-refused
evaluate-umst-toml-remotes-operation false = utmv-document-ok

refuse-second-argmin-selector : umst-toml-remotes-import-refusal
refuse-second-argmin-selector = utmir-second-argmin

refuse-production-wired-toml-push : entity-pre-push-refusal
refuse-production-wired-toml-push = eppr-production-wired-refused

apply-umst-toml-remote-row :
  (row : urge-remote-toml-row) (host : entity-remote-host) →
  (conjunct : umst-toml-remotes-conjunct) (excitement-selected : Bool) →
  urge-remote-toml-row ⊎ entity-pre-push-refusal
apply-umst-toml-remote-row row host conjunct excitement-selected with
  umst-toml-remotes-conjunct-admits conjunct
... | false = inj₂ (eppr-unclassified-host-refused erh-unclassified)
... | true with not excitement-selected
... | true = inj₂ (eppr-unclassified-host-refused erh-unclassified)
... | false with evaluate-toml-pre-push row host
... | inj₁ _ = inj₁ row
... | inj₂ r = inj₂ r

umst-toml-remotes-parse-refused-positive :
  evaluate-umst-toml-remotes-operation true ≡ utmv-parse-refused
umst-toml-remotes-parse-refused-positive = refl

umst-toml-remotes-document-ok-when-not-parse-refused :
  evaluate-umst-toml-remotes-operation false ≡ utmv-document-ok
umst-toml-remotes-document-ok-when-not-parse-refused = refl

refuse-second-argmin-selector-positive :
  refuse-second-argmin-selector ≡ utmir-second-argmin
refuse-second-argmin-selector-positive = refl

refuse-production-wired-toml-push-positive :
  refuse-production-wired-toml-push ≡ eppr-production-wired-refused
refuse-production-wired-toml-push-positive = refl

------------------------------------------------------------------------
-- SECTION 3: Fixture document + honest parse surrogate
------------------------------------------------------------------------

umst-toml-fixture-labs-public : urge-remote-toml-row
umst-toml-fixture-labs-public = record
  { urtr-section = "labs-public"
  ; urtr-entity = ue-labs
  ; urtr-classification = rc-public-oss
  ; urtr-canonical = cr-forge
  ; urtr-mirror = mr-github
  }

umst-toml-fixture-compose-confidential : urge-remote-toml-row
umst-toml-fixture-compose-confidential = record
  { urtr-section = "compose-confidential"
  ; urtr-entity = ue-compose
  ; urtr-classification = rc-compose-confidential
  ; urtr-canonical = cr-forge
  ; urtr-mirror = mr-none
  }

root-umst-toml-fixture-document : umst-toml-remotes-document
root-umst-toml-fixture-document = record
  { utrd-rows =
      umst-toml-fixture-labs-public ∷
      umst-toml-fixture-compose-confidential ∷
      List.[]
  }

parse-root-umst-toml-remotes-fixture :
  umst-toml-remotes-document ⊎ toml-remote-parse-error
parse-root-umst-toml-remotes-fixture = inj₁ root-umst-toml-fixture-document

parse-root-umst-toml-remotes-empty :
  umst-toml-remotes-document ⊎ toml-remote-parse-error
parse-root-umst-toml-remotes-empty = inj₂ trpe-no-remote-sections

root-umst-toml-fixture-document-two-rows :
  List.length (umst-toml-remotes-document.utrd-rows root-umst-toml-fixture-document) ≡ 2
root-umst-toml-fixture-document-two-rows = refl

parse-root-umst-toml-remotes-fixture-ok :
  parse-root-umst-toml-remotes-fixture ≡ inj₁ root-umst-toml-fixture-document
parse-root-umst-toml-remotes-fixture-ok = refl

parse-root-umst-toml-remotes-empty-refused :
  parse-root-umst-toml-remotes-empty ≡ inj₂ trpe-no-remote-sections
parse-root-umst-toml-remotes-empty-refused = refl

------------------------------------------------------------------------
-- SECTION 4: Root `umst.toml` composes Excitement (no second argmin)
------------------------------------------------------------------------

record umst-toml-remotes-ctx (src : ThermodynamicState) : Set where
  field
    umst-toml-remotes-successors : List (history-candidate src)

umst-toml-remotes-select :
  (src : ThermodynamicState) (ctx : umst-toml-remotes-ctx src) →
  history-candidate src ⊎ excitement-residue
umst-toml-remotes-select src ctx =
  excitement-select src (umst-toml-remotes-ctx.umst-toml-remotes-successors ctx)

umst-toml-remotes-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : umst-toml-remotes-ctx src) →
  umst-toml-remotes-select src ctx ≡
  excitement-select src (umst-toml-remotes-ctx.umst-toml-remotes-successors ctx)
umst-toml-remotes-select-eq-excitement-select src ctx = refl

umst-toml-remotes-select-eq-entity-remote-select :
  ∀ (src : ThermodynamicState) (ctx : umst-toml-remotes-ctx src) →
  umst-toml-remotes-select src ctx ≡
  excitement-select src (umst-toml-remotes-ctx.umst-toml-remotes-successors ctx)
umst-toml-remotes-select-eq-entity-remote-select src ctx = refl

umst-toml-remotes-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : umst-toml-remotes-ctx src) →
  umst-toml-remotes-select src ctx ≡
  excitement-select src (umst-toml-remotes-ctx.umst-toml-remotes-successors ctx)
umst-toml-remotes-no-local-argmin src ctx = refl

umst-toml-remotes-empty :
  ∀ (src : ThermodynamicState) (ctx : umst-toml-remotes-ctx src) →
  umst-toml-remotes-ctx.umst-toml-remotes-successors ctx ≡ List.[] →
  umst-toml-remotes-select src ctx ≡ inj₂ exc-no-candidates
umst-toml-remotes-empty src ctx Hnil rewrite Hnil = refl

urge-umst-toml-remotes-select :
  (src : ThermodynamicState) (ctx : umst-toml-remotes-ctx src) →
  history-candidate src ⊎ excitement-residue
urge-umst-toml-remotes-select = umst-toml-remotes-select

umst-toml-excitement-compose-pin : ℕ
umst-toml-excitement-compose-pin = 0

umst-toml-excitement-compose-pin-marker : umst-toml-excitement-compose-pin ≡ 0
umst-toml-excitement-compose-pin-marker = refl

------------------------------------------------------------------------
-- SECTION 5: §13.6 fixtures + witness theorems
------------------------------------------------------------------------

umst-toml-fixture-conjunct : umst-toml-remotes-conjunct
umst-toml-fixture-conjunct = record
  { utrc-conj-gate-ok = true
  ; utrc-conj-document-typed = true
  ; utrc-conj-excitement-preserves = true
  }

umst-toml-fixture-state : ThermodynamicState
umst-toml-fixture-state = entity-remote-fixture-state

umst-toml-labs-public-section-key :
  urge-remote-toml-section-key umst-toml-fixture-labs-public ≡
  "urge.remote.labs-public"
umst-toml-labs-public-section-key = refl

umst-toml-compose-confidential-section-key :
  urge-remote-toml-section-key umst-toml-fixture-compose-confidential ≡
  "urge.remote.compose-confidential"
umst-toml-compose-confidential-section-key = refl

umst-toml-row-to-policy-labs-public :
  urge-remote-toml-row-to-policy umst-toml-fixture-labs-public ≡
  entity-remote-fixture-labs-public
umst-toml-row-to-policy-labs-public = refl

umst-toml-row-to-policy-compose-confidential :
  urge-remote-toml-row-to-policy umst-toml-fixture-compose-confidential ≡
  entity-remote-fixture-compose-confidential
umst-toml-row-to-policy-compose-confidential = refl

umst-toml-labs-github-admitted :
  evaluate-toml-pre-push umst-toml-fixture-labs-public erh-github ≡
  inj₁ eppv-admitted
umst-toml-labs-github-admitted = refl

umst-toml-compose-github-refused :
  evaluate-toml-pre-push umst-toml-fixture-compose-confidential erh-github ≡
  inj₂ eppr-compose-github-refused
umst-toml-compose-github-refused = refl

umst-toml-compose-origin-refused :
  evaluate-toml-pre-push umst-toml-fixture-compose-confidential erh-origin-cursor ≡
  inj₂ eppr-compose-origin-refused
umst-toml-compose-origin-refused = refl

umst-toml-compose-forge-admitted :
  evaluate-toml-pre-push umst-toml-fixture-compose-confidential erh-forge ≡
  inj₁ eppv-admitted
umst-toml-compose-forge-admitted = refl

umst-toml-fixture-apply-row-ok :
  apply-umst-toml-remote-row
    umst-toml-fixture-labs-public erh-forge
    umst-toml-fixture-conjunct true ≡
  inj₁ umst-toml-fixture-labs-public
umst-toml-fixture-apply-row-ok = refl

umst-toml-section-prefix-witness :
  urge-remote-section-prefix ≡ "urge.remote."
umst-toml-section-prefix-witness = entity-remote-section-prefix-witness

umst-toml-positive-refuse-not-silent :
  evaluate-umst-toml-remotes-operation true ≢ utmv-document-ok
umst-toml-positive-refuse-not-silent ()

umst-toml-compose-github-positive-refuse :
  evaluate-toml-pre-push umst-toml-fixture-compose-confidential erh-github ≢
  inj₁ eppv-admitted
umst-toml-compose-github-positive-refuse ()

umst-toml-compose-origin-positive-refuse :
  evaluate-toml-pre-push umst-toml-fixture-compose-confidential erh-origin-cursor ≢
  inj₁ eppv-admitted
umst-toml-compose-origin-positive-refuse ()

------------------------------------------------------------------------
-- SECTION 6: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

umst-toml-remotes-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
umst-toml-remotes-second-law-from-landauer proc ΔS t hent hdiss =
  entity-remote-second-law-from-landauer proc ΔS t hent hdiss

umst-toml-landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
umst-toml-landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

umst-toml-physics-green : Bool
umst-toml-physics-green = false

umst-toml-physics-green-false : umst-toml-physics-green ≡ false
umst-toml-physics-green-false = refl

umst-toml-remotes-production-wired : Bool
umst-toml-remotes-production-wired = false

umst-toml-remotes-production-wired-false :
  umst-toml-remotes-production-wired ≡ false
umst-toml-remotes-production-wired-false = refl

umst-toml-remotes-marker : ℕ
umst-toml-remotes-marker = 1

umst-toml-remotes-marker-eq : umst-toml-remotes-marker ≡ 1
umst-toml-remotes-marker-eq = refl

umst-toml-remotes-module-witness : ⊤
umst-toml-remotes-module-witness = tt

umst-toml-remotes-no-new-postulate : ⊤
umst-toml-remotes-no-new-postulate = tt

refuse-second-argmin-is-tag :
  refuse-second-argmin-selector ≡ utmir-second-argmin
refuse-second-argmin-is-tag = refl
