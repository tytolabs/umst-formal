-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.EntityRemote — meso/acting §13.6 entity remotes classification.
--
-- URGE-FORMAL-MESO-AGDA-ENTITY-REMOTE (umst-formal acting fiber only).
-- §13.6: `[urge.remote.*]` policy types; pre-push refuse github /
-- origin.cursor.com when entity = compose. Compose `entity-remote-select`
-- / `excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.EntityRemote where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; not; _∧_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (¬_)

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

record HistorySnapshot : Set where
  field
    commit-id head-id : ℕ

record HistoryTransition : Set where
  field
    prior : HistorySnapshot
    post : HistorySnapshot
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

------------------------------------------------------------------------
-- SECTION 1: §13.6 `[urge.remote.*]` policy carriers
------------------------------------------------------------------------

urge-remote-section-prefix : String
urge-remote-section-prefix = "urge.remote."

data urge-entity : Set where
  ue-labs ue-compose : urge-entity

data remote-classification : Set where
  rc-public-oss rc-labs-internal rc-compose-confidential rc-compose-defence rc-proposal-confidential : remote-classification

data canonical-remote : Set where
  cr-forge cr-none : canonical-remote

data mirror-remote : Set where
  mr-github mr-none : mirror-remote

data entity-remote-host : Set where
  erh-github erh-origin-cursor erh-forge erh-unclassified : entity-remote-host

record urge-remote-policy : Set where
  field
    erp-section : String
    erp-entity : urge-entity
    erp-classification : remote-classification
    erp-canonical : canonical-remote
    erp-mirror : mirror-remote

data entity-pre-push-verdict : Set where
  eppv-admitted eppv-compose-github-refused eppv-compose-origin-refused eppv-origin-never-ssot-refused eppv-unclassified-host-refused eppv-production-wired-refused : entity-pre-push-verdict

data entity-pre-push-refusal : Set where
  eppr-compose-github-refused eppr-compose-origin-refused eppr-origin-never-ssot-refused : entity-pre-push-refusal
  eppr-unclassified-host-refused : entity-remote-host → entity-pre-push-refusal
  eppr-production-wired-refused : entity-pre-push-refusal

data entity-remote-verdict : Set where
  erv-policy-ok erv-upstream-refused erv-inadmissible : entity-remote-verdict

------------------------------------------------------------------------
-- SECTION 2: §13.6 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record entity-remote-conjunct : Set where
  field
    erc-conj-gate-ok erc-conj-policy-typed erc-conj-excitement-preserves : Bool

entity-remote-conjunct-admits : entity-remote-conjunct → Bool
entity-remote-conjunct-admits c =
  entity-remote-conjunct.erc-conj-gate-ok c ∧
  entity-remote-conjunct.erc-conj-policy-typed c ∧
  entity-remote-conjunct.erc-conj-excitement-preserves c

classification-entity : remote-classification → urge-entity
classification-entity rc-public-oss = ue-labs
classification-entity rc-labs-internal = ue-labs
classification-entity rc-proposal-confidential = ue-labs
classification-entity rc-compose-confidential = ue-compose
classification-entity rc-compose-defence = ue-compose

data parse-urge-entity-result : Set where
  parsed-urge-entity : urge-entity → parse-urge-entity-result
  parse-urge-entity-unknown : parse-urge-entity-result

parse-urge-entity : String → parse-urge-entity-result
parse-urge-entity "labs" = parsed-urge-entity ue-labs
parse-urge-entity "LABS" = parsed-urge-entity ue-labs
parse-urge-entity "compose" = parsed-urge-entity ue-compose
parse-urge-entity "COMPOSE" = parsed-urge-entity ue-compose
parse-urge-entity _ = parse-urge-entity-unknown

classify-entity-remote-host : String → entity-remote-host
classify-entity-remote-host "" = erh-unclassified
classify-entity-remote-host "origin.cursor.com" = erh-origin-cursor
classify-entity-remote-host "github.com" = erh-github
classify-entity-remote-host "forge.tyto.in" = erh-forge
classify-entity-remote-host "forge.entity" = erh-forge
classify-entity-remote-host _ = erh-unclassified

labs-github-verdict : remote-classification → entity-pre-push-verdict ⊎ entity-pre-push-refusal
labs-github-verdict rc-public-oss = inj₁ eppv-admitted
labs-github-verdict rc-labs-internal = inj₂ (eppr-unclassified-host-refused erh-github)
labs-github-verdict rc-compose-confidential = inj₂ (eppr-unclassified-host-refused erh-github)
labs-github-verdict rc-compose-defence = inj₂ (eppr-unclassified-host-refused erh-github)
labs-github-verdict rc-proposal-confidential = inj₂ (eppr-unclassified-host-refused erh-github)

evaluate-entity-pre-push :
  (policy : urge-remote-policy) (host : entity-remote-host) →
  entity-pre-push-verdict ⊎ entity-pre-push-refusal
evaluate-entity-pre-push policy erh-origin-cursor with urge-remote-policy.erp-entity policy
... | ue-compose = inj₂ eppr-compose-origin-refused
... | ue-labs = inj₂ eppr-origin-never-ssot-refused
evaluate-entity-pre-push policy erh-github with urge-remote-policy.erp-entity policy
... | ue-compose = inj₂ eppr-compose-github-refused
... | ue-labs = labs-github-verdict (urge-remote-policy.erp-classification policy)
evaluate-entity-pre-push policy erh-forge = inj₁ eppv-admitted
evaluate-entity-pre-push policy erh-unclassified =
  inj₂ (eppr-unclassified-host-refused erh-unclassified)

refuse-production-wired-entity-push : entity-pre-push-refusal
refuse-production-wired-entity-push = eppr-production-wired-refused

evaluate-entity-remote-operation :
  (is-upstream-refused : Bool) → entity-remote-verdict
evaluate-entity-remote-operation true = erv-upstream-refused
evaluate-entity-remote-operation false = erv-policy-ok

apply-entity-remote-policy :
  (policy : urge-remote-policy) (host : entity-remote-host) →
  (conjunct : entity-remote-conjunct) (excitement-selected : Bool) →
  urge-remote-policy ⊎ entity-pre-push-refusal
apply-entity-remote-policy policy host conjunct excitement-selected with
  entity-remote-conjunct-admits conjunct
... | false = inj₂ (eppr-unclassified-host-refused erh-unclassified)
... | true with not excitement-selected
... | true = inj₂ (eppr-unclassified-host-refused erh-unclassified)
... | false with evaluate-entity-pre-push policy host
... | inj₁ _ = inj₁ policy
... | inj₂ r = inj₂ r

------------------------------------------------------------------------
-- SECTION 3: Entity remote composes Excitement (no second ℚ argmin)
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
excitement-select src List.[] = inj₂ exc-no-candidates
excitement-select src (c List.∷ _) = inj₁ c

record entity-remote-ctx (src : ThermodynamicState) : Set where
  field
    entity-remote-successors : List (history-candidate src)

entity-remote-select :
  (src : ThermodynamicState) (ctx : entity-remote-ctx src) →
  history-candidate src ⊎ excitement-residue
entity-remote-select src ctx =
  excitement-select src (entity-remote-ctx.entity-remote-successors ctx)

entity-remote-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : entity-remote-ctx src) →
  entity-remote-select src ctx ≡
  excitement-select src (entity-remote-ctx.entity-remote-successors ctx)
entity-remote-select-eq-excitement-select src ctx = refl

entity-remote-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : entity-remote-ctx src) →
  entity-remote-select src ctx ≡
  excitement-select src (entity-remote-ctx.entity-remote-successors ctx)
entity-remote-select-eq-urge-recovery-select src ctx = refl

entity-remote-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : entity-remote-ctx src) →
  entity-remote-select src ctx ≡
  excitement-select src (entity-remote-ctx.entity-remote-successors ctx)
entity-remote-no-local-argmin src ctx = refl

entity-remote-empty :
  ∀ (src : ThermodynamicState) (ctx : entity-remote-ctx src) →
  entity-remote-ctx.entity-remote-successors ctx ≡ List.[] →
  entity-remote-select src ctx ≡ inj₂ exc-no-candidates
entity-remote-empty src ctx Hnil rewrite Hnil = refl

urge-entity-remote-select :
  (src : ThermodynamicState) (ctx : entity-remote-ctx src) →
  history-candidate src ⊎ excitement-residue
urge-entity-remote-select = entity-remote-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

------------------------------------------------------------------------
-- SECTION 4: §13.6 fixtures + witness theorems
------------------------------------------------------------------------

entity-remote-fixture-labs-public : urge-remote-policy
entity-remote-fixture-labs-public = record
  { erp-section = "labs-public"
  ; erp-entity = ue-labs
  ; erp-classification = rc-public-oss
  ; erp-canonical = cr-forge
  ; erp-mirror = mr-github
  }

entity-remote-fixture-compose-confidential : urge-remote-policy
entity-remote-fixture-compose-confidential = record
  { erp-section = "compose-confidential"
  ; erp-entity = ue-compose
  ; erp-classification = rc-compose-confidential
  ; erp-canonical = cr-forge
  ; erp-mirror = mr-none
  }

entity-remote-fixture-conjunct : entity-remote-conjunct
entity-remote-fixture-conjunct = record
  { erc-conj-gate-ok = true
  ; erc-conj-policy-typed = true
  ; erc-conj-excitement-preserves = true
  }

entity-remote-fixture-state : ThermodynamicState
entity-remote-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

entity-remote-labs-github-admitted :
  evaluate-entity-pre-push entity-remote-fixture-labs-public erh-github ≡
  inj₁ eppv-admitted
entity-remote-labs-github-admitted = refl

entity-remote-compose-github-refused :
  evaluate-entity-pre-push entity-remote-fixture-compose-confidential erh-github ≡
  inj₂ eppr-compose-github-refused
entity-remote-compose-github-refused = refl

entity-remote-compose-origin-refused :
  evaluate-entity-pre-push entity-remote-fixture-compose-confidential erh-origin-cursor ≡
  inj₂ eppr-compose-origin-refused
entity-remote-compose-origin-refused = refl

entity-remote-origin-never-ssot-refused :
  evaluate-entity-pre-push entity-remote-fixture-labs-public erh-origin-cursor ≡
  inj₂ eppr-origin-never-ssot-refused
entity-remote-origin-never-ssot-refused = refl

entity-remote-compose-forge-admitted :
  evaluate-entity-pre-push entity-remote-fixture-compose-confidential erh-forge ≡
  inj₁ eppv-admitted
entity-remote-compose-forge-admitted = refl

entity-remote-section-prefix-witness :
  urge-remote-section-prefix ≡ "urge.remote."
entity-remote-section-prefix-witness = refl

entity-remote-parse-labs :
  parse-urge-entity "labs" ≡ parsed-urge-entity ue-labs
entity-remote-parse-labs = refl

entity-remote-parse-compose :
  parse-urge-entity "compose" ≡ parsed-urge-entity ue-compose
entity-remote-parse-compose = refl

entity-remote-classification-entity-labs :
  classification-entity rc-public-oss ≡ ue-labs
entity-remote-classification-entity-labs = refl

entity-remote-classification-entity-compose :
  classification-entity rc-compose-confidential ≡ ue-compose
entity-remote-classification-entity-compose = refl

entity-remote-fixture-apply-policy-ok :
  apply-entity-remote-policy
    entity-remote-fixture-labs-public erh-forge
    entity-remote-fixture-conjunct true ≡
  inj₁ entity-remote-fixture-labs-public
entity-remote-fixture-apply-policy-ok = refl

entity-remote-upstream-refused-positive :
  evaluate-entity-remote-operation true ≡ erv-upstream-refused
entity-remote-upstream-refused-positive = refl

entity-remote-policy-ok-when-not-upstream :
  evaluate-entity-remote-operation false ≡ erv-policy-ok
entity-remote-policy-ok-when-not-upstream = refl

refuse-production-wired-entity-push-positive :
  refuse-production-wired-entity-push ≡ eppr-production-wired-refused
refuse-production-wired-entity-push-positive = refl

entity-remote-positive-refuse-not-silent :
  evaluate-entity-remote-operation true ≢ erv-policy-ok
entity-remote-positive-refuse-not-silent ()

entity-remote-compose-github-positive-refuse :
  evaluate-entity-pre-push entity-remote-fixture-compose-confidential erh-github ≢
  inj₁ eppv-admitted
entity-remote-compose-github-positive-refuse ()

------------------------------------------------------------------------
-- SECTION 5: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

entity-remote-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
entity-remote-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

entity-remote-production-wired : Bool
entity-remote-production-wired = false

entity-remote-production-wired-false :
  entity-remote-production-wired ≡ false
entity-remote-production-wired-false = refl

entity-remote-marker : ℕ
entity-remote-marker = 1

entity-remote-marker-eq : entity-remote-marker ≡ 1
entity-remote-marker-eq = refl

entity-remote-module-witness : ⊤
entity-remote-module-witness = tt

entity-remote-no-new-postulate : ⊤
entity-remote-no-new-postulate = tt
