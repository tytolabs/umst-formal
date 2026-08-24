-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.OriginRefuse — meso/acting §16.8 origin refuse.
--
-- URGE-FORMAL-MESO-AGDA-ORIGIN-REFUSE (umst-formal acting fiber only).
-- §16.8: `origin.cursor.com` and GitHub-as-origin are refused for Compose.
-- India-resident Forgejo is canonical SSOT. Typed positive refuse — not only
-- `!physics_green`. Compose `origin-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.OriginRefuse where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers (minimal meso acting mirror)
------------------------------------------------------------------------

record HistorySnapshot : Set where
  field
    commit-id : ℕ
    head-id : ℕ

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

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

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
-- SECTION 2: Entity + origin host classification (§16.8 policy row)
------------------------------------------------------------------------

data UrgeEntity : Set where
  compose : UrgeEntity
  labs-public-oss : UrgeEntity

data OriginHost : Set where
  origin-cursor : OriginHost
  github : OriginHost
  forgejo-canonical : OriginHost
  unclassified : OriginHost

data OriginPolicyVerdict : Set where
  origin-admitted : OriginPolicyVerdict
  origin-refused : OriginPolicyVerdict

record origin-candidate : Set where
  field
    cand-id : ℕ
    cand-free-energy : ℚ
    host-class : OriginHost
    entity-class : UrgeEntity

------------------------------------------------------------------------
-- SECTION 3: Origin remote attempt carrier
------------------------------------------------------------------------

record OriginRemoteAttempt : Set where
  field
    remote-id : ℕ
    entity : UrgeEntity
    host : OriginHost
    dual-push : Bool
    source-free-energy : ℚ

record ForgejoCanonicalWitness : Set where
  field
    witness-id : ℕ
    india-resident : Bool

forgejo-witness-from-fields :
  (id : ℕ) (resident : Bool) → ForgejoCanonicalWitness
forgejo-witness-from-fields id resident = record
  { witness-id = id
  ; india-resident = resident
  }

------------------------------------------------------------------------
-- SECTION 4: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data OriginRefusal : Set where
  origin-cursor-compose-refused : OriginRefusal
  github-as-origin-compose-refused : OriginRefusal
  origin-cursor-labs-refused : OriginRefusal
  unclassified-host : OriginRefusal
  dual-push-compose-refused : OriginRefusal
  second-argmin : OriginRefusal

data OriginClass : Set where
  forgejo-canonical-ssot : OriginClass
  compose-excitement-arrow : OriginClass

refuse-origin-cursor-compose : OriginRefusal
refuse-origin-cursor-compose = origin-cursor-compose-refused

refuse-github-as-origin-compose : OriginRefusal
refuse-github-as-origin-compose = github-as-origin-compose-refused

refuse-origin-cursor-labs : OriginRefusal
refuse-origin-cursor-labs = origin-cursor-labs-refused

refuse-unclassified-host : OriginRefusal
refuse-unclassified-host = unclassified-host

refuse-dual-push-compose : OriginRefusal
refuse-dual-push-compose = dual-push-compose-refused

refuse-second-argmin : OriginRefusal
refuse-second-argmin = second-argmin

------------------------------------------------------------------------
-- SECTION 5: Gate origin policy (§16.8 entity × host)
------------------------------------------------------------------------

evaluate-origin-policy :
  (entity : UrgeEntity) (host : OriginHost) →
  OriginPolicyVerdict ⊎ OriginRefusal
evaluate-origin-policy compose origin-cursor = inj₂ origin-cursor-compose-refused
evaluate-origin-policy compose github = inj₂ github-as-origin-compose-refused
evaluate-origin-policy compose forgejo-canonical = inj₁ origin-admitted
evaluate-origin-policy compose unclassified = inj₂ unclassified-host
evaluate-origin-policy labs-public-oss origin-cursor = inj₂ origin-cursor-labs-refused
evaluate-origin-policy labs-public-oss github = inj₁ origin-admitted
evaluate-origin-policy labs-public-oss forgejo-canonical = inj₁ origin-admitted
evaluate-origin-policy labs-public-oss unclassified = inj₂ unclassified-host

gate-origin-refuse-dual-push :
  (attempt : OriginRemoteAttempt) →
  OriginRemoteAttempt.dual-push attempt ≡ true →
  OriginRefusal
gate-origin-refuse-dual-push attempt _ = dual-push-compose-refused

gate-origin-admit-forgejo :
  (attempt : OriginRemoteAttempt) →
  OriginRemoteAttempt.host attempt ≡ forgejo-canonical →
  ⊤
gate-origin-admit-forgejo attempt _ = tt

classify-origin :
  (attempt : OriginRemoteAttempt) →
  OriginClass ⊎ OriginRefusal
classify-origin attempt with OriginRemoteAttempt.dual-push attempt
... | true = inj₂ dual-push-compose-refused
... | false with evaluate-origin-policy (OriginRemoteAttempt.entity attempt)
                                              (OriginRemoteAttempt.host attempt)
... | inj₁ _ = inj₁ compose-excitement-arrow
... | inj₂ r = inj₂ r

------------------------------------------------------------------------
-- SECTION 6: Excitement compose pin (no second argmin)
------------------------------------------------------------------------

origin-excitement-select :
  (src : ℚ) → List origin-candidate →
  origin-candidate ⊎ excitement-residue
origin-excitement-select src List.[] = inj₂ exc-no-candidates
origin-excitement-select src (c List.∷ _) = inj₁ c

urge-origin-select :
  (src : ℚ) → List origin-candidate →
  origin-candidate ⊎ excitement-residue
urge-origin-select = origin-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 7: §16.8 fixtures + witness theorems
------------------------------------------------------------------------

compose-origin-cursor-fixture : OriginRemoteAttempt
compose-origin-cursor-fixture = record
  { remote-id = 0
  ; entity = compose
  ; host = origin-cursor
  ; dual-push = false
  ; source-free-energy = 0ℚ
  }

compose-github-origin-fixture : OriginRemoteAttempt
compose-github-origin-fixture = record
  { remote-id = 1
  ; entity = compose
  ; host = github
  ; dual-push = false
  ; source-free-energy = 0ℚ
  }

compose-forgejo-canonical-fixture : OriginRemoteAttempt
compose-forgejo-canonical-fixture = record
  { remote-id = 2
  ; entity = compose
  ; host = forgejo-canonical
  ; dual-push = false
  ; source-free-energy = 0ℚ
  }

dual-push-compose-fixture : OriginRemoteAttempt
dual-push-compose-fixture = record
  { remote-id = 3
  ; entity = compose
  ; host = forgejo-canonical
  ; dual-push = true
  ; source-free-energy = 0ℚ
  }

origin-cursor-compose-refused-fixture :
  evaluate-origin-policy compose origin-cursor ≡ inj₂ origin-cursor-compose-refused
origin-cursor-compose-refused-fixture = refl

github-compose-refused-fixture :
  evaluate-origin-policy compose github ≡ inj₂ github-as-origin-compose-refused
github-compose-refused-fixture = refl

forgejo-compose-admitted-fixture :
  evaluate-origin-policy compose forgejo-canonical ≡ inj₁ origin-admitted
forgejo-compose-admitted-fixture = refl

dual-push-classified-refused :
  classify-origin dual-push-compose-fixture ≡ inj₂ dual-push-compose-refused
dual-push-classified-refused = refl

forgejo-classified-admitted :
  classify-origin compose-forgejo-canonical-fixture ≡ inj₁ compose-excitement-arrow
forgejo-classified-admitted = refl

------------------------------------------------------------------------
-- SECTION 8: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

origin-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
origin-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

origin-refuse-production-wired : Bool
origin-refuse-production-wired = false

origin-refuse-production-wired-false :
  origin-refuse-production-wired ≡ false
origin-refuse-production-wired-false = refl

origin-refuse-marker : ℕ
origin-refuse-marker = 1

origin-refuse-marker-eq : origin-refuse-marker ≡ 1
origin-refuse-marker-eq = refl

origin-refuse-module-witness : ⊤
origin-refuse-module-witness = tt

origin-cursor-compose-refused-witness :
  (attempt : OriginRemoteAttempt) →
  (h : OriginRemoteAttempt.entity attempt ≡ compose) →
  (h′ : OriginRemoteAttempt.host attempt ≡ origin-cursor) →
  evaluate-origin-policy compose origin-cursor ≡ inj₂ origin-cursor-compose-refused
origin-cursor-compose-refused-witness attempt h h′ = refl

github-compose-refused-witness :
  refuse-github-as-origin-compose ≡ github-as-origin-compose-refused
github-compose-refused-witness = refl

dual-push-refused :
  (attempt : OriginRemoteAttempt) →
  (h : OriginRemoteAttempt.dual-push attempt ≡ true) →
  gate-origin-refuse-dual-push attempt h ≡ dual-push-compose-refused
dual-push-refused attempt h = refl
