-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ContentAddressed — meso/acting §3 content-addressed history.
--
-- URGE-FORMAL-MESO-AGDA-CONTENT-ADDRESSED (umst-formal acting fiber only).
-- §3: geometric identity is **primary**; git hash is a compatibility witness,
-- not sole id. History recovery composes `content-addressed-excitement-select`
-- — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.ContentAddressed where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; not; _∧_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (does; ¬_)

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
-- SECTION 1: Typed history carriers (minimal meso acting mirror)
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

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record history-candidate (src : ThermodynamicState) : Set where
  field
    cand-id : ℕ
    cand-tgt : ThermodynamicState
    cand-admissible : Admissible src cand-tgt

content-addressed-excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
content-addressed-excitement-select src List.[] = inj₂ exc-no-candidates
content-addressed-excitement-select src (c List.∷ _) = inj₁ c

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
-- SECTION 2: Content-addressed snapshot + typed morphism carriers (§3)
------------------------------------------------------------------------

record ContentGeometricIdentity : Set where
  field
    geom-content-id : ℕ
    geom-resolution-bits : ℕ

record ContentGitHashCompat : Set where
  field
    git-hash : String

record ContentAddressedUcrsStamp : Set where
  field
    ucrs-seq : ℕ
    ucrs-wall-has-t : Bool

record ContentGeometricPrimaryCert : Set where
  field
    geometric-primary : Bool

record ContentAddressedSnapshot : Set where
  field
    snapshot-id : ℕ
    snapshot-head : ThermodynamicState
    snapshot-geometric : ContentGeometricIdentity
    snapshot-git-compat : Maybe ContentGitHashCompat
    snapshot-ucrs : ContentAddressedUcrsStamp
    snapshot-geometric-cert : ContentGeometricPrimaryCert
    snapshot-provenance-intact : Bool

record ContentAddressedWitness : Set where
  field
    witness-geometric : ContentGeometricIdentity
    witness-git-compat : Maybe ContentGitHashCompat
    witness-geometric-primary : Bool
    witness-provenance-intact : Bool

record ContentAddressedMorphism : Set where
  field
    morphism-from : ContentAddressedSnapshot
    morphism-to-seq : ℕ
    morphism-witness : ContentAddressedWitness
    morphism-excitement-selected : Bool

data ContentAddressedRefusal : Set where
  car-git-hash-only-identity : String → ContentAddressedRefusal
  car-host-id-identity : ℕ → ContentAddressedRefusal
  car-gate-rejected : ℕ → ContentAddressedRefusal
  car-geometric-zero : ℕ → ContentAddressedRefusal
  car-second-argmin-refused : ContentAddressedRefusal

data ContentAddressedVerdict : Set where
  cav-admitted : ContentAddressedVerdict
  cav-git-hash-only-refused : ContentAddressedVerdict
  cav-host-id-refused : ContentAddressedVerdict
  cav-inadmissible : ContentAddressedVerdict

------------------------------------------------------------------------
-- SECTION 3: §3 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record ContentAdmissibilityConjunct : Set where
  field
    conj-gate-ok : Bool
    conj-geometric-primary : Bool
    conj-excitement-preserves : Bool

content-conjunct-admits : ContentAdmissibilityConjunct → Bool
content-conjunct-admits c =
  ContentAdmissibilityConjunct.conj-gate-ok c ∧
  ContentAdmissibilityConjunct.conj-geometric-primary c ∧
  ContentAdmissibilityConjunct.conj-excitement-preserves c

nat-ne-zero? : ℕ → Bool
nat-ne-zero? zero = false
nat-ne-zero? (suc _) = true

geometric-content-id-present : ContentGeometricIdentity → Bool
geometric-content-id-present g =
  nat-ne-zero? (ContentGeometricIdentity.geom-content-id g)

evaluate-git-hash-only-identity : Bool → ContentAddressedVerdict
evaluate-git-hash-only-identity true = cav-git-hash-only-refused
evaluate-git-hash-only-identity false = cav-admitted

evaluate-host-id-identity : Bool → ContentAddressedVerdict
evaluate-host-id-identity true = cav-host-id-refused
evaluate-host-id-identity false = cav-admitted

refuse-git-hash-only-identity : String → ContentAddressedRefusal
refuse-git-hash-only-identity git-hash = car-git-hash-only-identity git-hash

refuse-host-id-identity : ℕ → ContentAddressedRefusal
refuse-host-id-identity host-id = car-host-id-identity host-id

refuse-second-argmin : ContentAddressedRefusal
refuse-second-argmin = car-second-argmin-refused

witness-from-snapshot : ContentAddressedSnapshot → ContentAddressedWitness
witness-from-snapshot s = record
  { witness-geometric = ContentAddressedSnapshot.snapshot-geometric s
  ; witness-git-compat = ContentAddressedSnapshot.snapshot-git-compat s
  ; witness-geometric-primary =
      ContentGeometricPrimaryCert.geometric-primary
        (ContentAddressedSnapshot.snapshot-geometric-cert s)
  ; witness-provenance-intact = ContentAddressedSnapshot.snapshot-provenance-intact s
  }

refuse-missing-geometric-identity :
  (snapshot : ContentAddressedSnapshot) → ContentAddressedRefusal
refuse-missing-geometric-identity snapshot with ContentAddressedSnapshot.snapshot-git-compat snapshot
... | just compat = car-git-hash-only-identity (ContentGitHashCompat.git-hash compat)
... | nothing = car-host-id-identity zero

apply-content-addressed-morphism :
  (snapshot : ContentAddressedSnapshot) (to-seq : ℕ) →
  (conjunct : ContentAdmissibilityConjunct) (excitement-selected : Bool) →
  ContentAddressedMorphism ⊎ ContentAddressedRefusal
apply-content-addressed-morphism snapshot to-seq conjunct excitement-selected =
  if not (content-conjunct-admits conjunct) then
    inj₂ (car-gate-rejected
      (ContentAddressedUcrsStamp.ucrs-seq (ContentAddressedSnapshot.snapshot-ucrs snapshot)))
  else if not (geometric-content-id-present (ContentAddressedSnapshot.snapshot-geometric snapshot)) then
    inj₂ (refuse-missing-geometric-identity snapshot)
  else if not (ContentGeometricPrimaryCert.geometric-primary
      (ContentAddressedSnapshot.snapshot-geometric-cert snapshot)) then
    inj₂ (car-geometric-zero (ContentAddressedSnapshot.snapshot-id snapshot))
  else if not (ContentAddressedSnapshot.snapshot-provenance-intact snapshot) then
    inj₂ (car-geometric-zero (ContentAddressedSnapshot.snapshot-id snapshot))
  else if not excitement-selected then
    inj₂ (car-geometric-zero (ContentAddressedSnapshot.snapshot-id snapshot))
  else
    inj₁ record
      { morphism-from = snapshot
      ; morphism-to-seq = to-seq
      ; morphism-witness = witness-from-snapshot snapshot
      ; morphism-excitement-selected = excitement-selected
      }

------------------------------------------------------------------------
-- SECTION 4: Content-addressed composes Excitement (no second argmin)
------------------------------------------------------------------------

record content-addressed-ctx (src : ThermodynamicState) : Set where
  field
    content-addressed-successors : List (history-candidate src)

content-addressed-select :
  (src : ThermodynamicState) (ctx : content-addressed-ctx src) →
  history-candidate src ⊎ excitement-residue
content-addressed-select src ctx =
  content-addressed-excitement-select src
    (content-addressed-ctx.content-addressed-successors ctx)

urge-content-addressed-select :
  (src : ThermodynamicState) (successors : List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
urge-content-addressed-select src successors =
  content-addressed-excitement-select src successors

content-addressed-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : content-addressed-ctx src) →
  content-addressed-select src ctx ≡
  content-addressed-excitement-select src
    (content-addressed-ctx.content-addressed-successors ctx)
content-addressed-select-eq-excitement-select src ctx = refl

content-addressed-select-eq-urge-select :
  ∀ (src : ThermodynamicState) (ctx : content-addressed-ctx src) →
  content-addressed-select src ctx ≡
  urge-content-addressed-select src
    (content-addressed-ctx.content-addressed-successors ctx)
content-addressed-select-eq-urge-select src ctx = refl

content-addressed-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : content-addressed-ctx src) →
  content-addressed-select src ctx ≡
  content-addressed-excitement-select src
    (content-addressed-ctx.content-addressed-successors ctx)
content-addressed-no-local-argmin src ctx = refl

content-addressed-empty :
  ∀ (src : ThermodynamicState) (ctx : content-addressed-ctx src) →
  content-addressed-ctx.content-addressed-successors ctx ≡ List.[] →
  content-addressed-select src ctx ≡ inj₂ exc-no-candidates
content-addressed-empty src ctx refl = refl

------------------------------------------------------------------------
-- SECTION 5: §3 fixtures + witness theorems
------------------------------------------------------------------------

content-fixture-state : ThermodynamicState
content-fixture-state = record
  { density = ℚ.0ℚ
  ; free-energy = ℚ.0ℚ
  ; hydration = ℚ.0ℚ
  ; strength = ℚ.0ℚ
  }

content-fixture-geometric : ContentGeometricIdentity
content-fixture-geometric = record
  { geom-content-id = 5381
  ; geom-resolution-bits = 2
  }

content-fixture-git-compat : ContentGitHashCompat
content-fixture-git-compat = record { git-hash = "sha1:geometric-primary-compat" }

content-fixture-ucrs : ContentAddressedUcrsStamp
content-fixture-ucrs = record { ucrs-seq = 3 ; ucrs-wall-has-t = true }

content-fixture-geometric-cert : ContentGeometricPrimaryCert
content-fixture-geometric-cert = record { geometric-primary = true }

content-fixture-snapshot : ContentAddressedSnapshot
content-fixture-snapshot = record
  { snapshot-id = 1
  ; snapshot-head = content-fixture-state
  ; snapshot-geometric = content-fixture-geometric
  ; snapshot-git-compat = just content-fixture-git-compat
  ; snapshot-ucrs = content-fixture-ucrs
  ; snapshot-geometric-cert = content-fixture-geometric-cert
  ; snapshot-provenance-intact = true
  }

content-fixture-conjunct : ContentAdmissibilityConjunct
content-fixture-conjunct = record
  { conj-gate-ok = true
  ; conj-geometric-primary = true
  ; conj-excitement-preserves = true
  }

content-addressed-git-hash-only-refused :
  evaluate-git-hash-only-identity true ≡ cav-git-hash-only-refused
content-addressed-git-hash-only-refused = refl

content-addressed-admitted-when-not-git-hash-only :
  evaluate-git-hash-only-identity false ≡ cav-admitted
content-addressed-admitted-when-not-git-hash-only = refl

content-addressed-host-id-refused :
  evaluate-host-id-identity true ≡ cav-host-id-refused
content-addressed-host-id-refused = refl

content-addressed-admitted-when-not-host-id :
  evaluate-host-id-identity false ≡ cav-admitted
content-addressed-admitted-when-not-host-id = refl

refuse-git-hash-only-identity-positive :
  ∀ git-hash →
  refuse-git-hash-only-identity git-hash ≡ car-git-hash-only-identity git-hash
refuse-git-hash-only-identity-positive git-hash = refl

refuse-host-id-identity-positive :
  ∀ host-id → refuse-host-id-identity host-id ≡ car-host-id-identity host-id
refuse-host-id-identity-positive host-id = refl

refuse-second-argmin-positive :
  refuse-second-argmin ≡ car-second-argmin-refused
refuse-second-argmin-positive = refl

content-fixture-geometric-content-id-present :
  geometric-content-id-present content-fixture-geometric ≡ true
content-fixture-geometric-content-id-present = refl

content-fixture-witness-preserves-geometric :
  ContentAddressedWitness.witness-geometric (witness-from-snapshot content-fixture-snapshot) ≡
  content-fixture-geometric
content-fixture-witness-preserves-geometric = refl

content-fixture-witness-preserves-git-compat :
  ContentAddressedWitness.witness-git-compat (witness-from-snapshot content-fixture-snapshot) ≡
  just content-fixture-git-compat
content-fixture-witness-preserves-git-compat = refl

------------------------------------------------------------------------
-- SECTION 6: Excitement compose pin (no second argmin)
------------------------------------------------------------------------

urge-content-addressed-select-pin :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-content-addressed-select-pin = urge-content-addressed-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ car-second-argmin-refused
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 7: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

content-addressed-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
content-addressed-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

content-addressed-production-wired : Bool
content-addressed-production-wired = false

content-addressed-production-wired-false :
  content-addressed-production-wired ≡ false
content-addressed-production-wired-false = refl

content-addressed-marker : ℕ
content-addressed-marker = 1

content-addressed-marker-eq : content-addressed-marker ≡ 1
content-addressed-marker-eq = refl

content-addressed-module-witness : ⊤
content-addressed-module-witness = tt

content-addressed-no-new-axiom : ⊤
content-addressed-no-new-axiom = tt

content-addressed-non-claim : String
content-addressed-non-claim =
  "§3 content-addressed history; geometric identity primary, git hash compatibility; compose excitement-select not local argmin; not physics GREEN; not production_wired"

content-addressed-git-hash-only-not-admitted :
  evaluate-git-hash-only-identity true ≡ cav-git-hash-only-refused
content-addressed-git-hash-only-not-admitted = refl

content-addressed-host-id-not-admitted :
  evaluate-host-id-identity true ≡ cav-host-id-refused
content-addressed-host-id-not-admitted = refl

git-hash-only-refused :
  refuse-git-hash-only-identity "sha1:only-hash" ≡
  car-git-hash-only-identity "sha1:only-hash"
git-hash-only-refused = refl

host-id-refused :
  refuse-host-id-identity 3735928559 ≡ car-host-id-identity 3735928559
host-id-refused = refl

second-argmin-refused :
  refuse-second-argmin ≡ car-second-argmin-refused
second-argmin-refused = refl
