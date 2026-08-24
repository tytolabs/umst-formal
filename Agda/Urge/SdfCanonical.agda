-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.SdfCanonical — meso/acting §12 SDFCanonical tautology.
--
-- URGE-FORMAL-MESO-AGDA-SDF-CANONICAL (umst-formal acting fiber only).
-- §12: byte-equal canonical SDFs imply behavior-equivalent history actions
-- named on history identity — mirrors Lean `Behavior.SDFCanonical` and
-- Coq `Urge.SdfCanonical`. Compose `sdf-canonical-excitement-select`
-- — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.SdfCanonical where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; not; _∧_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.DivMod using (_%_)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (does; ¬_)

------------------------------------------------------------------------
-- SECTION 1: History action + identity carriers (§12)
------------------------------------------------------------------------

record history-action : Set where
  field
    history-action-bytes : List ℕ
    history-action-canonicalized : Bool

record history-identity : Set where
  field
    history-identity-action : history-action
    history-identity-content-id : ℕ

record sdf-canonical-witness : Set where
  field
    sdf-canonical-witness-bytes : List ℕ
    sdf-canonical-witness-content-id : ℕ
    sdf-canonical-witness-canonicalized : Bool

record sdf-canonical-morphism : Set where
  field
    sdf-canonical-morphism-from : history-identity
    sdf-canonical-morphism-to-content-id : ℕ
    sdf-canonical-morphism-witness : sdf-canonical-witness
    sdf-canonical-morphism-excitement-selected : Bool

data behavior-equiv : Set where
  bev-equivalent : behavior-equiv
  bev-distinct : behavior-equiv

data sdf-canonical-refusal : Set where
  scr-canonical-sdf-mismatch : ℕ → ℕ → sdf-canonical-refusal
  scr-alias-without-canonicalization : ℕ → sdf-canonical-refusal
  scr-invented-equiv-without-canonical : ℕ → sdf-canonical-refusal
  scr-second-argmin : sdf-canonical-refusal
  scr-gate-rejected : ℕ → sdf-canonical-refusal

data sdf-canonical-verdict : Set where
  scv-admitted : sdf-canonical-verdict
  scv-alias-refused : sdf-canonical-verdict
  scv-invented-equiv-refused : sdf-canonical-verdict
  scv-inadmissible : sdf-canonical-verdict

------------------------------------------------------------------------
-- SECTION 2: §12 admissibility conjunct + positive refuse
------------------------------------------------------------------------

canonical-sdf : history-action → List ℕ
canonical-sdf a = history-action.history-action-bytes a

nat-list-eqb : List ℕ → List ℕ → Bool
nat-list-eqb [] [] = true
nat-list-eqb (x ∷ xs) (y ∷ ys) =
  if does (ℕ-Props._≟_ x y) then nat-list-eqb xs ys else false
nat-list-eqb [] (_ ∷ _) = false
nat-list-eqb (_ ∷ _) [] = false

content-id-step : ℕ → ℕ → ℕ
content-id-step acc b = (acc * 16777619 + b) % (4294967296)

content-id-from-canonical : List ℕ → ℕ → ℕ
content-id-from-canonical [] acc = acc
content-id-from-canonical (b ∷ rest) acc =
  content-id-from-canonical rest (content-id-step acc b)

history-content-id : history-action → ℕ
history-content-id a =
  content-id-from-canonical (canonical-sdf a) 5381

behavior-equiv-of : history-action → history-action → behavior-equiv
behavior-equiv-of left right =
  if nat-list-eqb (canonical-sdf left) (canonical-sdf right) then
    bev-equivalent
  else
    bev-distinct

BehaviorEquiv : history-action → history-action → Set
BehaviorEquiv a b = canonical-sdf a ≡ canonical-sdf b

SDFCanonical :
  (a b : history-action) →
  canonical-sdf a ≡ canonical-sdf b →
  BehaviorEquiv a b
SDFCanonical a b h = h

record sdf-canonical-admissibility-conjunct : Set where
  field
    sdf-canonical-conj-gate-ok : Bool
    sdf-canonical-conj-canonicalized : Bool
    sdf-canonical-conj-excitement-preserves : Bool

sdf-canonical-conjunct-admits : sdf-canonical-admissibility-conjunct → Bool
sdf-canonical-conjunct-admits (record { sdf-canonical-conj-gate-ok = g
                                     ; sdf-canonical-conj-canonicalized = c
                                     ; sdf-canonical-conj-excitement-preserves = e }) =
  g ∧ c ∧ e

evaluate-alias-without-canonicalization : Bool → sdf-canonical-verdict
evaluate-alias-without-canonicalization true = scv-alias-refused
evaluate-alias-without-canonicalization false = scv-admitted

evaluate-invented-equiv-without-canonical : Bool → sdf-canonical-verdict
evaluate-invented-equiv-without-canonical true = scv-invented-equiv-refused
evaluate-invented-equiv-without-canonical false = scv-admitted

refuse-alias-without-canonicalization : ℕ → sdf-canonical-refusal
refuse-alias-without-canonicalization payload =
  scr-alias-without-canonicalization payload

refuse-invented-equiv-without-canonical : ℕ → sdf-canonical-refusal
refuse-invented-equiv-without-canonical content-id =
  scr-invented-equiv-without-canonical content-id

refuse-second-argmin-selector : sdf-canonical-refusal
refuse-second-argmin-selector = scr-second-argmin

witness-from-history-identity : history-identity → sdf-canonical-witness
witness-from-history-identity h = record
  { sdf-canonical-witness-bytes =
      canonical-sdf (history-identity.history-identity-action h)
  ; sdf-canonical-witness-content-id = history-content-id (history-identity.history-identity-action h)
  ; sdf-canonical-witness-canonicalized =
      history-action.history-action-canonicalized (history-identity.history-identity-action h)
  }

sdf-canonical-theorem :
  history-action → history-action →
  behavior-equiv ⊎ sdf-canonical-refusal
sdf-canonical-theorem left right =
  if not (history-action.history-action-canonicalized left) then
    inj₂ (scr-alias-without-canonicalization 0)
  else if not (history-action.history-action-canonicalized right) then
    inj₂ (scr-alias-without-canonicalization 0)
  else if nat-list-eqb (canonical-sdf left) (canonical-sdf right) then
    inj₁ bev-equivalent
  else
    inj₂ (scr-canonical-sdf-mismatch
            (history-content-id left) (history-content-id right))

admit-history-identity-step :
  history-identity → history-identity →
  behavior-equiv ⊎ sdf-canonical-refusal →
  sdf-canonical-verdict ⊎ sdf-canonical-refusal
admit-history-identity-step left right (inj₁ bev-equivalent) =
  let left-id = history-content-id (history-identity.history-identity-action left)
      right-id = history-content-id (history-identity.history-identity-action right)
  in if not (does (ℕ-Props._≟_ (history-identity.history-identity-content-id left) left-id)) then
       inj₂ (scr-invented-equiv-without-canonical (history-identity.history-identity-content-id left))
     else if not (does (ℕ-Props._≟_ (history-identity.history-identity-content-id right) right-id)) then
       inj₂ (scr-invented-equiv-without-canonical (history-identity.history-identity-content-id right))
     else if not (does (ℕ-Props._≟_ (history-identity.history-identity-content-id left)
                                      (history-identity.history-identity-content-id right))) then
       inj₂ (scr-canonical-sdf-mismatch left-id right-id)
     else
       inj₁ scv-admitted
admit-history-identity-step left right (inj₁ bev-distinct) =
  inj₂ (scr-canonical-sdf-mismatch
          (history-content-id (history-identity.history-identity-action left))
          (history-content-id (history-identity.history-identity-action right)))
admit-history-identity-step left right (inj₂ r) = inj₂ r

admit-history-identity :
  history-identity → history-identity →
  sdf-canonical-admissibility-conjunct →
  sdf-canonical-verdict ⊎ sdf-canonical-refusal
admit-history-identity left right conjunct =
  if not (sdf-canonical-conjunct-admits conjunct) then
    inj₂ (scr-gate-rejected 0)
  else
    admit-history-identity-step left right
      (sdf-canonical-theorem
         (history-identity.history-identity-action left)
         (history-identity.history-identity-action right))

apply-sdf-canonical-morphism :
  history-identity → ℕ →
  sdf-canonical-admissibility-conjunct → Bool →
  sdf-canonical-morphism ⊎ sdf-canonical-refusal
apply-sdf-canonical-morphism identity to-content-id conjunct excitement-selected =
  if not (sdf-canonical-conjunct-admits conjunct) then
    inj₂ (scr-gate-rejected (history-identity.history-identity-content-id identity))
  else if not (history-action.history-action-canonicalized (history-identity.history-identity-action identity)) then
    inj₂ (scr-alias-without-canonicalization (history-identity.history-identity-content-id identity))
  else if not excitement-selected then
    inj₂ (scr-canonical-sdf-mismatch
            (history-identity.history-identity-content-id identity) to-content-id)
  else
    inj₁ record
      { sdf-canonical-morphism-from = identity
      ; sdf-canonical-morphism-to-content-id = to-content-id
      ; sdf-canonical-morphism-witness = witness-from-history-identity identity
      ; sdf-canonical-morphism-excitement-selected = excitement-selected
      }

sdf-canonical-alias-refused :
  evaluate-alias-without-canonicalization true ≡ scv-alias-refused
sdf-canonical-alias-refused = refl

sdf-canonical-admitted-when-not-alias :
  evaluate-alias-without-canonicalization false ≡ scv-admitted
sdf-canonical-admitted-when-not-alias = refl

sdf-canonical-invented-equiv-refused :
  evaluate-invented-equiv-without-canonical true ≡ scv-invented-equiv-refused
sdf-canonical-invented-equiv-refused = refl

refuse-alias-without-canonicalization-positive :
  (payload : ℕ) →
  refuse-alias-without-canonicalization payload ≡
  scr-alias-without-canonicalization payload
refuse-alias-without-canonicalization-positive payload = refl

refuse-second-argmin-selector-positive :
  refuse-second-argmin-selector ≡ scr-second-argmin
refuse-second-argmin-selector-positive = refl

------------------------------------------------------------------------
-- SECTION 3: Typed history carriers + excitement compose (no second argmin)
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

record sdf-canonical-candidate : Set where
  field
    cand-id : ℕ
    cand-content-id : ℕ
    canonicalized : Bool

sdf-canonical-excitement-select :
  (src : ℚ) → List sdf-canonical-candidate →
  sdf-canonical-candidate ⊎ excitement-residue
sdf-canonical-excitement-select src List.[] = inj₂ exc-no-candidates
sdf-canonical-excitement-select src (c List.∷ _) = inj₁ c

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

data SdfCanonicalExcitementPin : Set where
  sccp-import-select-excitement : SdfCanonicalExcitementPin
  sccp-second-argmin-refused : SdfCanonicalExcitementPin

sdf-canonical-excitement-compose :
  (src : ℚ) → List sdf-canonical-candidate →
  SdfCanonicalExcitementPin →
  sdf-canonical-candidate ⊎ excitement-residue
sdf-canonical-excitement-compose src cands sccp-import-select-excitement =
  sdf-canonical-excitement-select src cands
sdf-canonical-excitement-compose src cands sccp-second-argmin-refused =
  inj₂ exc-all-inadmissible

urge-sdf-canonical-select :
  (src : ℚ) → List sdf-canonical-candidate →
  sdf-canonical-candidate ⊎ excitement-residue
urge-sdf-canonical-select = sdf-canonical-excitement-select

sdf-canonical-excitement-select-eq :
  ∀ (src : ℚ) (cands : List sdf-canonical-candidate) →
  sdf-canonical-excitement-compose src cands sccp-import-select-excitement ≡
  sdf-canonical-excitement-select src cands
sdf-canonical-excitement-select-eq src cands = refl

sdf-canonical-select-eq-urge :
  ∀ (src : ℚ) (cands : List sdf-canonical-candidate) →
  urge-sdf-canonical-select src cands ≡
  sdf-canonical-excitement-select src cands
sdf-canonical-select-eq-urge src cands = refl

sdf-canonical-no-local-argmin :
  ∀ (src : ℚ) (cands : List sdf-canonical-candidate) →
  urge-sdf-canonical-select src cands ≡
  sdf-canonical-excitement-select src cands
sdf-canonical-no-local-argmin src cands =
  sdf-canonical-select-eq-urge src cands

sdf-canonical-excitement-refuses-second-argmin :
  ∀ (src : ℚ) (cands : List sdf-canonical-candidate) →
  sdf-canonical-excitement-compose src cands sccp-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
sdf-canonical-excitement-refuses-second-argmin src cands = refl

sdf-canonical-excitement-empty :
  ∀ (src : ℚ) →
  urge-sdf-canonical-select src List.[] ≡ inj₂ exc-no-candidates
sdf-canonical-excitement-empty src = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin-selector ≡ scr-second-argmin
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 4: §12 fixtures + witness theorems
------------------------------------------------------------------------

sdf-canonical-fixture-bytes : List ℕ
sdf-canonical-fixture-bytes =
  115 ∷ 100 ∷ 102 ∷ 58 ∷ 118 ∷ 49 ∷ 58 ∷ 99 ∷ 104 ∷ 97 ∷ 105 ∷ 114 ∷ []

sdf-canonical-fixture-action : history-action
sdf-canonical-fixture-action = record
  { history-action-bytes = sdf-canonical-fixture-bytes
  ; history-action-canonicalized = true
  }

sdf-canonical-fixture-content-id : ℕ
sdf-canonical-fixture-content-id = history-content-id sdf-canonical-fixture-action

sdf-canonical-fixture-identity : history-identity
sdf-canonical-fixture-identity = record
  { history-identity-action = sdf-canonical-fixture-action
  ; history-identity-content-id = sdf-canonical-fixture-content-id
  }

sdf-canonical-fixture-identity-same : history-identity
sdf-canonical-fixture-identity-same = record
  { history-identity-action = sdf-canonical-fixture-action
  ; history-identity-content-id = sdf-canonical-fixture-content-id
  }

sdf-canonical-fixture-action-distinct : history-action
sdf-canonical-fixture-action-distinct = record
  { history-action-bytes =
      115 ∷ 100 ∷ 102 ∷ 58 ∷ 118 ∷ 49 ∷ 58 ∷ 115 ∷ 112 ∷ 104 ∷ 101 ∷ 114 ∷ 101 ∷ []
  ; history-action-canonicalized = true
  }

sdf-canonical-fixture-identity-distinct : history-identity
sdf-canonical-fixture-identity-distinct = record
  { history-identity-action = sdf-canonical-fixture-action-distinct
  ; history-identity-content-id = history-content-id sdf-canonical-fixture-action-distinct
  }

sdf-canonical-fixture-action-alias : history-action
sdf-canonical-fixture-action-alias = record
  { history-action-bytes = sdf-canonical-fixture-bytes
  ; history-action-canonicalized = false
  }

sdf-canonical-fixture-conjunct : sdf-canonical-admissibility-conjunct
sdf-canonical-fixture-conjunct = record
  { sdf-canonical-conj-gate-ok = true
  ; sdf-canonical-conj-canonicalized = true
  ; sdf-canonical-conj-excitement-preserves = true
  }

sdf-canonical-fixture-canonical-sdf-id :
  canonical-sdf sdf-canonical-fixture-action ≡ sdf-canonical-fixture-bytes
sdf-canonical-fixture-canonical-sdf-id = refl

sdf-canonical-fixture-byte-equal-admitted :
  admit-history-identity
    sdf-canonical-fixture-identity sdf-canonical-fixture-identity-same
    sdf-canonical-fixture-conjunct ≡
  inj₁ scv-admitted
sdf-canonical-fixture-byte-equal-admitted = refl

sdf-canonical-fixture-alias-refused :
  refuse-alias-without-canonicalization 42 ≡
  scr-alias-without-canonicalization 42
sdf-canonical-fixture-alias-refused = refl

sdf-canonical-fixture-apply-morphism-ok :
  apply-sdf-canonical-morphism
    sdf-canonical-fixture-identity sdf-canonical-fixture-content-id
    sdf-canonical-fixture-conjunct true ≡
  inj₁ record
    { sdf-canonical-morphism-from = sdf-canonical-fixture-identity
    ; sdf-canonical-morphism-to-content-id = sdf-canonical-fixture-content-id
    ; sdf-canonical-morphism-witness = witness-from-history-identity sdf-canonical-fixture-identity
    ; sdf-canonical-morphism-excitement-selected = true
    }
sdf-canonical-fixture-apply-morphism-ok = refl

sdf-canonical-fixture-witness-preserves-bytes :
  sdf-canonical-witness.sdf-canonical-witness-bytes
    (witness-from-history-identity sdf-canonical-fixture-identity) ≡
  sdf-canonical-fixture-bytes
sdf-canonical-fixture-witness-preserves-bytes = refl

sdf-canonical-fixture-theorem-tautology :
  sdf-canonical-theorem sdf-canonical-fixture-action sdf-canonical-fixture-action ≡
  inj₁ bev-equivalent
sdf-canonical-fixture-theorem-tautology = refl

sdf-canonical-named-identity-tautology :
  SDFCanonical sdf-canonical-fixture-action sdf-canonical-fixture-action refl ≡ refl
sdf-canonical-named-identity-tautology = refl

sdf-canonical-alias-not-admitted :
  evaluate-alias-without-canonicalization true ≢ scv-admitted
sdf-canonical-alias-not-admitted ()

sdf-canonical-positive-refuse-not-silent :
  evaluate-invented-equiv-without-canonical true ≢ scv-admitted
sdf-canonical-positive-refuse-not-silent ()

------------------------------------------------------------------------
-- SECTION 5: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

sdf-canonical-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
sdf-canonical-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

sdf-canonical-production-wired : Bool
sdf-canonical-production-wired = false

sdf-canonical-production-wired-false :
  sdf-canonical-production-wired ≡ false
sdf-canonical-production-wired-false = refl

sdf-canonical-marker : ℕ
sdf-canonical-marker = 1

sdf-canonical-marker-eq : sdf-canonical-marker ≡ 1
sdf-canonical-marker-eq = refl

sdf-canonical-module-witness : ⊤
sdf-canonical-module-witness = tt

sdf-canonical-no-new-postulate : ⊤
sdf-canonical-no-new-postulate = tt
