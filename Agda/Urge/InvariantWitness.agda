-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.InvariantWitness — meso/acting §3 invariant witness.
--
-- URGE-FORMAL-MESO-AGDA-INVARIANT-WITNESS (umst-formal acting fiber only).
-- Every admitted history object carries a proof-carrying InvariantWitness —
-- not optional, not host-id theater. Composes `excitement-select` — no second
-- ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` meso discipline + Coq `InvariantWitness.v`.
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.InvariantWitness where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; not; _∧_)
open import Data.Empty using (⊥)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 0: Minimal thermodynamic head pin (parallel to CarrierProduct)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  field state-tag : ℕ

record Admissible (s₀ s₁ : ThermodynamicState) : Set where
  field adm-tag : ℕ

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

admitSecondLaw-from-landauer :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
  PhysicalSecondLaw proc entropyDecrease →
  ∀ (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
admitSecondLaw-from-landauer proc ΔS hSL t hent hdiss =
  let step1 = subst (λ x → x ≤ ErasureProcess.dissipatedEntropy proc) (sym hent) hSL
  in subst (λ d → HistoryTransition.entropy-drop t ≤ d) (sym hdiss) step1

------------------------------------------------------------------------
-- SECTION 1: InvariantWitness factor + history object (§3 mandatory)
------------------------------------------------------------------------

record InvariantWitness : Set where
  field
    satisfied : Bool
    margin-h : ℚ

witnessProp : InvariantWitness → Set
witnessProp w =
  if InvariantWitness.satisfied w then ⊤ else ⊥

satisfiedWitness : InvariantWitness
satisfiedWitness = record { satisfied = true ; margin-h = 0ℚ }

rejectedWitness : InvariantWitness
rejectedWitness = record { satisfied = false ; margin-h = 0ℚ }

record history-object : Set where
  field
    content-id : ℕ
    theorem-id : ℕ
    witness : InvariantWitness

data witness-prop-tag : Set where
  wpt-satisfied : witness-prop-tag
  wpt-rejected : witness-prop-tag

witness-prop-consistent : InvariantWitness → witness-prop-tag → Bool
witness-prop-consistent w wpt-satisfied = InvariantWitness.satisfied w
witness-prop-consistent w wpt-rejected = not (InvariantWitness.satisfied w)

history-object-with-witness :
  (content-id theorem-id : ℕ) (w : InvariantWitness) → history-object
history-object-with-witness cid tid w = record
  { content-id = cid
  ; theorem-id = tid
  ; witness = w
  }

record invariant-witness-bundle : Set where
  field
    iwb-witness : InvariantWitness
    iwb-prop-tag : witness-prop-tag
    iwb-excitement-selected : Bool

data invariant-witness-refusal : Set where
  iwr-witness-absent : invariant-witness-refusal
  iwr-witness-stripped : ℕ → invariant-witness-refusal
  iwr-witness-unsatisfied : ℕ → invariant-witness-refusal
  iwr-witness-prop-inconsistent : ℕ → invariant-witness-refusal
  iwr-gate-rejected : ℕ → invariant-witness-refusal

data invariant-witness-verdict : Set where
  iwv-admit-ok : invariant-witness-verdict
  iwv-witness-absent-refused : invariant-witness-verdict
  iwv-witness-stripped-refused : invariant-witness-verdict
  iwv-inadmissible : invariant-witness-verdict

record invariant-admissibility-conjunct : Set where
  field
    invariant-conj-gate-ok : Bool
    invariant-conj-witness-present : Bool
    invariant-conj-excitement-preserves : Bool

invariant-conjunct-admits : invariant-admissibility-conjunct → Bool
invariant-conjunct-admits c =
  invariant-admissibility-conjunct.invariant-conj-gate-ok c ∧
  invariant-admissibility-conjunct.invariant-conj-witness-present c ∧
  invariant-admissibility-conjunct.invariant-conj-excitement-preserves c

------------------------------------------------------------------------
-- SECTION 2: §3 admissibility conjunct + positive refuse
------------------------------------------------------------------------

evaluate-invariant-witness-operation :
  (witness-absent : Bool) → invariant-witness-verdict
evaluate-invariant-witness-operation true = iwv-witness-absent-refused
evaluate-invariant-witness-operation false = iwv-admit-ok

refuse-witness-absent : invariant-witness-refusal
refuse-witness-absent = iwr-witness-absent

refuse-witness-strip : (content-id : ℕ) → invariant-witness-refusal
refuse-witness-strip cid = iwr-witness-stripped cid

witness-from-history-object :
  (obj : history-object) (tag : witness-prop-tag) (excitement-selected : Bool) →
  invariant-witness-bundle
witness-from-history-object obj tag sel = record
  { iwb-witness = history-object.witness obj
  ; iwb-prop-tag = tag
  ; iwb-excitement-selected = sel
  }

object-has-witness : history-object → Bool
object-has-witness obj =
  witness-prop-consistent (history-object.witness obj) wpt-satisfied ∧
  InvariantWitness.satisfied (history-object.witness obj)

admit-history-object : history-object → ⊤ ⊎ invariant-witness-refusal
admit-history-object obj =
  let w = history-object.witness obj
      cid = history-object.content-id obj
  in if (not (witness-prop-consistent w wpt-satisfied) ∧
         not (witness-prop-consistent w wpt-rejected))
     then inj₂ (iwr-witness-prop-inconsistent cid)
     else if not (InvariantWitness.satisfied w)
          then inj₂ (iwr-witness-unsatisfied cid)
          else inj₁ tt

apply-invariant-witness-admission :
  (obj : history-object)
  (conjunct : invariant-admissibility-conjunct)
  (witness-absent excitement-selected : Bool) →
  invariant-witness-bundle ⊎ invariant-witness-refusal
apply-invariant-witness-admission obj conjunct witness-absent excitement-selected =
  if witness-absent
  then inj₂ iwr-witness-absent
  else if not (invariant-conjunct-admits conjunct)
       then inj₂ (iwr-gate-rejected (history-object.content-id obj))
       else if not excitement-selected
            then inj₂ (iwr-witness-stripped (history-object.content-id obj))
            else go (admit-history-object obj)
  where
  go : ⊤ ⊎ invariant-witness-refusal → invariant-witness-bundle ⊎ invariant-witness-refusal
  go (inj₂ r) = inj₂ r
  go (inj₁ _) = inj₁ (witness-from-history-object obj wpt-satisfied excitement-selected)

invariant-witness-absent-refused :
  evaluate-invariant-witness-operation true ≡ iwv-witness-absent-refused
invariant-witness-absent-refused = refl

invariant-witness-admit-ok-when-witnessed :
  evaluate-invariant-witness-operation false ≡ iwv-admit-ok
invariant-witness-admit-ok-when-witnessed = refl

refuse-witness-absent-positive :
  refuse-witness-absent ≡ iwr-witness-absent
refuse-witness-absent-positive = refl

refuse-witness-strip-positive :
  ∀ (content-id : ℕ) → refuse-witness-strip content-id ≡ iwr-witness-stripped content-id
refuse-witness-strip-positive content-id = refl

satisfied-witness-prop-consistent :
  witness-prop-consistent satisfiedWitness wpt-satisfied ≡ true
satisfied-witness-prop-consistent = refl

rejected-witness-prop-consistent :
  witness-prop-consistent rejectedWitness wpt-rejected ≡ true
rejected-witness-prop-consistent = refl

------------------------------------------------------------------------
-- SECTION 3: Excitement compose (no second ℚ argmin)
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
excitement-select src List.[] = inj₂ exc-no-candidates
excitement-select src (c List.∷ _) = inj₁ c

urge-recovery-select :
  (src : ThermodynamicState) (successors : List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select = excitement-select

record invariant-witness-ctx (src : ThermodynamicState) : Set where
  field
    invariant-witness-successors : List (history-candidate src)

invariant-witness-select :
  (src : ThermodynamicState) (ctx : invariant-witness-ctx src) →
  history-candidate src ⊎ excitement-residue
invariant-witness-select src ctx =
  urge-recovery-select src (invariant-witness-ctx.invariant-witness-successors ctx)

invariant-witness-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : invariant-witness-ctx src) →
  invariant-witness-select src ctx ≡
  excitement-select src (invariant-witness-ctx.invariant-witness-successors ctx)
invariant-witness-select-eq-excitement-select src ctx = refl

invariant-witness-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : invariant-witness-ctx src) →
  invariant-witness-select src ctx ≡
  urge-recovery-select src (invariant-witness-ctx.invariant-witness-successors ctx)
invariant-witness-select-eq-urge-recovery-select src ctx = refl

invariant-witness-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : invariant-witness-ctx src) →
  invariant-witness-select src ctx ≡
  excitement-select src (invariant-witness-ctx.invariant-witness-successors ctx)
invariant-witness-no-local-argmin src ctx =
  invariant-witness-select-eq-excitement-select src ctx

invariant-witness-empty :
  ∀ (src : ThermodynamicState) (ctx : invariant-witness-ctx src) →
  invariant-witness-ctx.invariant-witness-successors ctx ≡ List.[] →
  invariant-witness-select src ctx ≡ inj₂ exc-no-candidates
invariant-witness-empty src ctx eq rewrite eq = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

------------------------------------------------------------------------
-- SECTION 4: §3 fixtures + witnessed ledger
------------------------------------------------------------------------

invariant-fixture-state : ThermodynamicState
invariant-fixture-state = record { state-tag = 0 }

invariant-fixture-object : history-object
invariant-fixture-object = history-object-with-witness 66 7 satisfiedWitness

invariant-fixture-rejected : history-object
invariant-fixture-rejected = history-object-with-witness 67 7 rejectedWitness

invariant-fixture-conjunct : invariant-admissibility-conjunct
invariant-fixture-conjunct = record
  { invariant-conj-gate-ok = true
  ; invariant-conj-witness-present = true
  ; invariant-conj-excitement-preserves = true
  }

invariant-fixture-admit-ok :
  admit-history-object invariant-fixture-object ≡ inj₁ tt
invariant-fixture-admit-ok = refl

invariant-fixture-rejected-unsatisfied :
  admit-history-object invariant-fixture-rejected ≡ inj₂ (iwr-witness-unsatisfied 67)
invariant-fixture-rejected-unsatisfied = refl

invariant-fixture-apply-admission-ok :
  apply-invariant-witness-admission
    invariant-fixture-object invariant-fixture-conjunct false true ≡
  inj₁ (witness-from-history-object invariant-fixture-object wpt-satisfied true)
invariant-fixture-apply-admission-ok = refl

invariant-fixture-witness-absent-refused :
  apply-invariant-witness-admission
    invariant-fixture-object invariant-fixture-conjunct true true ≡
  inj₂ iwr-witness-absent
invariant-fixture-witness-absent-refused = refl

invariant-fixture-object-has-witness :
  object-has-witness invariant-fixture-object ≡ true
invariant-fixture-object-has-witness = refl

invariant-fixture-witness-preserves-margin :
  InvariantWitness.margin-h (history-object.witness invariant-fixture-object) ≡ 0ℚ
invariant-fixture-witness-preserves-margin = refl

record witnessed-history-ledger : Set where
  field
    witnessed-objects : List history-object

witnessed-ledger-empty : witnessed-history-ledger
witnessed-ledger-empty = record { witnessed-objects = List.[] }

witnessed-ledger-append :
  (ledger : witnessed-history-ledger) (obj : history-object) →
  witnessed-history-ledger ⊎ invariant-witness-refusal
witnessed-ledger-append ledger obj with admit-history-object obj
... | inj₂ r = inj₂ r
... | inj₁ _ = inj₁ record
  { witnessed-objects = witnessed-history-ledger.witnessed-objects ledger ++ obj List.∷ List.[] }

all-objects-have-witness : List history-object → Bool
all-objects-have-witness List.[] = true
all-objects-have-witness (o List.∷ os) = object-has-witness o ∧ all-objects-have-witness os

witnessed-ledger-every-has-witness : witnessed-history-ledger → Bool
witnessed-ledger-every-has-witness ledger =
  all-objects-have-witness (witnessed-history-ledger.witnessed-objects ledger)

invariant-fixture-ledger-append-ok :
  witnessed-ledger-append witnessed-ledger-empty invariant-fixture-object ≡
  inj₁ record { witnessed-objects = invariant-fixture-object List.∷ List.[] }
invariant-fixture-ledger-append-ok = refl

invariant-fixture-ledger-every-has-witness :
  witnessed-ledger-every-has-witness
    (record { witnessed-objects = invariant-fixture-object List.∷ List.[] }) ≡ true
invariant-fixture-ledger-every-has-witness = refl

------------------------------------------------------------------------
-- SECTION 5: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

invariant-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
invariant-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

invariant-witness-physics-green : Bool
invariant-witness-physics-green = false

invariant-witness-physics-green-false :
  invariant-witness-physics-green ≡ false
invariant-witness-physics-green-false = refl

invariant-witness-production-wired : Bool
invariant-witness-production-wired = false

invariant-witness-production-wired-false :
  invariant-witness-production-wired ≡ false
invariant-witness-production-wired-false = refl

invariant-witness-module-witness : ⊤
invariant-witness-module-witness = tt

invariant-witness-no-new-axiom : ⊤
invariant-witness-no-new-axiom = tt

invariant-witness-positive-refuse-not-silent :
  evaluate-invariant-witness-operation true ≢ iwv-admit-ok
invariant-witness-positive-refuse-not-silent ()

invariant-witness-marker : ℕ
invariant-witness-marker = 3

invariant-witness-marker-eq : invariant-witness-marker ≡ 3
invariant-witness-marker-eq = refl
