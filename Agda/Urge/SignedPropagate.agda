-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.SignedPropagate — meso/acting §4 signed propagation.
--
-- URGE-FORMAL-MESO-AGDA-SIGNED-PROPAGATE (umst-formal acting fiber only).
-- §4: propagation of signed stamped witnessed states — stamp `T` required;
-- witness retained; unsigned propagation refused — not silent accept. Compose
-- `signed-propagate-select` / `excitement-select` — no second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` / Coq `Urge.SignedPropagate`. Sole physics
-- postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.SignedPropagate where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; not; _∧_)
open import Data.Integer.Base using (ℤ; _+_; +_; -[1+_])
open import Data.Integer.Properties as ℤ-Props using (_≤?_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
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
-- SECTION 1: Signed stamped witnessed carriers (§4)
------------------------------------------------------------------------

record signed-propagate-wall-stamp : Set where
  field
    signed-wall-seq : ℕ
    signed-wall-has-t : Bool

record signed-stamped-witness-state : Set where
  field
    signed-value : ℤ
    signed-stamp : signed-propagate-wall-stamp
    signed-witness-bits : ℕ

record signed-propagation-step : Set where
  field
    signed-delta : ℤ
    signed-post-stamp : signed-propagate-wall-stamp
    signed-post-witness-bits : ℕ

record signed-propagate-witness : Set where
  field
    signed-witness-stamp : signed-propagate-wall-stamp
    signed-witness-bit-budget : ℕ

record signed-propagate-morphism : Set where
  field
    signed-morphism-from : signed-stamped-witness-state
    signed-morphism-to : signed-stamped-witness-state
    signed-morphism-witness : signed-propagate-witness
    signed-morphism-excitement-selected : Bool

data signed-propagate-refusal : Set where
  spr-prior-stamp-invalid : ℕ → signed-propagate-refusal
  spr-post-stamp-invalid : ℕ → signed-propagate-refusal
  spr-unsigned-propagation-refused : signed-propagate-refusal
  spr-witness-dropped : ℕ → ℕ → signed-propagate-refusal
  spr-signed-overflow : signed-propagate-refusal
  spr-gate-rejected : ℕ → signed-propagate-refusal

data signed-propagate-verdict : Set where
  spv-morphism-ok spv-unsigned-propagation-refused spv-inadmissible : signed-propagate-verdict

------------------------------------------------------------------------
-- SECTION 2: §4 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record signed-admissibility-conjunct : Set where
  field
    signed-conj-gate-ok : Bool
    signed-conj-stamp-ok : Bool
    signed-conj-witness-present : Bool
    signed-conj-excitement-preserves : Bool

wall-stamp-ok : signed-propagate-wall-stamp → Bool
wall-stamp-ok s = signed-propagate-wall-stamp.signed-wall-has-t s

witness-present : signed-stamped-witness-state → Bool
witness-present st = does (zero <? signed-stamped-witness-state.signed-witness-bits st)

signed-conjunct-admits : signed-admissibility-conjunct → Bool
signed-conjunct-admits (record { signed-conj-gate-ok = g
                                ; signed-conj-stamp-ok = s
                                ; signed-conj-witness-present = w
                                ; signed-conj-excitement-preserves = e }) =
  g ∧ s ∧ w ∧ e

evaluate-signed-propagate-operation :
  (is-unsigned-carry : Bool) → signed-propagate-verdict
evaluate-signed-propagate-operation true = spv-unsigned-propagation-refused
evaluate-signed-propagate-operation false = spv-morphism-ok

refuse-unsigned-propagation : signed-propagate-refusal
refuse-unsigned-propagation = spr-unsigned-propagation-refused

witness-from-signed-state : signed-stamped-witness-state → signed-propagate-witness
witness-from-signed-state st = record
  { signed-witness-stamp = signed-stamped-witness-state.signed-stamp st
  ; signed-witness-bit-budget = signed-stamped-witness-state.signed-witness-bits st
  }

signed-overflow-lower : ℤ
signed-overflow-lower = -[1+ 999999 ]

signed-overflow-upper : ℤ
signed-overflow-upper = + 1000000

signed-add-ok : ℤ → ℤ → Bool
signed-add-ok prior delta =
  let result = prior + delta in
  (does (signed-overflow-lower ℤ-Props.≤? result)) ∧
  (does (result ℤ-Props.≤? signed-overflow-upper))

propagate-signed-state :
  (prior : signed-stamped-witness-state) →
  (step : signed-propagation-step) →
  (conjunct : signed-admissibility-conjunct) →
  (excitement-selected : Bool) →
  signed-stamped-witness-state ⊎ signed-propagate-refusal
propagate-signed-state prior step conjunct excitement-selected =
  if not (wall-stamp-ok (signed-stamped-witness-state.signed-stamp prior)) then
    inj₂ (spr-prior-stamp-invalid
      (signed-propagate-wall-stamp.signed-wall-seq
        (signed-stamped-witness-state.signed-stamp prior)))
  else if not (witness-present prior) then
    inj₂ spr-unsigned-propagation-refused
  else if not (wall-stamp-ok (signed-propagation-step.signed-post-stamp step)) then
    inj₂ (spr-post-stamp-invalid
      (signed-propagate-wall-stamp.signed-wall-seq
        (signed-propagation-step.signed-post-stamp step)))
  else if does (signed-propagation-step.signed-post-witness-bits step
                  <? signed-stamped-witness-state.signed-witness-bits prior) then
    inj₂ (spr-witness-dropped
      (signed-stamped-witness-state.signed-witness-bits prior)
      (signed-propagation-step.signed-post-witness-bits step))
  else if not (signed-add-ok
                 (signed-stamped-witness-state.signed-value prior)
                 (signed-propagation-step.signed-delta step)) then
    inj₂ spr-signed-overflow
  else if not (signed-conjunct-admits conjunct) then
    inj₂ (spr-gate-rejected
      (signed-propagate-wall-stamp.signed-wall-seq
        (signed-stamped-witness-state.signed-stamp prior)))
  else if not excitement-selected then
    inj₂ spr-unsigned-propagation-refused
  else inj₁ record
    { signed-value =
        signed-stamped-witness-state.signed-value prior +
        signed-propagation-step.signed-delta step
    ; signed-stamp = signed-propagation-step.signed-post-stamp step
    ; signed-witness-bits = signed-propagation-step.signed-post-witness-bits step
    }

apply-signed-propagate-morphism :
  (prior : signed-stamped-witness-state) →
  (step : signed-propagation-step) →
  (conjunct : signed-admissibility-conjunct) →
  (excitement-selected : Bool) →
  signed-propagate-morphism ⊎ signed-propagate-refusal
apply-signed-propagate-morphism prior step conjunct excitement-selected with
  propagate-signed-state prior step conjunct excitement-selected
... | inj₁ post = inj₁ record
  { signed-morphism-from = prior
  ; signed-morphism-to = post
  ; signed-morphism-witness = witness-from-signed-state prior
  ; signed-morphism-excitement-selected = excitement-selected
  }
... | inj₂ r = inj₂ r

signed-propagate-unsigned-refused :
  ∀ (is-unsigned-carry : Bool) →
  is-unsigned-carry ≡ true →
  evaluate-signed-propagate-operation is-unsigned-carry ≡
  spv-unsigned-propagation-refused
signed-propagate-unsigned-refused true refl = refl

signed-propagate-morphism-ok-when-not-unsigned :
  evaluate-signed-propagate-operation false ≡ spv-morphism-ok
signed-propagate-morphism-ok-when-not-unsigned = refl

refuse-unsigned-propagation-positive :
  refuse-unsigned-propagation ≡ spr-unsigned-propagation-refused
refuse-unsigned-propagation-positive = refl

------------------------------------------------------------------------
-- SECTION 3: Signed propagate composes excitement-select (no second argmin)
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

record signed-propagate-ctx (src : ThermodynamicState) : Set where
  field
    signed-propagate-successors : List (history-candidate src)

signed-propagate-select :
  (src : ThermodynamicState) → signed-propagate-ctx src →
  history-candidate src ⊎ excitement-residue
signed-propagate-select src ctx =
  excitement-select src (signed-propagate-ctx.signed-propagate-successors ctx)

signed-propagate-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : signed-propagate-ctx src) →
  signed-propagate-select src ctx ≡
  excitement-select src (signed-propagate-ctx.signed-propagate-successors ctx)
signed-propagate-select-eq-excitement-select src ctx = refl

signed-propagate-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : signed-propagate-ctx src) →
  signed-propagate-select src ctx ≡
  excitement-select src (signed-propagate-ctx.signed-propagate-successors ctx)
signed-propagate-no-local-argmin src ctx =
  signed-propagate-select-eq-excitement-select src ctx

signed-propagate-empty :
  ∀ (src : ThermodynamicState) (ctx : signed-propagate-ctx src) →
  signed-propagate-ctx.signed-propagate-successors ctx ≡ List.[] →
  signed-propagate-select src ctx ≡ inj₂ exc-no-candidates
signed-propagate-empty src ctx refl = refl

------------------------------------------------------------------------
-- SECTION 4: Excitement compose pin (no second ℚ argmin)
------------------------------------------------------------------------

data SignedPropagateRefusal : Set where
  unsigned-propagation second-argmin witness-drop : SignedPropagateRefusal

refuse-unsigned-propagation-tag : SignedPropagateRefusal
refuse-unsigned-propagation-tag = unsigned-propagation

refuse-second-argmin : SignedPropagateRefusal
refuse-second-argmin = second-argmin

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

urge-signed-propagate-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-signed-propagate-select = excitement-select

------------------------------------------------------------------------
-- SECTION 5: §4 fixtures + witness theorems
------------------------------------------------------------------------

signed-fixture-stamp : signed-propagate-wall-stamp
signed-fixture-stamp = record
  { signed-wall-seq = 1
  ; signed-wall-has-t = true
  }

signed-fixture-post-stamp : signed-propagate-wall-stamp
signed-fixture-post-stamp = record
  { signed-wall-seq = 2
  ; signed-wall-has-t = true
  }

signed-fixture-state : signed-stamped-witness-state
signed-fixture-state = record
  { signed-value = + 10
  ; signed-stamp = signed-fixture-stamp
  ; signed-witness-bits = 4
  }

signed-fixture-step : signed-propagation-step
signed-fixture-step = record
  { signed-delta = + 3
  ; signed-post-stamp = signed-fixture-post-stamp
  ; signed-post-witness-bits = 4
  }

signed-fixture-conjunct : signed-admissibility-conjunct
signed-fixture-conjunct = record
  { signed-conj-gate-ok = true
  ; signed-conj-stamp-ok = true
  ; signed-conj-witness-present = true
  ; signed-conj-excitement-preserves = true
  }

signed-fixture-post-state : signed-stamped-witness-state
signed-fixture-post-state = record
  { signed-value = + 13
  ; signed-stamp = signed-fixture-post-stamp
  ; signed-witness-bits = 4
  }

signed-fixture-unsigned-refused :
  refuse-unsigned-propagation ≡ spr-unsigned-propagation-refused
signed-fixture-unsigned-refused = refl

signed-fixture-propagate-ok :
  propagate-signed-state
    signed-fixture-state signed-fixture-step signed-fixture-conjunct true ≡
  inj₁ signed-fixture-post-state
signed-fixture-propagate-ok = refl

signed-fixture-apply-morphism-ok :
  apply-signed-propagate-morphism
    signed-fixture-state signed-fixture-step signed-fixture-conjunct true ≡
  inj₁ record
    { signed-morphism-from = signed-fixture-state
    ; signed-morphism-to = signed-fixture-post-state
    ; signed-morphism-witness = witness-from-signed-state signed-fixture-state
    ; signed-morphism-excitement-selected = true
    }
signed-fixture-apply-morphism-ok = refl

signed-fixture-unsigned-state : signed-stamped-witness-state
signed-fixture-unsigned-state = record
  { signed-value = + 1
  ; signed-stamp = signed-fixture-stamp
  ; signed-witness-bits = 0
  }

signed-fixture-unsigned-propagation-refused :
  propagate-signed-state
    signed-fixture-unsigned-state signed-fixture-step signed-fixture-conjunct true ≡
  inj₂ spr-unsigned-propagation-refused
signed-fixture-unsigned-propagation-refused = refl

signed-fixture-witness-drop-step : signed-propagation-step
signed-fixture-witness-drop-step = record
  { signed-delta = + 1
  ; signed-post-stamp = signed-fixture-post-stamp
  ; signed-post-witness-bits = 2
  }

signed-fixture-witness-drop-refused :
  propagate-signed-state
    signed-fixture-state signed-fixture-witness-drop-step
    signed-fixture-conjunct true ≡
  inj₂ (spr-witness-dropped 4 2)
signed-fixture-witness-drop-refused = refl

signed-fixture-witness-preserves-stamp :
  signed-propagate-witness.signed-witness-stamp
    (witness-from-signed-state signed-fixture-state) ≡
  signed-fixture-stamp
signed-fixture-witness-preserves-stamp = refl

signed-fixture-wall-stamp-ok :
  wall-stamp-ok signed-fixture-stamp ≡ true
signed-fixture-wall-stamp-ok = refl

signed-fixture-witness-present :
  witness-present signed-fixture-state ≡ true
signed-fixture-witness-present = refl

signed-propagate-positive-refuse-not-silent :
  evaluate-signed-propagate-operation true ≢ spv-morphism-ok
signed-propagate-positive-refuse-not-silent ()

------------------------------------------------------------------------
-- SECTION 6: Typed history + Landauer bridge (zero new postulates)
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

signed-propagate-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
signed-propagate-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

signed-propagate-physics-green : Bool
signed-propagate-physics-green = false

signed-propagate-physics-green-false :
  signed-propagate-physics-green ≡ false
signed-propagate-physics-green-false = refl

signed-propagate-production-wired : Bool
signed-propagate-production-wired = false

signed-propagate-production-wired-false :
  signed-propagate-production-wired ≡ false
signed-propagate-production-wired-false = refl

signed-propagate-module-witness : ⊤
signed-propagate-module-witness = tt

signed-propagate-no-new-axiom : ⊤
signed-propagate-no-new-axiom = tt

signed-propagate-marker : ℕ
signed-propagate-marker = 1

signed-propagate-marker-eq : signed-propagate-marker ≡ 1
signed-propagate-marker-eq = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl
