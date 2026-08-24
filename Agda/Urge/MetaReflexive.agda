-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.MetaReflexive — meso/acting §10.5 umst-meta reflexive
-- health of Urge morphisms.
--
-- URGE-FORMAL-MESO-AGDA-META-REFLEXIVE (umst-formal acting fiber only).
-- Reflexive gate on repository + mesh transitions so Urge cannot lie about
-- integrity, residues, or formal coverage. Positive refuse via typed
-- `MetaReflexiveRefusal` — not only `!physics_green`. Composes
-- `excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.MetaReflexive where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_; not)
open import Data.List as List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
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

------------------------------------------------------------------------
-- SECTION 1: Urge morphism + reflexive health carriers (§10.5)
------------------------------------------------------------------------

data urge-morphism-kind : Set where
  umk-commit-patch : urge-morphism-kind
  umk-merge : urge-morphism-kind
  umk-recovery : urge-morphism-kind
  umk-mi-observation : urge-morphism-kind
  umk-signed-propagate : urge-morphism-kind

data reflexive-health-verdict : Set where
  rhv-healthy : reflexive-health-verdict
  rhv-refuse-bypass-meta : reflexive-health-verdict
  rhv-refuse-self-exempt : reflexive-health-verdict
  rhv-refuse-invented-green : reflexive-health-verdict
  rhv-refuse-missing-stamp : reflexive-health-verdict
  rhv-refuse-formal-overclaim : reflexive-health-verdict

record meta-reflexive-stamp : Set where
  field
    meta-stamp-seq : ℕ
    meta-stamp-wall-has-t : Bool

record meta-reflexive-witness : Set where
  field
    meta-witness-stamp : meta-reflexive-stamp
    meta-witness-present : Bool
    meta-witness-formal-coverage : Bool

record urge-morphism : Set where
  field
    morph-kind : urge-morphism-kind
    urge-morphism-bypasses-meta-gate : Bool
    urge-morphism-self-exempt : Bool
    urge-morphism-physics-green-claim : Bool
    urge-morphism-meta-witness-present : Bool
    urge-morphism-stamp : meta-reflexive-stamp
    urge-morphism-stamp-nonempty : Bool
    urge-morphism-formal-overclaim : Bool

data meta-reflexive-refusal : Set where
  mrr-bypass-meta : urge-morphism-kind → meta-reflexive-refusal
  mrr-self-exempt : urge-morphism-kind → meta-reflexive-refusal
  mrr-invented-green : urge-morphism-kind → meta-reflexive-refusal
  mrr-missing-stamp : ℕ → meta-reflexive-refusal
  mrr-formal-overclaim : urge-morphism-kind → meta-reflexive-refusal

data meta-reflexive-verdict : Set where
  mrv-healthy : meta-reflexive-verdict
  mrv-bypass-refused : meta-reflexive-verdict
  mrv-inadmissible : meta-reflexive-verdict

record reflexive-health-report : Set where
  field
    reflexive-report-kind : urge-morphism-kind
    reflexive-report-verdict : reflexive-health-verdict
    reflexive-report-physics-green : Bool

------------------------------------------------------------------------
-- SECTION 2: §10.5 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record meta-admissibility-conjunct : Set where
  field
    meta-conj-gate-ok : Bool
    meta-conj-reflexive-honest : Bool
    meta-conj-excitement-preserves : Bool

meta-conjunct-admits : meta-admissibility-conjunct → Bool
meta-conjunct-admits c =
  meta-admissibility-conjunct.meta-conj-gate-ok c ∧
  meta-admissibility-conjunct.meta-conj-reflexive-honest c ∧
  meta-admissibility-conjunct.meta-conj-excitement-preserves c

evaluate-meta-gate-bypass : Bool → meta-reflexive-verdict
evaluate-meta-gate-bypass true = mrv-bypass-refused
evaluate-meta-gate-bypass false = mrv-healthy

refuse-bypass-meta-gate : urge-morphism-kind → meta-reflexive-refusal
refuse-bypass-meta-gate k = mrr-bypass-meta k

refuse-self-exempt : urge-morphism-kind → meta-reflexive-refusal
refuse-self-exempt k = mrr-self-exempt k

refuse-invented-green : urge-morphism-kind → meta-reflexive-refusal
refuse-invented-green k = mrr-invented-green k

refuse-formal-overclaim : urge-morphism-kind → meta-reflexive-refusal
refuse-formal-overclaim k = mrr-formal-overclaim k

healthy-report : (k : urge-morphism-kind) → reflexive-health-report
healthy-report k = record
  { reflexive-report-kind = k
  ; reflexive-report-verdict = rhv-healthy
  ; reflexive-report-physics-green = false
  }

evaluate-reflexive-health-stamp-formal :
  (m : urge-morphism) →
  reflexive-health-report ⊎ meta-reflexive-refusal
evaluate-reflexive-health-stamp-formal m =
  if_then_else_ (urge-morphism.urge-morphism-stamp-nonempty m)
    (if_then_else_ (urge-morphism.urge-morphism-formal-overclaim m)
      (inj₂ (mrr-formal-overclaim (urge-morphism.morph-kind m)))
      (inj₁ (healthy-report (urge-morphism.morph-kind m))))
    (inj₂ (mrr-missing-stamp
      (meta-reflexive-stamp.meta-stamp-seq (urge-morphism.urge-morphism-stamp m))))

evaluate-reflexive-health-after-self :
  (m : urge-morphism) →
  reflexive-health-report ⊎ meta-reflexive-refusal
evaluate-reflexive-health-after-self m =
  if_then_else_ (urge-morphism.urge-morphism-physics-green-claim m ∧
                 not (urge-morphism.urge-morphism-meta-witness-present m))
    (inj₂ (mrr-invented-green (urge-morphism.morph-kind m)))
    (evaluate-reflexive-health-stamp-formal m)

evaluate-reflexive-health :
  (m : urge-morphism) →
  reflexive-health-report ⊎ meta-reflexive-refusal
evaluate-reflexive-health m =
  if_then_else_ (urge-morphism.urge-morphism-bypasses-meta-gate m)
    (inj₂ (mrr-bypass-meta (urge-morphism.morph-kind m)))
    (if_then_else_ (urge-morphism.urge-morphism-self-exempt m)
      (inj₂ (mrr-self-exempt (urge-morphism.morph-kind m)))
      (evaluate-reflexive-health-after-self m))

apply-meta-reflexive-morphism :
  (m : urge-morphism) →
  (conjunct : meta-admissibility-conjunct) →
  (excitement-selected : Bool) →
  urge-morphism ⊎ meta-reflexive-refusal
apply-meta-reflexive-morphism m conjunct excitement-selected with meta-conjunct-admits conjunct
... | false = inj₂ (mrr-missing-stamp (meta-reflexive-stamp.meta-stamp-seq (urge-morphism.urge-morphism-stamp m)))
... | true with excitement-selected
... | false = inj₂ (mrr-formal-overclaim (urge-morphism.morph-kind m))
... | true with evaluate-reflexive-health m
... | inj₁ _ = inj₁ m
... | inj₂ r = inj₂ r

meta-reflexive-bypass-refused :
  (k : urge-morphism-kind) →
  refuse-bypass-meta-gate k ≡ mrr-bypass-meta k
meta-reflexive-bypass-refused k = refl

meta-reflexive-self-exempt-refused :
  (k : urge-morphism-kind) →
  refuse-self-exempt k ≡ mrr-self-exempt k
meta-reflexive-self-exempt-refused k = refl

meta-reflexive-invented-green-refused :
  (k : urge-morphism-kind) →
  refuse-invented-green k ≡ mrr-invented-green k
meta-reflexive-invented-green-refused k = refl

meta-reflexive-formal-overclaim-refused :
  (k : urge-morphism-kind) →
  refuse-formal-overclaim k ≡ mrr-formal-overclaim k
meta-reflexive-formal-overclaim-refused k = refl

evaluate-meta-gate-bypass-positive :
  evaluate-meta-gate-bypass true ≡ mrv-bypass-refused
evaluate-meta-gate-bypass-positive = refl

evaluate-meta-gate-bypass-honest :
  evaluate-meta-gate-bypass false ≡ mrv-healthy
evaluate-meta-gate-bypass-honest = refl

------------------------------------------------------------------------
-- SECTION 2b: Excitement hook (mirrors ExcitementImport — no local argmin)
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

urge-recovery-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select = excitement-select

------------------------------------------------------------------------
-- SECTION 3: Reflexive recovery composes Excitement (no second argmin)
------------------------------------------------------------------------

record meta-reflexive-ctx (src : ThermodynamicState) : Set where
  field
    meta-reflexive-successors : List (history-candidate src)

meta-reflexive-select :
  (src : ThermodynamicState) →
  (ctx : meta-reflexive-ctx src) →
  history-candidate src ⊎ excitement-residue
meta-reflexive-select src ctx =
  urge-recovery-select src (meta-reflexive-ctx.meta-reflexive-successors ctx)

meta-reflexive-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : meta-reflexive-ctx src) →
  meta-reflexive-select src ctx ≡
  excitement-select src (meta-reflexive-ctx.meta-reflexive-successors ctx)
meta-reflexive-select-eq-excitement-select src ctx = refl

meta-reflexive-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : meta-reflexive-ctx src) →
  meta-reflexive-select src ctx ≡
  urge-recovery-select src (meta-reflexive-ctx.meta-reflexive-successors ctx)
meta-reflexive-select-eq-urge-recovery-select src ctx = refl

meta-reflexive-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : meta-reflexive-ctx src) →
  meta-reflexive-select src ctx ≡
  excitement-select src (meta-reflexive-ctx.meta-reflexive-successors ctx)
meta-reflexive-no-local-argmin src ctx =
  meta-reflexive-select-eq-excitement-select src ctx

meta-reflexive-empty :
  ∀ (src : ThermodynamicState) (ctx : meta-reflexive-ctx src) →
  meta-reflexive-ctx.meta-reflexive-successors ctx ≡ List.[] →
  meta-reflexive-select src ctx ≡ inj₂ exc-no-candidates
meta-reflexive-empty src ctx Hnil rewrite Hnil = refl

------------------------------------------------------------------------
-- SECTION 4: §10.5 fixtures + witness theorems
------------------------------------------------------------------------

meta-fixture-state : ThermodynamicState
meta-fixture-state = record { density = 0ℚ ; free-energy = 0ℚ ; hydration = 0ℚ ; strength = 0ℚ }

meta-fixture-stamp : meta-reflexive-stamp
meta-fixture-stamp = record
  { meta-stamp-seq = 7
  ; meta-stamp-wall-has-t = true
  }

meta-fixture-witness : meta-reflexive-witness
meta-fixture-witness = record
  { meta-witness-stamp = meta-fixture-stamp
  ; meta-witness-present = true
  ; meta-witness-formal-coverage = true
  }

meta-fixture-healthy-morphism : urge-morphism
meta-fixture-healthy-morphism = record
  { morph-kind = umk-commit-patch
  ; urge-morphism-bypasses-meta-gate = false
  ; urge-morphism-self-exempt = false
  ; urge-morphism-physics-green-claim = false
  ; urge-morphism-meta-witness-present = false
  ; urge-morphism-stamp = meta-fixture-stamp
  ; urge-morphism-stamp-nonempty = true
  ; urge-morphism-formal-overclaim = false
  }

meta-fixture-bypass-morphism : urge-morphism
meta-fixture-bypass-morphism = record
  { morph-kind = umk-merge
  ; urge-morphism-bypasses-meta-gate = true
  ; urge-morphism-self-exempt = false
  ; urge-morphism-physics-green-claim = false
  ; urge-morphism-meta-witness-present = false
  ; urge-morphism-stamp = meta-fixture-stamp
  ; urge-morphism-stamp-nonempty = true
  ; urge-morphism-formal-overclaim = false
  }

meta-fixture-invented-green : urge-morphism
meta-fixture-invented-green = record
  { morph-kind = umk-recovery
  ; urge-morphism-bypasses-meta-gate = false
  ; urge-morphism-self-exempt = false
  ; urge-morphism-physics-green-claim = true
  ; urge-morphism-meta-witness-present = false
  ; urge-morphism-stamp = meta-fixture-stamp
  ; urge-morphism-stamp-nonempty = true
  ; urge-morphism-formal-overclaim = false
  }

meta-fixture-conjunct : meta-admissibility-conjunct
meta-fixture-conjunct = record
  { meta-conj-gate-ok = true
  ; meta-conj-reflexive-honest = true
  ; meta-conj-excitement-preserves = true
  }

meta-fixture-healthy-report : reflexive-health-report
meta-fixture-healthy-report = record
  { reflexive-report-kind = umk-commit-patch
  ; reflexive-report-verdict = rhv-healthy
  ; reflexive-report-physics-green = false
  }

meta-fixture-healthy-admits :
  evaluate-reflexive-health meta-fixture-healthy-morphism ≡
  inj₁ meta-fixture-healthy-report
meta-fixture-healthy-admits = refl

meta-fixture-bypass-refused :
  evaluate-reflexive-health meta-fixture-bypass-morphism ≡
  inj₂ (mrr-bypass-meta umk-merge)
meta-fixture-bypass-refused = refl

meta-fixture-invented-green-refused :
  evaluate-reflexive-health meta-fixture-invented-green ≡
  inj₂ (mrr-invented-green umk-recovery)
meta-fixture-invented-green-refused = refl

meta-fixture-apply-morphism-ok :
  apply-meta-reflexive-morphism
    meta-fixture-healthy-morphism meta-fixture-conjunct true ≡
  inj₁ meta-fixture-healthy-morphism
meta-fixture-apply-morphism-ok = refl

meta-fixture-witness-preserves-stamp :
  meta-reflexive-witness.meta-witness-stamp meta-fixture-witness ≡ meta-fixture-stamp
meta-fixture-witness-preserves-stamp = refl

------------------------------------------------------------------------
-- SECTION 5: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

meta-reflexive-physics-green : Bool
meta-reflexive-physics-green = false

meta-reflexive-physics-green-false :
  meta-reflexive-physics-green ≡ false
meta-reflexive-physics-green-false = refl

meta-reflexive-production-wired : Bool
meta-reflexive-production-wired = false

meta-reflexive-production-wired-false :
  meta-reflexive-production-wired ≡ false
meta-reflexive-production-wired-false = refl

meta-reflexive-module-witness : ⊤
meta-reflexive-module-witness = tt

meta-reflexive-no-new-axiom : ⊤
meta-reflexive-no-new-axiom = tt

meta-reflexive-positive-refuse-not-silent :
  evaluate-meta-gate-bypass true ≢ mrv-healthy
meta-reflexive-positive-refuse-not-silent ()

meta-reflexive-marker : ℕ
meta-reflexive-marker = 1

meta-reflexive-marker-eq : meta-reflexive-marker ≡ 1
meta-reflexive-marker-eq = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  mrr-formal-overclaim umk-signed-propagate ≡
  mrr-formal-overclaim umk-signed-propagate
refuse-second-argmin-is-tag = refl
