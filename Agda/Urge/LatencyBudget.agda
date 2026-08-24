-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.LatencyBudget — meso/acting §17.8 latency budget.
--
-- URGE-FORMAL-MESO-AGDA-LATENCY-BUDGET (umst-formal acting fiber only).
-- §17.8: latency budget as typed predicate on admit — integer surrogate ms
-- vs declared tier ceiling, **not** wall-clock SLA theater. Merge / recovery
-- slow path composes `latency-budget-excitement-select` — no second ℚ argmin.
--
-- Mirror `Urge.CompactionComposite` discipline. Sole physics postulate remains
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated). Zero extra
-- postulates beyond Landauer.
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.LatencyBudget where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ-Props using (_≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (does)

------------------------------------------------------------------------
-- SECTION 1: §17.8 typed budget tiers (not wall-clock GREEN)
------------------------------------------------------------------------

interactive-budget-ms : ℕ
interactive-budget-ms = 16

local-commit-budget-ms : ℕ
local-commit-budget-ms = 100

merge-recovery-budget-ms : ℕ
merge-recovery-budget-ms = 1000

background-budget-ms : ℕ
background-budget-ms = 10000

interactive-budget-ms-eq : interactive-budget-ms ≡ 16
interactive-budget-ms-eq = refl

local-commit-budget-ms-eq : local-commit-budget-ms ≡ 100
local-commit-budget-ms-eq = refl

merge-recovery-budget-ms-eq : merge-recovery-budget-ms ≡ 1000
merge-recovery-budget-ms-eq = refl

background-budget-ms-eq : background-budget-ms ≡ 10000
background-budget-ms-eq = refl

data LatencyBudgetTier : Set where
  lbt-interactive : LatencyBudgetTier
  lbt-local-commit : LatencyBudgetTier
  lbt-merge-recovery : LatencyBudgetTier
  lbt-background : LatencyBudgetTier

latency-tier-budget-ms : LatencyBudgetTier → ℕ
latency-tier-budget-ms lbt-interactive = interactive-budget-ms
latency-tier-budget-ms lbt-local-commit = local-commit-budget-ms
latency-tier-budget-ms lbt-merge-recovery = merge-recovery-budget-ms
latency-tier-budget-ms lbt-background = background-budget-ms

latency-tier-interactive-budget :
  latency-tier-budget-ms lbt-interactive ≡ interactive-budget-ms
latency-tier-interactive-budget = refl

latency-tier-local-commit-budget :
  latency-tier-budget-ms lbt-local-commit ≡ local-commit-budget-ms
latency-tier-local-commit-budget = refl

latency-tier-merge-recovery-budget :
  latency-tier-budget-ms lbt-merge-recovery ≡ merge-recovery-budget-ms
latency-tier-merge-recovery-budget = refl

latency-tier-background-budget :
  latency-tier-budget-ms lbt-background ≡ background-budget-ms
latency-tier-background-budget = refl

------------------------------------------------------------------------
-- SECTION 2: Candidate + witness carriers (§17.8 morphism mirror)
------------------------------------------------------------------------

record LatencyBudgetCandidate : Set where
  field
    lb-candidate-tier : LatencyBudgetTier
    lb-candidate-surrogate-ms : ℕ
    lb-candidate-claims-wall-clock-sla : Bool
    lb-candidate-claims-physics-green : Bool

record LatencyBudgetWitness : Set where
  field
    lb-witness-tier : LatencyBudgetTier
    lb-witness-budget-ms : ℕ
    lb-witness-surrogate-ms : ℕ
    lb-witness-typed-predicate : Bool

record LatencyBudgetMorphismWitness : Set where
  field
    lb-morph-witness-tier : LatencyBudgetTier
    lb-morph-witness-budget-ms : ℕ
    lb-morph-witness-surrogate-ms : ℕ
    lb-morph-witness-typed-predicate : Bool

record LatencyBudgetMorphism : Set where
  field
    lb-morphism-from : LatencyBudgetCandidate
    lb-morphism-witness : LatencyBudgetMorphismWitness
    lb-morphism-excitement-selected : Bool

data LatencyBudgetRefusal : Set where
  lbr-budget-exceeded : ℕ → ℕ → LatencyBudgetRefusal
  lbr-wall-clock-sla-theater : LatencyBudgetRefusal
  lbr-physics-green-invent : LatencyBudgetRefusal
  lbr-unbounded-latency-ratio-theater : LatencyBudgetRefusal
  lbr-gate-rejected : ℕ → LatencyBudgetRefusal

data LatencyBudgetVerdict : Set where
  lbv-admit-ok : LatencyBudgetVerdict
  lbv-wall-clock-sla-refused : LatencyBudgetVerdict
  lbv-physics-green-refused : LatencyBudgetVerdict
  lbv-ratio-theater-refused : LatencyBudgetVerdict
  lbv-inadmissible : LatencyBudgetVerdict

------------------------------------------------------------------------
-- SECTION 3: §17.8 admissibility conjunct + typed predicate
------------------------------------------------------------------------

record LatencyAdmissibilityConjunct : Set where
  field
    lb-conj-gate-ok : Bool
    lb-conj-typed-predicate : Bool
    lb-conj-excitement-preserves : Bool

latency-conjunct-admits : LatencyAdmissibilityConjunct → Bool
latency-conjunct-admits c =
  if LatencyAdmissibilityConjunct.lb-conj-gate-ok c then
    if LatencyAdmissibilityConjunct.lb-conj-typed-predicate c then
      LatencyAdmissibilityConjunct.lb-conj-excitement-preserves c
    else
      false
  else
    false

latency-budget-admit-pred : LatencyBudgetCandidate → Bool
latency-budget-admit-pred c =
  if LatencyBudgetCandidate.lb-candidate-claims-wall-clock-sla c then
    false
  else
    if LatencyBudgetCandidate.lb-candidate-claims-physics-green c then
      false
    else
      does (LatencyBudgetCandidate.lb-candidate-surrogate-ms c ℕ-Props.≤?
            latency-tier-budget-ms (LatencyBudgetCandidate.lb-candidate-tier c))

evaluate-wall-clock-sla-operation : Bool → LatencyBudgetVerdict
evaluate-wall-clock-sla-operation true = lbv-wall-clock-sla-refused
evaluate-wall-clock-sla-operation false = lbv-admit-ok

evaluate-physics-green-operation : Bool → LatencyBudgetVerdict
evaluate-physics-green-operation true = lbv-physics-green-refused
evaluate-physics-green-operation false = lbv-admit-ok

refuse-wall-clock-sla-theater :
  LatencyBudgetRefusal ⊎ LatencyBudgetRefusal
refuse-wall-clock-sla-theater = inj₂ lbr-wall-clock-sla-theater

refuse-unbounded-latency-ratio-theater :
  LatencyBudgetRefusal ⊎ LatencyBudgetRefusal
refuse-unbounded-latency-ratio-theater = inj₂ lbr-unbounded-latency-ratio-theater

evaluate-latency-budget-admit :
  LatencyBudgetCandidate →
  LatencyBudgetWitness ⊎ LatencyBudgetRefusal
evaluate-latency-budget-admit c =
  if LatencyBudgetCandidate.lb-candidate-claims-physics-green c then
    inj₂ lbr-physics-green-invent
  else
    if LatencyBudgetCandidate.lb-candidate-claims-wall-clock-sla c then
      inj₂ lbr-wall-clock-sla-theater
    else
      let budget-ms = latency-tier-budget-ms (LatencyBudgetCandidate.lb-candidate-tier c)
          surrogate-ms = LatencyBudgetCandidate.lb-candidate-surrogate-ms c
      in if does (surrogate-ms ℕ-Props.≤? budget-ms) then
           inj₁ (record
             { lb-witness-tier = LatencyBudgetCandidate.lb-candidate-tier c
             ; lb-witness-budget-ms = budget-ms
             ; lb-witness-surrogate-ms = surrogate-ms
             ; lb-witness-typed-predicate = true
             })
         else
           inj₂ (lbr-budget-exceeded surrogate-ms budget-ms)

witness-from-candidate :
  LatencyBudgetCandidate → LatencyBudgetWitness → LatencyBudgetMorphismWitness
witness-from-candidate c w = record
  { lb-morph-witness-tier = LatencyBudgetWitness.lb-witness-tier w
  ; lb-morph-witness-budget-ms = LatencyBudgetWitness.lb-witness-budget-ms w
  ; lb-morph-witness-surrogate-ms = LatencyBudgetWitness.lb-witness-surrogate-ms w
  ; lb-morph-witness-typed-predicate = LatencyBudgetWitness.lb-witness-typed-predicate w
  }

apply-latency-budget-morphism-admitted :
  LatencyBudgetCandidate → Bool →
  LatencyBudgetWitness ⊎ LatencyBudgetRefusal →
  LatencyBudgetMorphism ⊎ LatencyBudgetRefusal
apply-latency-budget-morphism-admitted candidate excitement-selected (inj₁ w) =
  inj₁ (record
    { lb-morphism-from = candidate
    ; lb-morphism-witness = witness-from-candidate candidate w
    ; lb-morphism-excitement-selected = excitement-selected
    })
apply-latency-budget-morphism-admitted candidate _ (inj₂ r) = inj₂ r

apply-latency-budget-morphism :
  LatencyBudgetCandidate → LatencyAdmissibilityConjunct → Bool →
  LatencyBudgetMorphism ⊎ LatencyBudgetRefusal
apply-latency-budget-morphism candidate conjunct excitement-selected =
  if latency-conjunct-admits conjunct then
    if LatencyAdmissibilityConjunct.lb-conj-typed-predicate conjunct then
      if excitement-selected then
        apply-latency-budget-morphism-admitted candidate excitement-selected
          (evaluate-latency-budget-admit candidate)
      else
        inj₂ (lbr-budget-exceeded
               (LatencyBudgetCandidate.lb-candidate-surrogate-ms candidate)
               (latency-tier-budget-ms (LatencyBudgetCandidate.lb-candidate-tier candidate)))
    else
      inj₂ lbr-wall-clock-sla-theater
  else
    inj₂ (lbr-gate-rejected (LatencyBudgetCandidate.lb-candidate-surrogate-ms candidate))

budget-witness-for : LatencyBudgetTier → LatencyBudgetWitness
budget-witness-for t = record
  { lb-witness-tier = t
  ; lb-witness-budget-ms = latency-tier-budget-ms t
  ; lb-witness-surrogate-ms = zero
  ; lb-witness-typed-predicate = true
  }

budget-witness-for-typed :
  ∀ (t : LatencyBudgetTier) →
  LatencyBudgetWitness.lb-witness-typed-predicate (budget-witness-for t) ≡ true
budget-witness-for-typed t = refl

budget-witness-for-budget :
  ∀ (t : LatencyBudgetTier) →
  LatencyBudgetWitness.lb-witness-budget-ms (budget-witness-for t) ≡ latency-tier-budget-ms t
budget-witness-for-budget t = refl

check-typed-budget :
  LatencyBudgetTier → ℕ →
  LatencyBudgetWitness ⊎ LatencyBudgetRefusal
check-typed-budget t surrogate-ms =
  evaluate-latency-budget-admit (record
    { lb-candidate-tier = t
    ; lb-candidate-surrogate-ms = surrogate-ms
    ; lb-candidate-claims-wall-clock-sla = false
    ; lb-candidate-claims-physics-green = false
    })

------------------------------------------------------------------------
-- SECTION 4: Excitement compose (no second ℚ argmin)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  field
    stub : ℕ

Admissible : ThermodynamicState → ThermodynamicState → Set
Admissible _ _ = ⊤

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record history-candidate (src : ThermodynamicState) : Set where
  field
    cand-id : ℕ
    cand-tgt : ThermodynamicState
    cand-admissible : Admissible src cand-tgt

latency-budget-excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
latency-budget-excitement-select src List.[] = inj₂ exc-no-candidates
latency-budget-excitement-select src (c List.∷ _) = inj₁ c

record LatencyBudgetCtx (src : ThermodynamicState) : Set where
  field
    latency-budget-successors : List (history-candidate src)

latency-budget-recovery-select :
  (src : ThermodynamicState) (ctx : LatencyBudgetCtx src) →
  history-candidate src ⊎ excitement-residue
latency-budget-recovery-select src ctx =
  latency-budget-excitement-select src (LatencyBudgetCtx.latency-budget-successors ctx)

latency-budget-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : LatencyBudgetCtx src) →
  latency-budget-recovery-select src ctx ≡
  latency-budget-excitement-select src (LatencyBudgetCtx.latency-budget-successors ctx)
latency-budget-select-eq-excitement-select src ctx = refl

latency-budget-no-second-argmin :
  ∀ (src : ThermodynamicState) (ctx : LatencyBudgetCtx src) →
  latency-budget-recovery-select src ctx ≡
  latency-budget-excitement-select src (LatencyBudgetCtx.latency-budget-successors ctx)
latency-budget-no-second-argmin src ctx = refl

urge-latency-budget-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-latency-budget-select = latency-budget-excitement-select

urge-latency-budget-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  urge-latency-budget-select src cands ≡ latency-budget-excitement-select src cands
urge-latency-budget-select-eq-excitement-select src cands = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin : LatencyBudgetRefusal
refuse-second-argmin = lbr-unbounded-latency-ratio-theater

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ lbr-unbounded-latency-ratio-theater
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 5: Typed history carriers + Landauer bridge
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

latency-budget-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
latency-budget-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 6: §17.8 fixtures + honesty flags (zero new postulates)
------------------------------------------------------------------------

latency-fixture-interactive-candidate : LatencyBudgetCandidate
latency-fixture-interactive-candidate = record
  { lb-candidate-tier = lbt-interactive
  ; lb-candidate-surrogate-ms = 10
  ; lb-candidate-claims-wall-clock-sla = false
  ; lb-candidate-claims-physics-green = false
  }

latency-fixture-local-commit-candidate : LatencyBudgetCandidate
latency-fixture-local-commit-candidate = record
  { lb-candidate-tier = lbt-local-commit
  ; lb-candidate-surrogate-ms = 80
  ; lb-candidate-claims-wall-clock-sla = false
  ; lb-candidate-claims-physics-green = false
  }

latency-fixture-over-budget-candidate : LatencyBudgetCandidate
latency-fixture-over-budget-candidate = record
  { lb-candidate-tier = lbt-local-commit
  ; lb-candidate-surrogate-ms = suc local-commit-budget-ms
  ; lb-candidate-claims-wall-clock-sla = false
  ; lb-candidate-claims-physics-green = false
  }

latency-fixture-wall-clock-candidate : LatencyBudgetCandidate
latency-fixture-wall-clock-candidate = record
  { lb-candidate-tier = lbt-local-commit
  ; lb-candidate-surrogate-ms = 50
  ; lb-candidate-claims-wall-clock-sla = true
  ; lb-candidate-claims-physics-green = false
  }

latency-fixture-green-candidate : LatencyBudgetCandidate
latency-fixture-green-candidate = record
  { lb-candidate-tier = lbt-merge-recovery
  ; lb-candidate-surrogate-ms = 500
  ; lb-candidate-claims-wall-clock-sla = false
  ; lb-candidate-claims-physics-green = true
  }

latency-fixture-conjunct : LatencyAdmissibilityConjunct
latency-fixture-conjunct = record
  { lb-conj-gate-ok = true
  ; lb-conj-typed-predicate = true
  ; lb-conj-excitement-preserves = true
  }

latency-fixture-interactive-admits :
  evaluate-latency-budget-admit latency-fixture-interactive-candidate ≡
  inj₁ (record
    { lb-witness-tier = lbt-interactive
    ; lb-witness-budget-ms = interactive-budget-ms
    ; lb-witness-surrogate-ms = 10
    ; lb-witness-typed-predicate = true
    })
latency-fixture-interactive-admits = refl

latency-fixture-local-commit-admits :
  evaluate-latency-budget-admit latency-fixture-local-commit-candidate ≡
  inj₁ (record
    { lb-witness-tier = lbt-local-commit
    ; lb-witness-budget-ms = local-commit-budget-ms
    ; lb-witness-surrogate-ms = 80
    ; lb-witness-typed-predicate = true
    })
latency-fixture-local-commit-admits = refl

latency-fixture-over-budget-refused :
  evaluate-latency-budget-admit latency-fixture-over-budget-candidate ≡
  inj₂ (lbr-budget-exceeded (suc local-commit-budget-ms) local-commit-budget-ms)
latency-fixture-over-budget-refused = refl

latency-fixture-wall-clock-refused :
  evaluate-latency-budget-admit latency-fixture-wall-clock-candidate ≡
  inj₂ lbr-wall-clock-sla-theater
latency-fixture-wall-clock-refused = refl

latency-fixture-physics-green-refused :
  evaluate-latency-budget-admit latency-fixture-green-candidate ≡
  inj₂ lbr-physics-green-invent
latency-fixture-physics-green-refused = refl

latency-fixture-admit-pred-within-tier :
  latency-budget-admit-pred latency-fixture-local-commit-candidate ≡ true
latency-fixture-admit-pred-within-tier = refl

latency-fixture-admit-pred-wall-clock-false :
  latency-budget-admit-pred latency-fixture-wall-clock-candidate ≡ false
latency-fixture-admit-pred-wall-clock-false = refl

evaluate-wall-clock-sla-refused :
  evaluate-wall-clock-sla-operation true ≡ lbv-wall-clock-sla-refused
evaluate-wall-clock-sla-refused = refl

wall-clock-sla-theater-refused :
  refuse-wall-clock-sla-theater ≡ inj₂ lbr-wall-clock-sla-theater
wall-clock-sla-theater-refused = refl

unbounded-ratio-theater-refused :
  refuse-unbounded-latency-ratio-theater ≡ inj₂ lbr-unbounded-latency-ratio-theater
unbounded-ratio-theater-refused = refl

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

latency-budget-production-wired : Bool
latency-budget-production-wired = false

latency-budget-production-wired-false :
  latency-budget-production-wired ≡ false
latency-budget-production-wired-false = refl

latency-budget-marker : ℕ
latency-budget-marker = 1

latency-budget-marker-eq : latency-budget-marker ≡ 1
latency-budget-marker-eq = refl

latency-budget-module-witness : ⊤
latency-budget-module-witness = tt
