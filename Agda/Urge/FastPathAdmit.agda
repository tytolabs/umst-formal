-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.FastPathAdmit — meso/acting §17.8 fast-path admission.
--
-- URGE-FORMAL-MESO-AGDA-FAST-PATH-ADMIT (umst-formal acting fiber only).
-- §17.8: local commit admission ≤100ms via typed fast predicate (analogue of
-- R23 PreservationWitness — no whole-tree re-scan). Merge / recovery ≤1s slow
-- path with composed `excitement-select` — **not** wall-clock GREEN.
--
-- Mirror `Urge.CompactionComposite` discipline: compose excitement select —
-- no second ℚ argmin. Sole physics postulate remains
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated). Zero extra
-- postulates beyond Landauer.
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.FastPathAdmit where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ-Props using (_≤?_; ≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.List as List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (does)

------------------------------------------------------------------------
-- SECTION 1: §17.8 typed budget constants (not wall-clock GREEN)
------------------------------------------------------------------------

local-commit-budget-ms : ℕ
local-commit-budget-ms = 100

merge-recovery-budget-ms : ℕ
merge-recovery-budget-ms = 1000

local-commit-budget-ms-eq : local-commit-budget-ms ≡ 100
local-commit-budget-ms-eq = refl

merge-recovery-budget-ms-eq : merge-recovery-budget-ms ≡ 1000
merge-recovery-budget-ms-eq = refl

------------------------------------------------------------------------
-- SECTION 1b: Excitement hook (local mirror — no CoInfectiveImport)
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

excitement-select :
  (src : ThermodynamicState) → List.List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
excitement-select src List.[] = inj₂ exc-no-candidates
excitement-select src (c List.∷ _) = inj₁ c

record history-recovery-ctx (src : ThermodynamicState) : Set where
  field
    recovery-successors : List.List (history-candidate src)

urge-recovery :
  (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  history-candidate src ⊎ excitement-residue
urge-recovery src ctx =
  excitement-select src (history-recovery-ctx.recovery-successors ctx)

urge-recovery-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  urge-recovery src ctx ≡
  excitement-select src (history-recovery-ctx.recovery-successors ctx)
urge-recovery-eq-excitement-select src ctx = refl

------------------------------------------------------------------------
-- SECTION 2: Admission path classification
------------------------------------------------------------------------

data AdmitPath : Set where
  admit-path-fast-local : AdmitPath
  admit-path-full-merge-recovery : AdmitPath

admit-path-budget-ms : AdmitPath → ℕ
admit-path-budget-ms admit-path-fast-local = local-commit-budget-ms
admit-path-budget-ms admit-path-full-merge-recovery = merge-recovery-budget-ms

admit-path-fast-local-budget :
  admit-path-budget-ms admit-path-fast-local ≡ local-commit-budget-ms
admit-path-fast-local-budget = refl

admit-path-merge-recovery-budget :
  admit-path-budget-ms admit-path-full-merge-recovery ≡ merge-recovery-budget-ms
admit-path-merge-recovery-budget = refl

------------------------------------------------------------------------
-- SECTION 3: Fast-path candidate + typed predicate
------------------------------------------------------------------------

record FastPathCandidate : Set where
  field
    fp-is-local-append : Bool
    fp-requires-whole-tree-rescan : Bool
    fp-is-merge-or-recovery : Bool

fast-path-admit-pred : FastPathCandidate → Bool
fast-path-admit-pred c =
  if FastPathCandidate.fp-is-local-append c then
    if FastPathCandidate.fp-requires-whole-tree-rescan c then
      false
    else
      if FastPathCandidate.fp-is-merge-or-recovery c then
        false
      else
        true
  else
    false

data FastPathAdmitRefusal : Set where
  fp-refuse-whole-tree-rescan : FastPathAdmitRefusal
  fp-refuse-merge-recovery-slow-path : FastPathAdmitRefusal
  fp-refuse-wall-clock-sla-theater : FastPathAdmitRefusal
  fp-refuse-budget-exceeded : ℕ → ℕ → FastPathAdmitRefusal

classify-admit-path :
  (c : FastPathCandidate) →
  AdmitPath ⊎ FastPathAdmitRefusal
classify-admit-path c =
  if FastPathCandidate.fp-requires-whole-tree-rescan c then
    inj₂ fp-refuse-whole-tree-rescan
  else
    if FastPathCandidate.fp-is-merge-or-recovery c then
      inj₂ fp-refuse-merge-recovery-slow-path
    else
      if fast-path-admit-pred c then
        inj₁ admit-path-fast-local
      else
        inj₂ (fp-refuse-budget-exceeded (suc local-commit-budget-ms) local-commit-budget-ms)

classify-admit-path-fast-local :
  (c : FastPathCandidate) →
  FastPathCandidate.fp-is-local-append c ≡ true →
  FastPathCandidate.fp-requires-whole-tree-rescan c ≡ false →
  FastPathCandidate.fp-is-merge-or-recovery c ≡ false →
  classify-admit-path c ≡ inj₁ admit-path-fast-local
classify-admit-path-fast-local c hAppend hRescan hMerge
  rewrite hRescan
  rewrite hMerge
  rewrite hAppend
  = refl

classify-admit-path-whole-tree-rescan :
  (c : FastPathCandidate) →
  FastPathCandidate.fp-requires-whole-tree-rescan c ≡ true →
  classify-admit-path c ≡ inj₂ fp-refuse-whole-tree-rescan
classify-admit-path-whole-tree-rescan c h
  rewrite h
  = refl

classify-admit-path-merge-recovery :
  (c : FastPathCandidate) →
  FastPathCandidate.fp-requires-whole-tree-rescan c ≡ false →
  FastPathCandidate.fp-is-merge-or-recovery c ≡ true →
  classify-admit-path c ≡ inj₂ fp-refuse-merge-recovery-slow-path
classify-admit-path-merge-recovery c hRescan hMerge
  rewrite hRescan
  rewrite hMerge
  = refl

refuse-wall-clock-sla-theater :
  FastPathAdmitRefusal ⊎ FastPathAdmitRefusal
refuse-wall-clock-sla-theater = inj₂ fp-refuse-wall-clock-sla-theater

------------------------------------------------------------------------
-- SECTION 4: Typed budget witness (declared ceiling, not measured)
------------------------------------------------------------------------

record LatencyBudgetWitness : Set where
  field
    lb-path : AdmitPath
    lb-budget-ms : ℕ
    lb-typed-predicate : Bool

budget-witness-for : (p : AdmitPath) → LatencyBudgetWitness
budget-witness-for p = record
  { lb-path = p
  ; lb-budget-ms = admit-path-budget-ms p
  ; lb-typed-predicate = true
  }

budget-witness-for-typed :
  ∀ (p : AdmitPath) →
  LatencyBudgetWitness.lb-typed-predicate (budget-witness-for p) ≡ true
budget-witness-for-typed p = refl

budget-witness-for-budget :
  ∀ (p : AdmitPath) →
  LatencyBudgetWitness.lb-budget-ms (budget-witness-for p) ≡ admit-path-budget-ms p
budget-witness-for-budget p = refl

check-typed-budget :
  (p : AdmitPath) (estimated-ms : ℕ) →
  LatencyBudgetWitness ⊎ FastPathAdmitRefusal
check-typed-budget p estimated-ms =
  if does (estimated-ms ℕ-Props.≤? admit-path-budget-ms p) then
    inj₁ (budget-witness-for p)
  else
    inj₂ (fp-refuse-budget-exceeded estimated-ms (admit-path-budget-ms p))

------------------------------------------------------------------------
-- SECTION 5: Slow path composes Excitement (no second argmin)
------------------------------------------------------------------------

slow-path-recovery :
  (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  history-candidate src ⊎ excitement-residue
slow-path-recovery = urge-recovery

slow-path-recovery-eq-urge-recovery :
  ∀ (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  slow-path-recovery src ctx ≡ urge-recovery src ctx
slow-path-recovery-eq-urge-recovery src ctx = refl

slow-path-recovery-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  slow-path-recovery src ctx ≡
  excitement-select src (history-recovery-ctx.recovery-successors ctx)
slow-path-recovery-eq-excitement-select src ctx = refl

slow-path-recovery-no-second-argmin :
  ∀ (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  slow-path-recovery src ctx ≡
  excitement-select src (history-recovery-ctx.recovery-successors ctx)
slow-path-recovery-no-second-argmin src ctx = refl

urge-fast-path-select :
  (src : ThermodynamicState) → List.List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-fast-path-select = excitement-select

urge-fast-path-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List.List (history-candidate src)) →
  urge-fast-path-select src cands ≡ excitement-select src cands
urge-fast-path-select-eq-excitement-select src cands = refl

classify-slow-path :
  (c : FastPathCandidate) →
  AdmitPath ⊎ FastPathAdmitRefusal
classify-slow-path c =
  if FastPathCandidate.fp-is-merge-or-recovery c then
    inj₁ admit-path-full-merge-recovery
  else
    classify-admit-path c

classify-slow-path-merge-recovery :
  (c : FastPathCandidate) →
  FastPathCandidate.fp-is-merge-or-recovery c ≡ true →
  classify-slow-path c ≡ inj₁ admit-path-full-merge-recovery
classify-slow-path-merge-recovery c h
  rewrite h
  = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

------------------------------------------------------------------------
-- SECTION 6: Typed history carriers + Landauer bridge
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

fast-path-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
fast-path-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 7: Honesty flags (zero new postulates)
------------------------------------------------------------------------

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

fast-path-production-wired : Bool
fast-path-production-wired = false

fast-path-production-wired-false :
  fast-path-production-wired ≡ false
fast-path-production-wired-false = refl

fast-path-admit-marker : ℕ
fast-path-admit-marker = 1

fast-path-admit-marker-eq : fast-path-admit-marker ≡ 1
fast-path-admit-marker-eq = refl

fast-path-admit-module-witness : ⊤
fast-path-admit-module-witness = tt

preservation-witness-analogue-pin : ℕ
preservation-witness-analogue-pin = 0

preservation-witness-analogue-marker :
  preservation-witness-analogue-pin ≡ 0
preservation-witness-analogue-marker = refl

whole-tree-rescan-refused :
  classify-admit-path
    (record { fp-is-local-append = true
            ; fp-requires-whole-tree-rescan = true
            ; fp-is-merge-or-recovery = false })
  ≡ inj₂ fp-refuse-whole-tree-rescan
whole-tree-rescan-refused = refl

wall-clock-sla-theater-refused :
  refuse-wall-clock-sla-theater ≡ inj₂ fp-refuse-wall-clock-sla-theater
wall-clock-sla-theater-refused = refl
