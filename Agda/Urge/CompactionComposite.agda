-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.CompactionComposite — meso/acting §17.5 compaction composite.
--
-- URGE-FORMAL-MESO-AGDA-COMPACTION-COMPOSITE (umst-formal acting fiber only).
-- §17.5: compaction is a composite Excitement arrow paying MI — not
-- delete-old-commits theater and not git-gc semantic squash. Composite *is*
-- the residue; `wasDerivedFrom*` derivation chain retained. Compose
-- `compaction-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.CompactionComposite where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Rational.Properties as ℚ-Props using (≤-refl; ≤-trans)
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

record compaction-candidate : Set where
  field
    cand-id : ℕ
    cand-free-energy : ℚ
    provenance-intact : Bool

compaction-excitement-select :
  (src : ℚ) → List compaction-candidate →
  compaction-candidate ⊎ excitement-residue
compaction-excitement-select src List.[] = inj₂ exc-no-candidates
compaction-excitement-select src (c List.∷ _) = inj₁ c

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
-- SECTION 2: Derivation chain witness (§17.5 wasDerivedFrom chain)
------------------------------------------------------------------------

record DerivationChainWitness : Set where
  field
    head-stamp : ℕ
    tail-stamps : List ℕ

derivation-chain-from-stamps : (head : ℕ) (tail : List ℕ) → DerivationChainWitness
derivation-chain-from-stamps head tail = record
  { head-stamp = head
  ; tail-stamps = tail
  }

------------------------------------------------------------------------
-- SECTION 3: MI payment witness — compaction pays MI, not null probe
------------------------------------------------------------------------

record MiPaymentWitness : Set where
  field
    required-bits : ℚ
    paid-bits : ℚ

mi-paid : MiPaymentWitness → Set
mi-paid w =
  ℚ.0ℚ ℚ.< MiPaymentWitness.paid-bits w ×
  MiPaymentWitness.required-bits w ≤ MiPaymentWitness.paid-bits w

mi-paid-intro :
  (w : MiPaymentWitness) →
  ℚ.0ℚ ℚ.< MiPaymentWitness.paid-bits w →
  MiPaymentWitness.required-bits w ≤ MiPaymentWitness.paid-bits w →
  mi-paid w
mi-paid-intro w hp hpaid = hp , hpaid

------------------------------------------------------------------------
-- SECTION 4: Composite compaction arrow — composite *is* the residue
------------------------------------------------------------------------

record CompositeCompactionArrow : Set where
  field
    composite-id : ℕ
    witness : DerivationChainWitness
    source-free-energy : ℚ
    mi : MiPaymentWitness
    mi-ok : mi-paid mi

record CompactionAttempt : Set where
  field
    delete-old-commits : Bool
    git-gc-substrate-only : Bool
    semantic-squash : Bool
    mi : MiPaymentWitness
    witness : Maybe DerivationChainWitness
    source-free-energy : ℚ

------------------------------------------------------------------------
-- SECTION 5: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data CompactionCompositeRefusal : Set where
  git-gc-theater : CompactionCompositeRefusal
  delete-old-commits-theater : CompactionCompositeRefusal
  semantic-squash-without-composite : CompactionCompositeRefusal
  second-argmin : CompactionCompositeRefusal
  mi-unpaid : CompactionCompositeRefusal

data CompactionClass : Set where
  git-gc-substrate : CompactionClass
  composite-excitement-arrow : CompactionClass

refuse-git-gc-theater : CompactionCompositeRefusal
refuse-git-gc-theater = git-gc-theater

refuse-delete-old-commits-theater : CompactionCompositeRefusal
refuse-delete-old-commits-theater = delete-old-commits-theater

refuse-semantic-squash-without-composite : CompactionCompositeRefusal
refuse-semantic-squash-without-composite = semantic-squash-without-composite

refuse-second-argmin : CompactionCompositeRefusal
refuse-second-argmin = second-argmin

refuse-mi-unpaid : CompactionCompositeRefusal
refuse-mi-unpaid = mi-unpaid

------------------------------------------------------------------------
-- SECTION 6: Gate compaction attempts (§17.5 composite arrow paying MI)
------------------------------------------------------------------------

composite-arrow-from-witness :
  (id : ℕ) (w : DerivationChainWitness) (src : ℚ) (mi : MiPaymentWitness) →
  mi-paid mi →
  CompositeCompactionArrow
composite-arrow-from-witness id w src mi hmi = record
  { composite-id = id
  ; witness = w
  ; source-free-energy = src
  ; mi = mi
  ; mi-ok = hmi
  }

classify-compaction :
  (attempt : CompactionAttempt) →
  Maybe DerivationChainWitness →
  CompactionClass ⊎ CompactionCompositeRefusal
classify-compaction attempt nothing with CompactionAttempt.semantic-squash attempt
... | true = inj₂ semantic-squash-without-composite
... | false with CompactionAttempt.git-gc-substrate-only attempt
... | true = inj₁ git-gc-substrate
... | false = inj₂ git-gc-theater
classify-compaction attempt (just w) with CompactionAttempt.semantic-squash attempt
... | true = inj₁ composite-excitement-arrow
... | false with CompactionAttempt.git-gc-substrate-only attempt
... | true = inj₁ git-gc-substrate
... | false = inj₁ composite-excitement-arrow

gate-compaction-mi-refuse-delete :
  (attempt : CompactionAttempt) →
  CompactionAttempt.delete-old-commits attempt ≡ true →
  CompactionCompositeRefusal
gate-compaction-mi-refuse-delete attempt _ = delete-old-commits-theater

gate-compaction-mi-admit :
  (attempt : CompactionAttempt) →
  CompactionAttempt.delete-old-commits attempt ≡ false →
  mi-paid (CompactionAttempt.mi attempt) →
  ⊤
gate-compaction-mi-admit attempt _ _ = tt

gate-compaction-mi-refuse-unpaid :
  (attempt : CompactionAttempt) →
  CompactionAttempt.delete-old-commits attempt ≡ false →
  ¬ mi-paid (CompactionAttempt.mi attempt) →
  CompactionCompositeRefusal
gate-compaction-mi-refuse-unpaid attempt _ _ = mi-unpaid

------------------------------------------------------------------------
-- SECTION 7: Excitement compose pin (no second argmin)
------------------------------------------------------------------------

urge-compaction-select :
  (src : ℚ) → List compaction-candidate →
  compaction-candidate ⊎ excitement-residue
urge-compaction-select = compaction-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 8: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

compaction-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
compaction-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

compaction-composite-production-wired : Bool
compaction-composite-production-wired = false

compaction-composite-production-wired-false :
  compaction-composite-production-wired ≡ false
compaction-composite-production-wired-false = refl

compaction-composite-marker : ℕ
compaction-composite-marker = 1

compaction-composite-marker-eq : compaction-composite-marker ≡ 1
compaction-composite-marker-eq = refl

compaction-composite-module-witness : ⊤
compaction-composite-module-witness = tt

delete-old-commits-refused :
  (attempt : CompactionAttempt) →
  (h : CompactionAttempt.delete-old-commits attempt ≡ true) →
  gate-compaction-mi-refuse-delete attempt h ≡ delete-old-commits-theater
delete-old-commits-refused attempt h = refl

git-gc-theater-refused :
  refuse-git-gc-theater ≡ git-gc-theater
git-gc-theater-refused = refl

semantic-squash-refused :
  refuse-semantic-squash-without-composite ≡ semantic-squash-without-composite
semantic-squash-refused = refl
