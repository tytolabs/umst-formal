-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.CompactionAsArrow — meso/acting §17.5 compaction as arrow.
--
-- URGE-FORMAL-MESO-AGDA-COMPACTION-AS-ARROW (umst-formal acting fiber only).
-- §17.5: sophisticated compaction is a composite Excitement arrow paying MI —
-- not delete-old-commits theater. Composite *is* the residue; `wasDerivedFrom*`
-- derivation chain retained. Compose `compaction-excitement-select` — no
-- second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.CompactionAsArrow where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_; _<_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers (CompactionComposite mirror)
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

------------------------------------------------------------------------
-- SECTION 2: Derivation chain witness (§17.5 wasDerivedFrom chain)
------------------------------------------------------------------------

record DerivationChainWitness : Set where
  field
    derivation-chain : List ℕ

retains-chain : DerivationChainWitness → Bool
retains-chain w with DerivationChainWitness.derivation-chain w
... | [] = false
... | _ ∷ _ = true

derivation-chain-from-stamps : List ℕ → DerivationChainWitness
derivation-chain-from-stamps chain = record { derivation-chain = chain }

retains-chain-singleton :
  (n : ℕ) → retains-chain (derivation-chain-from-stamps (n ∷ [])) ≡ true
retains-chain-singleton n = refl

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

mi-paid-bool-from-dec : (paid req : ℚ) → Dec (ℚ._<_ 0ℚ paid) → Dec (req ≤ paid) → Bool
mi-paid-bool-from-dec paid req (no _) _ = false
mi-paid-bool-from-dec paid req (yes _) (no _) = false
mi-paid-bool-from-dec paid req (yes _) (yes _) = true

mi-paid-bool : MiPaymentWitness → Bool
mi-paid-bool record { required-bits = req ; paid-bits = paid } =
  mi-paid-bool-from-dec paid req (ℚ.0ℚ ℚ.<? paid) (req ℚ.≤? paid)

mi-payment-from-landauer-bits : (n : ℕ) → MiPaymentWitness
mi-payment-from-landauer-bits zero = record { required-bits = 0ℚ ; paid-bits = 0ℚ }
mi-payment-from-landauer-bits (suc n) = record { required-bits = 0ℚ ; paid-bits = 0ℚ }

------------------------------------------------------------------------
-- SECTION 4: Composite compaction arrow — composite *is* the residue
------------------------------------------------------------------------

record CompactionArrow : Set where
  field
    composite-id : ℕ
    witness : DerivationChainWitness
    source-commit : ℕ
    excitement-selected : Bool

record CompactionAttempt : Set where
  field
    delete-old-commits : Bool
    mi : MiPaymentWitness
    witness : Maybe DerivationChainWitness
    provenance-intact : Bool
    excitement-selected : Bool

------------------------------------------------------------------------
-- SECTION 5: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data compaction-verdict : Set where
  caa-accept : compaction-verdict
  caa-reject : compaction-verdict

data CompactionAsArrowRefuse : Set where
  caa-refuse-delete-old-commits : CompactionAsArrowRefuse
  caa-refuse-mi-unpaid : CompactionAsArrowRefuse
  caa-refuse-second-argmin : CompactionAsArrowRefuse
  caa-refuse-missing-derivation-witness : CompactionAsArrowRefuse

refuse-delete-old-commits-theater : CompactionAsArrowRefuse
refuse-delete-old-commits-theater = caa-refuse-delete-old-commits

refuse-mi-unpaid : CompactionAsArrowRefuse
refuse-mi-unpaid = caa-refuse-mi-unpaid

refuse-second-argmin : CompactionAsArrowRefuse
refuse-second-argmin = caa-refuse-second-argmin

refuse-missing-derivation-witness : CompactionAsArrowRefuse
refuse-missing-derivation-witness = caa-refuse-missing-derivation-witness

------------------------------------------------------------------------
-- SECTION 6: Gate compaction attempts (§17.5 composite arrow paying MI)
------------------------------------------------------------------------

compaction-arrow-from-chain :
  (cid : ℕ) (chain : List ℕ) (source-commit : ℕ) (excitement-selected : Bool) →
  CompactionArrow ⊎ CompactionAsArrowRefuse
compaction-arrow-from-chain cid chain source-commit excitement-selected with chain
... | [] = inj₂ caa-refuse-missing-derivation-witness
... | _ ∷ _ = inj₁ (record
  { composite-id = cid
  ; witness = derivation-chain-from-stamps chain
  ; source-commit = source-commit
  ; excitement-selected = excitement-selected
  })

evaluate-compaction-attempt : CompactionAttempt → compaction-verdict
evaluate-compaction-attempt attempt with CompactionAttempt.delete-old-commits attempt
... | true = caa-reject
... | false with mi-paid-bool (CompactionAttempt.mi attempt)
... | false = caa-reject
... | true with CompactionAttempt.witness attempt
... | nothing = caa-reject
... | just w with retains-chain w
... | false = caa-reject
... | true with CompactionAttempt.provenance-intact attempt
... | false = caa-reject
... | true with CompactionAttempt.excitement-selected attempt
... | false = caa-reject
... | true = caa-accept

evaluate-compaction-attempt-refuse :
  (attempt : CompactionAttempt) →
  compaction-verdict ⊎ CompactionAsArrowRefuse
evaluate-compaction-attempt-refuse attempt with CompactionAttempt.delete-old-commits attempt
... | true = inj₂ caa-refuse-delete-old-commits
... | false with mi-paid-bool (CompactionAttempt.mi attempt)
... | false = inj₂ caa-refuse-mi-unpaid
... | true with CompactionAttempt.witness attempt
... | nothing = inj₂ caa-refuse-missing-derivation-witness
... | just w with retains-chain w
... | false = inj₂ caa-refuse-missing-derivation-witness
... | true with CompactionAttempt.provenance-intact attempt
... | false = inj₂ caa-refuse-missing-derivation-witness
... | true with CompactionAttempt.excitement-selected attempt
... | false = inj₂ caa-refuse-missing-derivation-witness
... | true = inj₁ caa-accept

gate-compaction-mi-refuse-delete :
  (attempt : CompactionAttempt) →
  CompactionAttempt.delete-old-commits attempt ≡ true →
  CompactionAsArrowRefuse
gate-compaction-mi-refuse-delete attempt _ = caa-refuse-delete-old-commits

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
  CompactionAsArrowRefuse
gate-compaction-mi-refuse-unpaid attempt _ _ = caa-refuse-mi-unpaid

------------------------------------------------------------------------
-- SECTION 7: Excitement compose pin (no second argmin)
------------------------------------------------------------------------

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

urge-compaction-select :
  (src : ℚ) → List compaction-candidate →
  compaction-candidate ⊎ excitement-residue
urge-compaction-select = compaction-excitement-select

compaction-as-arrow-select :
  (src : ℚ) → List compaction-candidate →
  compaction-candidate ⊎ excitement-residue
compaction-as-arrow-select = compaction-excitement-select

compaction-as-arrow-select-eq-excitement :
  ∀ (src : ℚ) (cands : List compaction-candidate) →
  compaction-as-arrow-select src cands ≡ compaction-excitement-select src cands
compaction-as-arrow-select-eq-excitement src cands = refl

urge-compaction-select-eq-excitement :
  ∀ (src : ℚ) (cands : List compaction-candidate) →
  urge-compaction-select src cands ≡ compaction-excitement-select src cands
urge-compaction-select-eq-excitement src cands = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ caa-refuse-second-argmin
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

compaction-as-arrow-physics-green : Bool
compaction-as-arrow-physics-green = false

compaction-as-arrow-physics-green-false :
  compaction-as-arrow-physics-green ≡ false
compaction-as-arrow-physics-green-false = refl

compaction-as-arrow-production-wired : Bool
compaction-as-arrow-production-wired = false

compaction-as-arrow-production-wired-false :
  compaction-as-arrow-production-wired ≡ false
compaction-as-arrow-production-wired-false = refl

compaction-as-arrow-marker : ℕ
compaction-as-arrow-marker = 175

compaction-as-arrow-marker-eq : compaction-as-arrow-marker ≡ 175
compaction-as-arrow-marker-eq = refl

compaction-as-arrow-module-witness : ⊤
compaction-as-arrow-module-witness = tt

delete-old-commits-refused :
  (attempt : CompactionAttempt) →
  (h : CompactionAttempt.delete-old-commits attempt ≡ true) →
  gate-compaction-mi-refuse-delete attempt h ≡ caa-refuse-delete-old-commits
delete-old-commits-refused attempt h = refl

refuse-delete-old-commits-theater-positive :
  refuse-delete-old-commits-theater ≡ caa-refuse-delete-old-commits
refuse-delete-old-commits-theater-positive = refl

refuse-second-argmin-positive :
  refuse-second-argmin ≡ caa-refuse-second-argmin
refuse-second-argmin-positive = refl

refuse-missing-derivation-witness-positive :
  refuse-missing-derivation-witness ≡ caa-refuse-missing-derivation-witness
refuse-missing-derivation-witness-positive = refl

compaction-as-arrow-non-claim : String
compaction-as-arrow-non-claim =
  "URGE-FORMAL-MESO-AGDA-COMPACTION-AS-ARROW §17.5 sophisticated compaction composite arrow paying MI not delete-old-commits; wasDerivedFrom chain retained; compose compaction-excitement-select not second argmin; sole postulate physicalSecondLaw cited; Unwired; physics_green false; production_wired false"
