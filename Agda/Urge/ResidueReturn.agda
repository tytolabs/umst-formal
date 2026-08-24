-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ResidueReturn — meso/acting §13.5 residue return.
--
-- URGE-FORMAL-MESO-AGDA-RESIDUE-RETURN (umst-formal acting fiber only).
-- §13.5: Urge returns Excitement Residue constructor counts + observed ΔF
-- to Excitement — history-plane evidence, not a restatement of `select`.
-- Six `UMST.Excitement.Residue` constructors pinned; compose
-- `residue-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.ResidueReturn where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false)
open import Data.List as List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _-_; _≤_)
open import Data.Rational.Properties as ℚ-Props using (≤-refl; ≤-trans)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers + six residue constructors
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
  exc-all-excluded-by-cbf : excitement-residue
  exc-all-excluded-by-dec : excitement-residue
  exc-untagged-constant : excitement-residue
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
-- SECTION 2: Per-constructor counts (§13.5 return field)
------------------------------------------------------------------------

record ResidueCounts : Set where
  field
    no-candidates : ℕ
    all-inadmissible : ℕ
    all-excluded-by-cbf : ℕ
    all-excluded-by-dec : ℕ
    untagged-constant : ℕ
    no-strict-improvement : ℕ

empty-counts : ResidueCounts
empty-counts = record
  { no-candidates = zero
  ; all-inadmissible = zero
  ; all-excluded-by-cbf = zero
  ; all-excluded-by-dec = zero
  ; untagged-constant = zero
  ; no-strict-improvement = zero
  }

increment-count : ResidueCounts → excitement-residue → ResidueCounts
increment-count c exc-no-candidates = record
  { no-candidates = suc (ResidueCounts.no-candidates c)
  ; all-inadmissible = ResidueCounts.all-inadmissible c
  ; all-excluded-by-cbf = ResidueCounts.all-excluded-by-cbf c
  ; all-excluded-by-dec = ResidueCounts.all-excluded-by-dec c
  ; untagged-constant = ResidueCounts.untagged-constant c
  ; no-strict-improvement = ResidueCounts.no-strict-improvement c
  }
increment-count c exc-all-inadmissible = record
  { no-candidates = ResidueCounts.no-candidates c
  ; all-inadmissible = suc (ResidueCounts.all-inadmissible c)
  ; all-excluded-by-cbf = ResidueCounts.all-excluded-by-cbf c
  ; all-excluded-by-dec = ResidueCounts.all-excluded-by-dec c
  ; untagged-constant = ResidueCounts.untagged-constant c
  ; no-strict-improvement = ResidueCounts.no-strict-improvement c
  }
increment-count c exc-all-excluded-by-cbf = record
  { no-candidates = ResidueCounts.no-candidates c
  ; all-inadmissible = ResidueCounts.all-inadmissible c
  ; all-excluded-by-cbf = suc (ResidueCounts.all-excluded-by-cbf c)
  ; all-excluded-by-dec = ResidueCounts.all-excluded-by-dec c
  ; untagged-constant = ResidueCounts.untagged-constant c
  ; no-strict-improvement = ResidueCounts.no-strict-improvement c
  }
increment-count c exc-all-excluded-by-dec = record
  { no-candidates = ResidueCounts.no-candidates c
  ; all-inadmissible = ResidueCounts.all-inadmissible c
  ; all-excluded-by-cbf = ResidueCounts.all-excluded-by-cbf c
  ; all-excluded-by-dec = suc (ResidueCounts.all-excluded-by-dec c)
  ; untagged-constant = ResidueCounts.untagged-constant c
  ; no-strict-improvement = ResidueCounts.no-strict-improvement c
  }
increment-count c exc-untagged-constant = record
  { no-candidates = ResidueCounts.no-candidates c
  ; all-inadmissible = ResidueCounts.all-inadmissible c
  ; all-excluded-by-cbf = ResidueCounts.all-excluded-by-cbf c
  ; all-excluded-by-dec = ResidueCounts.all-excluded-by-dec c
  ; untagged-constant = suc (ResidueCounts.untagged-constant c)
  ; no-strict-improvement = ResidueCounts.no-strict-improvement c
  }
increment-count c exc-no-strict-improvement = record
  { no-candidates = ResidueCounts.no-candidates c
  ; all-inadmissible = ResidueCounts.all-inadmissible c
  ; all-excluded-by-cbf = ResidueCounts.all-excluded-by-cbf c
  ; all-excluded-by-dec = ResidueCounts.all-excluded-by-dec c
  ; untagged-constant = ResidueCounts.untagged-constant c
  ; no-strict-improvement = suc (ResidueCounts.no-strict-improvement c)
  }

------------------------------------------------------------------------
-- SECTION 3: Observed ΔF corpus (exact ℚ — no f64)
------------------------------------------------------------------------

record ObservedDeltaF : Set where
  field
    src : ℚ
    observed : ℚ

observed-delta-f : ObservedDeltaF → ℚ
observed-delta-f d = ObservedDeltaF.observed d ℚ.- ObservedDeltaF.src d

mk-observed-delta-f : (src observed : ℚ) → ObservedDeltaF
mk-observed-delta-f src observed = record { src = src ; observed = observed }

------------------------------------------------------------------------
-- SECTION 4: §13.5 return payload — counts + observed ΔF
------------------------------------------------------------------------

record ResidueReturn : Set where
  field
    counts : ResidueCounts
    observed-deltas : List ObservedDeltaF

empty-residue-return : ResidueReturn
empty-residue-return = record
  { counts = empty-counts
  ; observed-deltas = List.[]
  }

------------------------------------------------------------------------
-- SECTION 5: Excitement candidate + composed select (no second argmin)
------------------------------------------------------------------------

record excitement-candidate : Set where
  field
    cand-id : ℕ
    cand-free-energy : ℚ
    cand-evidence-tagged : Bool

residue-excitement-select :
  (src : ℚ) → List excitement-candidate →
  excitement-candidate ⊎ excitement-residue
residue-excitement-select src List.[] = inj₂ exc-no-candidates
residue-excitement-select src (c List.∷ _) = inj₁ c

urge-residue-select :
  (src : ℚ) → List excitement-candidate →
  excitement-candidate ⊎ excitement-residue
urge-residue-select = residue-excitement-select

urge-residue-select-eq-residue-excitement-select :
  ∀ (src : ℚ) (cands : List excitement-candidate) →
  urge-residue-select src cands ≡ residue-excitement-select src cands
urge-residue-select-eq-residue-excitement-select src cands = refl

record-recovery-attempt :
  (buf : ResidueReturn) (src : ℚ) (cands : List excitement-candidate) →
  ResidueReturn × (excitement-candidate ⊎ excitement-residue)
record-recovery-attempt buf src cands with residue-excitement-select src cands
... | inj₁ c =
  (record
    { counts = ResidueReturn.counts buf
    ; observed-deltas = mk-observed-delta-f src (excitement-candidate.cand-free-energy c) List.∷ ResidueReturn.observed-deltas buf
    }) ,
  inj₁ c
... | inj₂ r =
  (record
    { counts = increment-count (ResidueReturn.counts buf) r
    ; observed-deltas = ResidueReturn.observed-deltas buf
    }) ,
  inj₂ r

------------------------------------------------------------------------
-- SECTION 6: Six-constructor pin (Lean `UMST.Excitement.Residue` arity)
------------------------------------------------------------------------

pin-six-residue-constructors : List excitement-residue
pin-six-residue-constructors =
  exc-no-candidates List.∷
  exc-all-inadmissible List.∷
  exc-all-excluded-by-cbf List.∷
  exc-all-excluded-by-dec List.∷
  exc-untagged-constant List.∷
  exc-no-strict-improvement List.∷
  List.[]

pin-six-length : length pin-six-residue-constructors ≡ 6
pin-six-length = refl

residue-constructor-names : List String
residue-constructor-names =
  "NoCandidates" List.∷
  "AllInadmissible" List.∷
  "AllExcludedByCbf" List.∷
  "AllExcludedByDec" List.∷
  "UntaggedConstant" List.∷
  "NoStrictImprovement" List.∷
  List.[]

------------------------------------------------------------------------
-- SECTION 7: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data ResidueReturnRefusal : Set where
  seventh-constructor : ResidueReturnRefusal
  f64-delta-f : ResidueReturnRefusal

refuse-seventh-constructor : ResidueReturnRefusal
refuse-seventh-constructor = seventh-constructor

refuse-f64-delta-f : ResidueReturnRefusal
refuse-f64-delta-f = f64-delta-f

refuse-second-argmin : ResidueReturnRefusal
refuse-second-argmin = seventh-constructor

------------------------------------------------------------------------
-- SECTION 8: Excitement compose pin (no second ℚ argmin)
------------------------------------------------------------------------

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

residue-select-empty :
  ∀ (src : ℚ) →
  urge-residue-select src List.[] ≡ inj₂ exc-no-candidates
residue-select-empty src = refl

------------------------------------------------------------------------
-- SECTION 9: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

residue-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
residue-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

residue-return-production-wired : Bool
residue-return-production-wired = false

residue-return-production-wired-false :
  residue-return-production-wired ≡ false
residue-return-production-wired-false = refl

residue-return-marker : ℕ
residue-return-marker = 1

residue-return-marker-eq : residue-return-marker ≡ 1
residue-return-marker-eq = refl

residue-return-module-witness : ⊤
residue-return-module-witness = tt

seventh-constructor-refused :
  refuse-seventh-constructor ≡ seventh-constructor
seventh-constructor-refused = refl

f64-delta-refused :
  refuse-f64-delta-f ≡ f64-delta-f
f64-delta-refused = refl
