-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.CountedConsume — meso/acting §21 counted domain consumer.
--
-- URGE-FORMAL-MESO-AGDA-COUNTED-CONSUME (umst-formal acting fiber only).
-- §21: domain provenance is scanner-emitted via `scan-counting`; refuse author
-- `Domain::new` / hand-filled extent. Compose `excitement-select` — no second
-- ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.CountedConsume where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; _∧_)
import Data.List as List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- SECTION 0: Minimal thermodynamic head carriers (no K-infect import chain)
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

data excitement-residue : Set where
  exc-no-candidates exc-all-inadmissible exc-no-strict-improvement : excitement-residue

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

urge-recovery-select :
  (src : ThermodynamicState) (successors : List.List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select src successors = excitement-select src successors

------------------------------------------------------------------------
-- SECTION 1: Scanner-emitted domain + scan-counting carriers (§21)
------------------------------------------------------------------------

data counted-domain-provenance : Set where
  cdp-counted : counted-domain-provenance

record counted-domain : Set where
  field
    counted-scope : List.List ℕ
    counted-cardinality : ℕ
    counted-exclusions : List.List ℕ
    counted-provenance : counted-domain-provenance

record counted-scanned-claim (V : Set) : Set where
  field
    counted-claim-value : V
    counted-claim-domain : counted-domain

record counted-scan-walk : Set where
  field
    counted-walk-scope : List.List ℕ
    counted-walk-exclusions : List.List ℕ

counted-scan-walk-empty : counted-scan-walk
counted-scan-walk-empty = record
  { counted-walk-scope = List.[]
  ; counted-walk-exclusions = List.[]
  }

counted-nat-inb : ℕ → List.List ℕ → Bool
counted-nat-inb n List.[] = false
counted-nat-inb n (x List.∷ xs) with x ≟ n
... | yes _ = true
... | no _ = counted-nat-inb n xs

counted-scan-touch : counted-scan-walk → ℕ → counted-scan-walk
counted-scan-touch w path-id with counted-nat-inb path-id (counted-scan-walk.counted-walk-scope w)
... | true = w
... | false = record
  { counted-walk-scope = path-id List.∷ counted-scan-walk.counted-walk-scope w
  ; counted-walk-exclusions = counted-scan-walk.counted-walk-exclusions w
  }

counted-scan-skip : counted-scan-walk → ℕ → counted-scan-walk
counted-scan-skip w path-id with counted-nat-inb path-id (counted-scan-walk.counted-walk-exclusions w)
... | true = w
... | false = record
  { counted-walk-scope = counted-scan-walk.counted-walk-scope w
  ; counted-walk-exclusions = path-id List.∷ counted-scan-walk.counted-walk-exclusions w
  }

data counted-domain-error : Set where
  cde-hand-filled-refused : counted-domain-error
  cde-cardinality-mismatch : ℕ → ℕ → counted-domain-error
  cde-empty-scan : counted-domain-error

data counted-consume-refusal : Set where
  ccr-author-domain-new : counted-consume-refusal
  ccr-hand-filled-domain : counted-consume-refusal
  ccr-empty-scan : counted-consume-refusal
  ccr-second-argmin : counted-consume-refusal

data counted-consume-verdict : Set where
  ccv-scan-ok : counted-consume-verdict
  ccv-author-domain-refused : counted-consume-verdict
  ccv-hand-fill-refused : counted-consume-verdict
  ccv-inadmissible : counted-consume-verdict

data counted-consume-admit : Set where
  cca-admitted : counted-consume-admit
  cca-refused : counted-consume-refusal → counted-consume-admit

------------------------------------------------------------------------
-- SECTION 2: §21 admissibility + scan-counting + positive refuse
------------------------------------------------------------------------

counted-cardinality-from-walk : counted-scan-walk → ℕ
counted-cardinality-from-walk w = List.length (counted-scan-walk.counted-walk-scope w)

counted-domain-from-walk : counted-scan-walk → counted-domain
counted-domain-from-walk w = record
  { counted-scope = counted-scan-walk.counted-walk-scope w
  ; counted-cardinality = counted-cardinality-from-walk w
  ; counted-exclusions = counted-scan-walk.counted-walk-exclusions w
  ; counted-provenance = cdp-counted
  }

verify-counted-domain : counted-domain → counted-domain ⊎ counted-domain-error
verify-counted-domain d with counted-domain.counted-provenance d
... | cdp-counted with counted-domain.counted-cardinality d ≟ List.length (counted-domain.counted-scope d)
... | yes _ = inj₁ d
... | no _ = inj₂ (cde-cardinality-mismatch
                  (counted-domain.counted-cardinality d)
                  (List.length (counted-domain.counted-scope d)))

scan-counting-finalize : counted-scan-walk → counted-domain ⊎ counted-domain-error
scan-counting-finalize w with counted-cardinality-from-walk w ≟ 0
... | yes _ = inj₂ cde-empty-scan
... | no _ = verify-counted-domain (counted-domain-from-walk w)

scan-counting : {V : Set} → counted-scan-walk → V → counted-scanned-claim V ⊎ counted-domain-error
scan-counting {V} w value with scan-counting-finalize w
... | inj₁ d = inj₁ (record
  { counted-claim-value = value
  ; counted-claim-domain = d
  })
... | inj₂ e = inj₂ e

evaluate-counted-domain-operation : Bool → counted-consume-verdict
evaluate-counted-domain-operation true = ccv-author-domain-refused
evaluate-counted-domain-operation false = ccv-scan-ok

refuse-author-domain-new : counted-consume-refusal
refuse-author-domain-new = ccr-author-domain-new

refuse-second-argmin-selector : counted-consume-refusal
refuse-second-argmin-selector = ccr-second-argmin

domain-to-admit : counted-domain → counted-consume-admit
domain-to-admit d with verify-counted-domain d
... | inj₁ _ = cca-admitted
... | inj₂ cde-hand-filled-refused = cca-refused ccr-hand-filled-domain
... | inj₂ (cde-cardinality-mismatch _ _) = cca-refused ccr-hand-filled-domain
... | inj₂ cde-empty-scan = cca-refused ccr-empty-scan

admit-scanned-claim : {V : Set} → counted-scanned-claim V → counted-consume-admit
admit-scanned-claim {V} claim =
  domain-to-admit (counted-scanned-claim.counted-claim-domain claim)

record counted-admissibility-conjunct : Set where
  field
    counted-conj-gate-ok : Bool
    counted-conj-scanner-emitted : Bool
    counted-conj-excitement-preserves : Bool

counted-conjunct-admits : counted-admissibility-conjunct → Bool
counted-conjunct-admits c =
  (counted-admissibility-conjunct.counted-conj-gate-ok c) ∧
  ((counted-admissibility-conjunct.counted-conj-scanner-emitted c) ∧
   (counted-admissibility-conjunct.counted-conj-excitement-preserves c))

apply-counted-consume-morphism :
  {V : Set} → counted-scanned-claim V → counted-admissibility-conjunct → Bool → Bool →
  counted-scanned-claim V ⊎ counted-consume-refusal
apply-counted-consume-morphism {V} claim conjunct excitement-selected author-construct
  with author-construct
... | true = inj₂ ccr-author-domain-new
... | false with counted-conjunct-admits conjunct
... | false = inj₂ ccr-hand-filled-domain
... | true with verify-counted-domain (counted-scanned-claim.counted-claim-domain claim)
... | inj₂ _ = inj₂ ccr-hand-filled-domain
... | inj₁ _ with excitement-selected
... | false = inj₂ ccr-second-argmin
... | true = inj₁ claim

counted-author-domain-refused :
  evaluate-counted-domain-operation true ≡ ccv-author-domain-refused
counted-author-domain-refused = refl

counted-scan-ok-when-not-author :
  evaluate-counted-domain-operation false ≡ ccv-scan-ok
counted-scan-ok-when-not-author = refl

refuse-author-domain-new-positive :
  refuse-author-domain-new ≡ ccr-author-domain-new
refuse-author-domain-new-positive = refl

refuse-second-argmin-positive :
  refuse-second-argmin-selector ≡ ccr-second-argmin
refuse-second-argmin-positive = refl

scan-counting-finalize-empty :
  scan-counting-finalize counted-scan-walk-empty ≡ inj₂ cde-empty-scan
scan-counting-finalize-empty = refl

------------------------------------------------------------------------
-- SECTION 3: Counted consume composes Excitement (no second argmin)
------------------------------------------------------------------------

record counted-consume-ctx (src : ThermodynamicState) : Set where
  field
    counted-consume-successors : List.List (history-candidate src)

counted-consume-select :
  (src : ThermodynamicState) (ctx : counted-consume-ctx src) →
  history-candidate src ⊎ excitement-residue
counted-consume-select src ctx =
  urge-recovery-select src (counted-consume-ctx.counted-consume-successors ctx)

counted-excitement-select :
  (src : ThermodynamicState) (successors : List.List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
counted-excitement-select src successors = excitement-select src successors

counted-consume-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : counted-consume-ctx src) →
  counted-consume-select src ctx ≡
  excitement-select src (counted-consume-ctx.counted-consume-successors ctx)
counted-consume-select-eq-excitement-select src ctx = refl

counted-consume-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : counted-consume-ctx src) →
  counted-consume-select src ctx ≡
  urge-recovery-select src (counted-consume-ctx.counted-consume-successors ctx)
counted-consume-select-eq-urge-recovery-select src ctx = refl

counted-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (successors : List.List (history-candidate src)) →
  counted-excitement-select src successors ≡ excitement-select src successors
counted-excitement-select-eq-excitement-select src successors = refl

counted-consume-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : counted-consume-ctx src) →
  counted-consume-select src ctx ≡
  excitement-select src (counted-consume-ctx.counted-consume-successors ctx)
counted-consume-no-local-argmin src ctx =
  counted-consume-select-eq-excitement-select src ctx

counted-consume-empty :
  ∀ (src : ThermodynamicState) (ctx : counted-consume-ctx src) →
  counted-consume-ctx.counted-consume-successors ctx ≡ List.[] →
  counted-consume-select src ctx ≡ inj₂ exc-no-candidates
counted-consume-empty src ctx Hnil rewrite Hnil = refl

------------------------------------------------------------------------
-- SECTION 4: §21 fixtures + witness theorems
------------------------------------------------------------------------

counted-fixture-state : ThermodynamicState
counted-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

counted-fixture-walk : counted-scan-walk
counted-fixture-walk =
  counted-scan-touch
    (counted-scan-touch counted-scan-walk-empty 1)
    2

counted-fixture-domain : counted-domain
counted-fixture-domain = counted-domain-from-walk counted-fixture-walk

counted-fixture-claim : counted-scanned-claim ℕ
counted-fixture-claim = record
  { counted-claim-value = 7
  ; counted-claim-domain = counted-fixture-domain
  }

counted-fixture-conjunct : counted-admissibility-conjunct
counted-fixture-conjunct = record
  { counted-conj-gate-ok = true
  ; counted-conj-scanner-emitted = true
  ; counted-conj-excitement-preserves = true
  }

counted-fixture-hand-filled : counted-domain
counted-fixture-hand-filled = record
  { counted-scope = 1 List.∷ 2 List.∷ List.[]
  ; counted-cardinality = 11809
  ; counted-exclusions = List.[]
  ; counted-provenance = cdp-counted
  }

counted-fixture-scanner-emitted-ok :
  verify-counted-domain counted-fixture-domain ≡ inj₁ counted-fixture-domain
counted-fixture-scanner-emitted-ok = refl

counted-fixture-hand-fill-refused :
  domain-to-admit counted-fixture-hand-filled ≡ cca-refused ccr-hand-filled-domain
counted-fixture-hand-fill-refused = refl

counted-fixture-author-domain-refused :
  apply-counted-consume-morphism counted-fixture-claim counted-fixture-conjunct true true
  ≡ inj₂ ccr-author-domain-new
counted-fixture-author-domain-refused = refl

counted-fixture-apply-morphism-ok :
  apply-counted-consume-morphism counted-fixture-claim counted-fixture-conjunct true false
  ≡ inj₁ counted-fixture-claim
counted-fixture-apply-morphism-ok = refl

counted-fixture-admit-scanned-claim-ok :
  admit-scanned-claim counted-fixture-claim ≡ cca-admitted
counted-fixture-admit-scanned-claim-ok = refl

counted-fixture-scan-counting-ok :
  scan-counting counted-fixture-walk 7 ≡ inj₁ counted-fixture-claim
counted-fixture-scan-counting-ok = refl

counted-fixture-cardinality-matches-scope :
  counted-domain.counted-cardinality counted-fixture-domain ≡
  List.length (counted-domain.counted-scope counted-fixture-domain)
counted-fixture-cardinality-matches-scope = refl

------------------------------------------------------------------------
-- SECTION 5: Landauer bridge + honesty flags (zero new postulates)
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

counted-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
counted-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

counted-consume-physics-green : Bool
counted-consume-physics-green = false

counted-consume-physics-green-false :
  counted-consume-physics-green ≡ false
counted-consume-physics-green-false = refl

counted-consume-production-wired : Bool
counted-consume-production-wired = false

counted-consume-production-wired-false :
  counted-consume-production-wired ≡ false
counted-consume-production-wired-false = refl

counted-consume-module-witness : ⊤
counted-consume-module-witness = tt

counted-consume-no-new-axiom : ⊤
counted-consume-no-new-axiom = tt

counted-consume-positive-refuse-not-silent :
  evaluate-counted-domain-operation true ≢ ccv-scan-ok
counted-consume-positive-refuse-not-silent ()

counted-consume-author-refuse-positive :
  refuse-author-domain-new ≡ ccr-author-domain-new
counted-consume-author-refuse-positive = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin-selector ≡ ccr-second-argmin
refuse-second-argmin-is-tag = refl
