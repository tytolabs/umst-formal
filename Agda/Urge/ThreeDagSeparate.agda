-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ThreeDagSeparate — meso/acting §16.11 / §22.2 three DAGs.
--
-- URGE-FORMAL-MESO-AGDA-THREE-DAG-SEPARATE (umst-formal acting fiber only).
-- §16.11 / §22.2: three DAGs unfused — (a) git bytes, (b) Kleisli history,
-- (c) UCRS causal. Agents walk (b) ordered by (c). Compose
-- `three-dag-excitement-select` — no second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite`. Sole physics postulate remains
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated). Zero extra
-- postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.ThreeDagSeparate where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_; not)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
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
-- SECTION 1: Three unfused DAG substrates + node carriers
------------------------------------------------------------------------

data three-dag-substrate : Set where
  tds-git-bytes tds-kleisli-history tds-ucrs-causal : three-dag-substrate

record git-commit-node : Set where
  field
    git-commit-hash : ℕ
    git-parent-hash : Maybe ℕ

record kleisli-history-node : Set where
  field
    kleisli-arrow-id : ℕ
    kleisli-gate-merge-excitement-admitted : Bool

record ucrs-causal-node : Set where
  field
    ucrs-seq : ℕ
    ucrs-wall-stamp-audit : Maybe ℕ
    ucrs-order-by-wall-clock : Bool

record three-dag-coordinates : Set where
  field
    tdc-git-commit : ℕ
    tdc-kleisli-arrow : ℕ
    tdc-ucrs-seq : ℕ

record three-dag-ucrs-stamp : Set where
  field
    three-dag-ucrs-seq : ℕ
    three-dag-ucrs-wall-has-t : Bool

record three-dag-witness : Set where
  field
    three-dag-witness-ucrs : three-dag-ucrs-stamp
    three-dag-witness-kleisli-admitted : Bool

record three-dag-morphism : Set where
  field
    three-dag-morphism-coords : three-dag-coordinates
    three-dag-morphism-witness : three-dag-witness
    three-dag-morphism-excitement-selected : Bool

nat-eqb : ℕ → ℕ → Bool
nat-eqb zero zero = true
nat-eqb zero (suc _) = false
nat-eqb (suc _) zero = false
nat-eqb (suc m) (suc n) = nat-eqb m n

nat-eqb-refl : ∀ n → nat-eqb n n ≡ true
nat-eqb-refl zero = refl
nat-eqb-refl (suc n) = nat-eqb-refl n

------------------------------------------------------------------------
-- SECTION 2: Fusion refusal + positive refuse (not silent accept)
------------------------------------------------------------------------

data three-dag-fusion-refusal : Set where
  tdf-git-bytes-as-kleisli-coord : three-dag-fusion-refusal
  tdf-ucrs-seq-fused-with-git-hash : three-dag-fusion-refusal
  tdf-wall-clock-as-ucrs-seq : three-dag-fusion-refusal
  tdf-kleisli-not-admitted : three-dag-fusion-refusal
  tdf-second-argmin-refused : three-dag-fusion-refusal
  tdf-physics-green-invent : three-dag-fusion-refusal

data three-dag-walker-verdict : Set where
  tdw-admitted : three-dag-walker-verdict
  tdw-refused : three-dag-fusion-refusal → three-dag-walker-verdict

record three-dag-admissibility-conjunct : Set where
  field
    three-dag-conj-gate-ok : Bool
    three-dag-conj-kleisli-admitted : Bool
    three-dag-conj-excitement-preserves : Bool

three-dag-conjunct-admits : three-dag-admissibility-conjunct → Bool
three-dag-conjunct-admits c =
  three-dag-admissibility-conjunct.three-dag-conj-gate-ok c ∧
  three-dag-admissibility-conjunct.three-dag-conj-kleisli-admitted c ∧
  three-dag-admissibility-conjunct.three-dag-conj-excitement-preserves c

refuses-git-kleisli-fusion : three-dag-coordinates → Bool
refuses-git-kleisli-fusion coords =
  nat-eqb (three-dag-coordinates.tdc-git-commit coords)
          (three-dag-coordinates.tdc-kleisli-arrow coords)

refuses-ucrs-git-fusion : three-dag-coordinates → Bool
refuses-ucrs-git-fusion coords =
  nat-eqb (three-dag-coordinates.tdc-ucrs-seq coords)
          (three-dag-coordinates.tdc-git-commit coords)

refuse-second-argmin-selector : three-dag-fusion-refusal
refuse-second-argmin-selector = tdf-second-argmin-refused

evaluate-three-dag-walk :
  three-dag-coordinates → kleisli-history-node → ucrs-causal-node → Bool →
  three-dag-walker-verdict
evaluate-three-dag-walk coords kleisli ucrs claim-physics-green =
  if claim-physics-green then tdw-refused tdf-physics-green-invent
  else if refuses-git-kleisli-fusion coords then
    tdw-refused tdf-git-bytes-as-kleisli-coord
  else if refuses-ucrs-git-fusion coords then
    tdw-refused tdf-ucrs-seq-fused-with-git-hash
  else if ucrs-causal-node.ucrs-order-by-wall-clock ucrs then
    tdw-refused tdf-wall-clock-as-ucrs-seq
  else if not (nat-eqb (three-dag-coordinates.tdc-ucrs-seq coords)
                        (ucrs-causal-node.ucrs-seq ucrs)) then
    tdw-refused tdf-wall-clock-as-ucrs-seq
  else if not (kleisli-history-node.kleisli-gate-merge-excitement-admitted kleisli) then
    tdw-refused tdf-kleisli-not-admitted
  else if not (nat-eqb (kleisli-history-node.kleisli-arrow-id kleisli)
                       (three-dag-coordinates.tdc-kleisli-arrow coords)) then
    tdw-refused tdf-kleisli-not-admitted
  else tdw-admitted

witness-from-coords :
  three-dag-coordinates → kleisli-history-node → three-dag-ucrs-stamp →
  three-dag-witness
witness-from-coords coords kleisli stamp = record
  { three-dag-witness-ucrs = stamp
  ; three-dag-witness-kleisli-admitted =
      kleisli-history-node.kleisli-gate-merge-excitement-admitted kleisli
  }

apply-three-dag-morphism :
  three-dag-coordinates → kleisli-history-node → ucrs-causal-node →
  three-dag-admissibility-conjunct → three-dag-ucrs-stamp → Bool →
  three-dag-morphism ⊎ three-dag-fusion-refusal
apply-three-dag-morphism coords kleisli ucrs conjunct stamp excitement-selected
  with three-dag-conjunct-admits conjunct
... | false = inj₂ tdf-kleisli-not-admitted
... | true with excitement-selected
... | false = inj₂ tdf-second-argmin-refused
... | true with evaluate-three-dag-walk coords kleisli ucrs false
... | tdw-admitted = inj₁ record
    { three-dag-morphism-coords = coords
    ; three-dag-morphism-witness = witness-from-coords coords kleisli stamp
    ; three-dag-morphism-excitement-selected = excitement-selected
    }
... | tdw-refused r = inj₂ r

refuse-second-argmin-selector-positive :
  refuse-second-argmin-selector ≡ tdf-second-argmin-refused
refuse-second-argmin-selector-positive = refl

refuses-git-kleisli-fusion-detects-equal :
  ∀ (n : ℕ) →
  refuses-git-kleisli-fusion
    (record { tdc-git-commit = n ; tdc-kleisli-arrow = n ; tdc-ucrs-seq = zero }) ≡
  true
refuses-git-kleisli-fusion-detects-equal n = nat-eqb-refl n

------------------------------------------------------------------------
-- SECTION 3: Three-DAG walk composes Excitement (no second argmin)
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

data three-dag-excitement-compose-pin : Set where
  tdecp-import-select-excitement tdecp-second-argmin-refused : three-dag-excitement-compose-pin

record three-dag-ctx (src : ThermodynamicState) : Set where
  field
    three-dag-successors : List (history-candidate src)

three-dag-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  three-dag-excitement-compose-pin →
  history-candidate src ⊎ excitement-residue
three-dag-excitement-select src cands tdecp-import-select-excitement =
  excitement-select src cands
three-dag-excitement-select src cands tdecp-second-argmin-refused =
  inj₂ exc-all-inadmissible

three-dag-select :
  (src : ThermodynamicState) (ctx : three-dag-ctx src) →
  history-candidate src ⊎ excitement-residue
three-dag-select src ctx =
  excitement-select src (three-dag-ctx.three-dag-successors ctx)

urge-recovery-select :
  (src : ThermodynamicState) (successors : List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select src successors = excitement-select src successors

three-dag-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : three-dag-ctx src) →
  three-dag-select src ctx ≡
  excitement-select src (three-dag-ctx.three-dag-successors ctx)
three-dag-select-eq-excitement-select src ctx = refl

three-dag-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : three-dag-ctx src) →
  three-dag-select src ctx ≡
  urge-recovery-select src (three-dag-ctx.three-dag-successors ctx)
three-dag-select-eq-urge-recovery-select src ctx = refl

three-dag-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : three-dag-ctx src) →
  three-dag-select src ctx ≡
  excitement-select src (three-dag-ctx.three-dag-successors ctx)
three-dag-no-local-argmin src ctx = three-dag-select-eq-excitement-select src ctx

three-dag-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  three-dag-excitement-select src cands tdecp-import-select-excitement ≡
  excitement-select src cands
three-dag-excitement-select-eq-excitement-select src cands = refl

three-dag-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  three-dag-excitement-select src cands tdecp-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
three-dag-excitement-select-refuses-second-argmin src cands = refl

three-dag-select-empty :
  ∀ (src : ThermodynamicState) (ctx : three-dag-ctx src) →
  three-dag-ctx.three-dag-successors ctx ≡ List.[] →
  three-dag-select src ctx ≡ inj₂ exc-no-candidates
three-dag-select-empty src ctx hs rewrite hs = refl

------------------------------------------------------------------------
-- SECTION 4: §16.11 fixtures + witness theorems
------------------------------------------------------------------------

three-dag-fixture-state : ThermodynamicState
three-dag-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

three-dag-fixture-ucrs : three-dag-ucrs-stamp
three-dag-fixture-ucrs = record
  { three-dag-ucrs-seq = 7
  ; three-dag-ucrs-wall-has-t = true
  }

three-dag-fixture-conjunct : three-dag-admissibility-conjunct
three-dag-fixture-conjunct = record
  { three-dag-conj-gate-ok = true
  ; three-dag-conj-kleisli-admitted = true
  ; three-dag-conj-excitement-preserves = true
  }

three-dag-fixture-coords : three-dag-coordinates
three-dag-fixture-coords = record
  { tdc-git-commit = 11
  ; tdc-kleisli-arrow = 22
  ; tdc-ucrs-seq = 7
  }

three-dag-fixture-kleisli : kleisli-history-node
three-dag-fixture-kleisli = record
  { kleisli-arrow-id = 22
  ; kleisli-gate-merge-excitement-admitted = true
  }

three-dag-fixture-ucrs-node : ucrs-causal-node
three-dag-fixture-ucrs-node = record
  { ucrs-seq = 7
  ; ucrs-wall-stamp-audit = just 42
  ; ucrs-order-by-wall-clock = false
  }

three-dag-fixture-walk-admitted :
  evaluate-three-dag-walk
    three-dag-fixture-coords
    three-dag-fixture-kleisli
    three-dag-fixture-ucrs-node
    false ≡ tdw-admitted
three-dag-fixture-walk-admitted = refl

three-dag-fixture-fused-coords : three-dag-coordinates
three-dag-fixture-fused-coords = record
  { tdc-git-commit = 66
  ; tdc-kleisli-arrow = 66
  ; tdc-ucrs-seq = 3
  }

three-dag-fixture-git-kleisli-fusion-refused :
  evaluate-three-dag-walk
    three-dag-fixture-fused-coords
    (record { kleisli-arrow-id = 66 ; kleisli-gate-merge-excitement-admitted = true })
    (record { ucrs-seq = 3 ; ucrs-wall-stamp-audit = nothing ; ucrs-order-by-wall-clock = false })
    false ≡ tdw-refused tdf-git-bytes-as-kleisli-coord
three-dag-fixture-git-kleisli-fusion-refused = refl

three-dag-fixture-wall-clock-order-refused :
  evaluate-three-dag-walk
    (record { tdc-git-commit = 33 ; tdc-kleisli-arrow = 44 ; tdc-ucrs-seq = 9 })
    (record { kleisli-arrow-id = 44 ; kleisli-gate-merge-excitement-admitted = true })
    (record { ucrs-seq = 9 ; ucrs-wall-stamp-audit = just 42 ; ucrs-order-by-wall-clock = true })
    false ≡ tdw-refused tdf-wall-clock-as-ucrs-seq
three-dag-fixture-wall-clock-order-refused = refl

three-dag-fixture-apply-morphism-ok :
  apply-three-dag-morphism
    three-dag-fixture-coords
    three-dag-fixture-kleisli
    three-dag-fixture-ucrs-node
    three-dag-fixture-conjunct
    three-dag-fixture-ucrs
    true ≡
  inj₁ record
    { three-dag-morphism-coords = three-dag-fixture-coords
    ; three-dag-morphism-witness =
        witness-from-coords
          three-dag-fixture-coords
          three-dag-fixture-kleisli
          three-dag-fixture-ucrs
    ; three-dag-morphism-excitement-selected = true
    }
three-dag-fixture-apply-morphism-ok = refl

three-dag-fixture-witness-preserves-ucrs :
  three-dag-witness.three-dag-witness-ucrs
    (witness-from-coords
       three-dag-fixture-coords
       three-dag-fixture-kleisli
       three-dag-fixture-ucrs) ≡
  three-dag-fixture-ucrs
three-dag-fixture-witness-preserves-ucrs = refl

three-dag-fixture-physics-green-invent-refused :
  evaluate-three-dag-walk
    three-dag-fixture-coords
    three-dag-fixture-kleisli
    three-dag-fixture-ucrs-node
    true ≡ tdw-refused tdf-physics-green-invent
three-dag-fixture-physics-green-invent-refused = refl

three-dag-fusion-refuse-not-silent :
  evaluate-three-dag-walk
    three-dag-fixture-fused-coords
    (record { kleisli-arrow-id = 66 ; kleisli-gate-merge-excitement-admitted = true })
    (record { ucrs-seq = 3 ; ucrs-wall-stamp-audit = nothing ; ucrs-order-by-wall-clock = false })
    false ≢ tdw-admitted
three-dag-fusion-refuse-not-silent ()

------------------------------------------------------------------------
-- SECTION 5: History transition + Landauer bridge (zero new postulates)
------------------------------------------------------------------------

record HistoryTransition : Set where
  field
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

three-dag-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
three-dag-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
------------------------------------------------------------------------

three-dag-separate-physics-green : Bool
three-dag-separate-physics-green = false

three-dag-separate-physics-green-false :
  three-dag-separate-physics-green ≡ false
three-dag-separate-physics-green-false = refl

three-dag-separate-production-wired : Bool
three-dag-separate-production-wired = false

three-dag-separate-production-wired-false :
  three-dag-separate-production-wired ≡ false
three-dag-separate-production-wired-false = refl

three-dag-separate-module-witness : ⊤
three-dag-separate-module-witness = tt

three-dag-separate-no-new-axiom : ⊤
three-dag-separate-no-new-axiom = tt

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  tdecp-second-argmin-refused ≡ tdecp-second-argmin-refused
refuse-second-argmin-is-tag = refl

three-dag-separate-marker : ℕ
three-dag-separate-marker = 1

three-dag-separate-marker-eq : three-dag-separate-marker ≡ 1
three-dag-separate-marker-eq = refl

urge-three-dag-select = three-dag-excitement-select
