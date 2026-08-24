-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.AntichainIndependent — meso/acting §22.2 conflict graph.
--
-- URGE-FORMAL-MESO-AGDA-ANTICHAIN-INDEPENDENT (umst-formal acting fiber only).
-- §22.2: conflict graph independent set — Urge **witnesses** prefix conflict
-- independent sets; does **not** fork `umst-adk` greedy `allocate_antichain`
-- or invent GREEN from antichain size. Compose `antichain-excitement-select`
-- — no second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` typed morphism discipline.
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.AntichainIndependent where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_)
open import Data.List as List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties as ℕ-Props using (_<?_)
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
-- SECTION 1: Conflict cell + graph + independent-set carriers (§22.2)
------------------------------------------------------------------------

record AntichainWritePath : Set where
  field
    antichain-path-zone : ℕ
    antichain-path-suffix : ℕ

record ConflictCell : Set where
  field
    conflict-cell-id : ℕ
    conflict-cell-write-set : List AntichainWritePath

record ConflictEdge : Set where
  field
    conflict-edge-left : ℕ
    conflict-edge-right : ℕ

record ConflictGraph : Set where
  field
    conflict-graph-nodes : List ℕ
    conflict-graph-edges : List ConflictEdge

data IndependentSetVerdict : Set where
  isv-admit isv-refuse-not-independent : IndependentSetVerdict

data AntichainIndependentRefusal : Set where
  air-fork-allocate-refused air-second-argmin-refused air-not-independent-set air-conflicting-neighbor air-greedy-mis-theater : AntichainIndependentRefusal

data AntichainIndependentVerdict : Set where
  aiv-independent-admit aiv-fork-allocate-refused aiv-greedy-mis-refused aiv-second-argmin-refused : AntichainIndependentVerdict

------------------------------------------------------------------------
-- SECTION 2: §22.2 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record AntichainAdmissibilityConjunct : Set where
  field
    antichain-conj-independent-ok : Bool
    antichain-conj-no-fork-allocate : Bool
    antichain-conj-excitement-preserves : Bool

antichain-conjunct-admits : AntichainAdmissibilityConjunct → Bool
antichain-conjunct-admits (record { antichain-conj-independent-ok = i
                                  ; antichain-conj-no-fork-allocate = f
                                  ; antichain-conj-excitement-preserves = e }) =
  i ∧ f ∧ e

nat-eqb : ℕ → ℕ → Bool
nat-eqb zero zero = true
nat-eqb zero (suc _) = false
nat-eqb (suc _) zero = false
nat-eqb (suc m) (suc n) = nat-eqb m n

nat-lt? : ℕ → ℕ → Bool
nat-lt? m n = does (ℕ-Props._<?_ m n)

antichain-paths-conflict-single : AntichainWritePath → AntichainWritePath → Bool
antichain-paths-conflict-single p q =
  nat-eqb (AntichainWritePath.antichain-path-zone p)
          (AntichainWritePath.antichain-path-zone q)

any-single-conflict : List AntichainWritePath → AntichainWritePath → Bool
any-single-conflict List.[] q = false
any-single-conflict (p List.∷ rest) q =
  if antichain-paths-conflict-single p q then true else any-single-conflict rest q

any-path-conflicts : List AntichainWritePath → List AntichainWritePath → Bool
any-path-conflicts left List.[] = false
any-path-conflicts left (q List.∷ rest) =
  if any-single-conflict left q then true else any-path-conflicts left rest

antichain-paths-conflict : List AntichainWritePath → List AntichainWritePath → Bool
antichain-paths-conflict left right =
  any-path-conflicts left right

canonical-conflict-edge : ℕ → ℕ → ConflictEdge
canonical-conflict-edge a b =
  if nat-lt? b a then
    record { conflict-edge-left = b ; conflict-edge-right = a }
  else
    record { conflict-edge-left = a ; conflict-edge-right = b }

node-in-list : ℕ → List ℕ → Bool
node-in-list n List.[] = false
node-in-list n (m List.∷ rest) =
  if nat-eqb n m then true else node-in-list n rest

edge-hits-selected : ConflictEdge → List ℕ → Bool
edge-hits-selected e selected =
  node-in-list (ConflictEdge.conflict-edge-left e) selected ∧
  node-in-list (ConflictEdge.conflict-edge-right e) selected

is-independent-set : List ConflictEdge → List ℕ → Bool
is-independent-set List.[] selected = true
is-independent-set (e List.∷ rest) selected =
  if edge-hits-selected e selected then false else is-independent-set rest selected

validate-independent-set :
  ConflictGraph → List ℕ →
  IndependentSetVerdict ⊎ AntichainIndependentRefusal
validate-independent-set g selected =
  if is-independent-set (ConflictGraph.conflict-graph-edges g) selected then
    inj₁ isv-admit
  else
    inj₂ air-not-independent-set

admit-antichain-member :
  ConflictCell → ConflictCell →
  IndependentSetVerdict ⊎ AntichainIndependentRefusal
admit-antichain-member incumbent candidate =
  if antichain-paths-conflict (ConflictCell.conflict-cell-write-set incumbent)
                              (ConflictCell.conflict-cell-write-set candidate) then
    inj₂ air-conflicting-neighbor
  else
    inj₁ isv-admit

refuse-fork-allocate : AntichainIndependentRefusal
refuse-fork-allocate = air-fork-allocate-refused

refuse-second-argmin-selector : AntichainIndependentRefusal
refuse-second-argmin-selector = air-second-argmin-refused

refuse-greedy-mis-theater : AntichainIndependentRefusal
refuse-greedy-mis-theater = air-greedy-mis-theater

physics-green-from-antichain-size : ℕ → Bool
physics-green-from-antichain-size size = false

evaluate-antichain-operation : Bool → AntichainIndependentVerdict
evaluate-antichain-operation true = aiv-fork-allocate-refused
evaluate-antichain-operation false = aiv-independent-admit

refuse-fork-allocate-positive :
  refuse-fork-allocate ≡ air-fork-allocate-refused
refuse-fork-allocate-positive = refl

refuse-second-argmin-selector-positive :
  refuse-second-argmin-selector ≡ air-second-argmin-refused
refuse-second-argmin-selector-positive = refl

refuse-greedy-mis-theater-positive :
  refuse-greedy-mis-theater ≡ air-greedy-mis-theater
refuse-greedy-mis-theater-positive = refl

antichain-size-never-invents-green :
  ∀ size → physics-green-from-antichain-size size ≡ false
antichain-size-never-invents-green size = refl

evaluate-antichain-operation-fork-refused :
  evaluate-antichain-operation true ≡ aiv-fork-allocate-refused
evaluate-antichain-operation-fork-refused = refl

evaluate-antichain-operation-witness-admit :
  evaluate-antichain-operation false ≡ aiv-independent-admit
evaluate-antichain-operation-witness-admit = refl

------------------------------------------------------------------------
-- SECTION 3: Antichain independent composes Excitement (no second argmin)
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

data AntichainExcitementComposePin : Set where
  aecp-import-select-excitement aecp-second-argmin-refused : AntichainExcitementComposePin

antichain-excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  AntichainExcitementComposePin →
  history-candidate src ⊎ excitement-residue
antichain-excitement-select src cands aecp-import-select-excitement =
  excitement-select src cands
antichain-excitement-select src cands aecp-second-argmin-refused =
  inj₂ exc-all-inadmissible

record AntichainIndependentCtx (src : ThermodynamicState) : Set where
  field
    antichain-independent-successors : List (history-candidate src)

urge-recovery-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select src successors = excitement-select src successors

antichain-independent-select :
  (src : ThermodynamicState) → AntichainIndependentCtx src →
  history-candidate src ⊎ excitement-residue
antichain-independent-select src ctx =
  urge-recovery-select src (AntichainIndependentCtx.antichain-independent-successors ctx)

antichain-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  antichain-excitement-select src cands aecp-import-select-excitement ≡
  excitement-select src cands
antichain-excitement-select-eq-excitement-select src cands = refl

antichain-independent-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : AntichainIndependentCtx src) →
  antichain-independent-select src ctx ≡
  excitement-select src (AntichainIndependentCtx.antichain-independent-successors ctx)
antichain-independent-select-eq-excitement-select src ctx = refl

antichain-independent-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : AntichainIndependentCtx src) →
  antichain-independent-select src ctx ≡
  urge-recovery-select src (AntichainIndependentCtx.antichain-independent-successors ctx)
antichain-independent-select-eq-urge-recovery-select src ctx = refl

antichain-independent-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : AntichainIndependentCtx src) →
  antichain-independent-select src ctx ≡
  excitement-select src (AntichainIndependentCtx.antichain-independent-successors ctx)
antichain-independent-no-local-argmin src ctx =
  antichain-independent-select-eq-excitement-select src ctx

antichain-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  antichain-excitement-select src cands aecp-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
antichain-excitement-select-refuses-second-argmin src cands = refl

antichain-independent-empty :
  ∀ (src : ThermodynamicState) (ctx : AntichainIndependentCtx src) →
  AntichainIndependentCtx.antichain-independent-successors ctx ≡ List.[] →
  antichain-independent-select src ctx ≡ inj₂ exc-no-candidates
antichain-independent-empty src ctx refl = refl

------------------------------------------------------------------------
-- SECTION 4: Excitement compose pin (no second ℚ argmin)
------------------------------------------------------------------------

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin : AntichainIndependentRefusal
refuse-second-argmin = air-second-argmin-refused

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ air-second-argmin-refused
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 5: §22.2 fixtures + witness theorems
------------------------------------------------------------------------

ai-path-zone-a : AntichainWritePath
ai-path-zone-a = record { antichain-path-zone = 1 ; antichain-path-suffix = 0 }

ai-path-zone-a-x : AntichainWritePath
ai-path-zone-a-x = record { antichain-path-zone = 1 ; antichain-path-suffix = 1 }

ai-path-zone-a-y : AntichainWritePath
ai-path-zone-a-y = record { antichain-path-zone = 1 ; antichain-path-suffix = 2 }

ai-fixture-accept : ConflictCell
ai-fixture-accept = record
  { conflict-cell-id = 0
  ; conflict-cell-write-set = ai-path-zone-a List.∷ List.[]
  }

ai-fixture-refuse-a : ConflictCell
ai-fixture-refuse-a = record
  { conflict-cell-id = 1
  ; conflict-cell-write-set = ai-path-zone-a-x List.∷ List.[]
  }

ai-fixture-refuse-b : ConflictCell
ai-fixture-refuse-b = record
  { conflict-cell-id = 2
  ; conflict-cell-write-set = ai-path-zone-a-y List.∷ List.[]
  }

ai-fixture-edge-0-1 : ConflictEdge
ai-fixture-edge-0-1 = canonical-conflict-edge 0 1

ai-fixture-edge-0-2 : ConflictEdge
ai-fixture-edge-0-2 = canonical-conflict-edge 0 2

ai-fixture-edge-1-2 : ConflictEdge
ai-fixture-edge-1-2 = canonical-conflict-edge 1 2

ai-fixture-graph : ConflictGraph
ai-fixture-graph = record
  { conflict-graph-nodes = 0 List.∷ 1 List.∷ 2 List.∷ List.[]
  ; conflict-graph-edges =
      ai-fixture-edge-0-1 List.∷
      ai-fixture-edge-0-2 List.∷
      ai-fixture-edge-1-2 List.∷
      List.[]
  }

ai-fixture-conjunct : AntichainAdmissibilityConjunct
ai-fixture-conjunct = record
  { antichain-conj-independent-ok = true
  ; antichain-conj-no-fork-allocate = true
  ; antichain-conj-excitement-preserves = true
  }

ai-fixture-accept-only-independent :
  validate-independent-set ai-fixture-graph (0 List.∷ List.[]) ≡ inj₁ isv-admit
ai-fixture-accept-only-independent = refl

ai-fixture-accept-refuse-a-conflicts :
  admit-antichain-member ai-fixture-accept ai-fixture-refuse-a ≡
  inj₂ air-conflicting-neighbor
ai-fixture-accept-refuse-a-conflicts = refl

ai-fixture-accept-refuse-b-conflicts :
  admit-antichain-member ai-fixture-accept ai-fixture-refuse-b ≡
  inj₂ air-conflicting-neighbor
ai-fixture-accept-refuse-b-conflicts = refl

ai-fixture-paths-conflict-accept-a :
  antichain-paths-conflict (ConflictCell.conflict-cell-write-set ai-fixture-accept)
                           (ConflictCell.conflict-cell-write-set ai-fixture-refuse-a) ≡
  true
ai-fixture-paths-conflict-accept-a = refl

ai-fixture-not-independent-pair :
  validate-independent-set ai-fixture-graph (0 List.∷ 1 List.∷ List.[]) ≡
  inj₂ air-not-independent-set
ai-fixture-not-independent-pair = refl

ai-fixture-conjunct-admits :
  antichain-conjunct-admits ai-fixture-conjunct ≡ true
ai-fixture-conjunct-admits = refl

ai-fixture-antichain-size-no-green :
  physics-green-from-antichain-size (length (ConflictGraph.conflict-graph-nodes ai-fixture-graph)) ≡
  false
ai-fixture-antichain-size-no-green = refl

antichain-independent-positive-refuse-not-silent :
  evaluate-antichain-operation true ≢ aiv-independent-admit
antichain-independent-positive-refuse-not-silent ()

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

antichain-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
antichain-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

antichain-independent-physics-green : Bool
antichain-independent-physics-green = false

antichain-independent-physics-green-false :
  antichain-independent-physics-green ≡ false
antichain-independent-physics-green-false = refl

antichain-independent-production-wired : Bool
antichain-independent-production-wired = false

antichain-independent-production-wired-false :
  antichain-independent-production-wired ≡ false
antichain-independent-production-wired-false = refl

antichain-independent-module-witness : ⊤
antichain-independent-module-witness = tt

antichain-independent-no-new-axiom : ⊤
antichain-independent-no-new-axiom = tt

antichain-independent-marker : ℕ
antichain-independent-marker = 1

antichain-independent-marker-eq : antichain-independent-marker ≡ 1
antichain-independent-marker-eq = refl

antichain-independent-fork-allocate-refused-positive :
  refuse-fork-allocate ≡ air-fork-allocate-refused
antichain-independent-fork-allocate-refused-positive = refl

antichain-independent-second-argmin-refused-positive :
  refuse-second-argmin-selector ≡ air-second-argmin-refused
antichain-independent-second-argmin-refused-positive = refl

antichain-independent-greedy-mis-refused-positive :
  refuse-greedy-mis-theater ≡ air-greedy-mis-theater
antichain-independent-greedy-mis-refused-positive = refl

antichain-independent-never-invents-green-from-size :
  ∀ size → physics-green-from-antichain-size size ≡ false
antichain-independent-never-invents-green-from-size size =
  antichain-size-never-invents-green size
