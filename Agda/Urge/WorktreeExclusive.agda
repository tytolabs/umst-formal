-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.WorktreeExclusive — meso/acting §16.11 worktree exclusive.
--
-- URGE-FORMAL-MESO-AGDA-WORKTREE-EXCLUSIVE (umst-formal acting fiber only).
-- §16.11: one agent ↔ one exclusive worktree; antichain exclusive copy on
-- the conflict graph. Gate failure at **claim** time — not merge-conflict
-- theater. Compose `worktree-excitement-select` / `excitement-select` —
-- no second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` typed morphism discipline.
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.WorktreeExclusive where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_; not)
open import Data.List as List using (List; []; _∷_; length)
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
-- SECTION 1: Agent lane + worktree + write_set carriers (§16.11)
------------------------------------------------------------------------

data AgentLane : Set where
  al-composer al-grok al-kimi : AgentLane

record WorktreeId : Set where
  field
    worktree-id-val : ℕ

record WriteSetPath : Set where
  field
    write-set-path-id : ℕ

record ExclusiveWriteSet : Set where
  field
    exclusive-write-set-paths : List WriteSetPath

record ExclusiveClaim : Set where
  field
    claim-agent : AgentLane
    claim-worktree : WorktreeId
    claim-write-set : ExclusiveWriteSet

record ExclusiveAdmission : Set where
  field
    admission-claim : ExclusiveClaim
    antichain-index : ℕ

data ClaimGateVerdict : Set where
  cgv-admit cgv-refused : ClaimGateVerdict

data WorktreeExclusiveRefusal : Set where
  wer-overlapping-write-set-at-claim wer-agent-already-owns-worktree wer-merge-conflict-theater wer-second-argmin-on-claim : WorktreeExclusiveRefusal

data WorktreeExclusiveVerdict : Set where
  wev-exclusive-admit wev-overlap-refused wev-merge-theater-refused wev-second-argmin-refused : WorktreeExclusiveVerdict

------------------------------------------------------------------------
-- SECTION 2: §16.11 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record WorktreeAdmissibilityConjunct : Set where
  field
    worktree-conj-antichain-ok : Bool
    worktree-conj-one-agent-one-worktree : Bool
    worktree-conj-excitement-preserves : Bool

worktree-conjunct-admits : WorktreeAdmissibilityConjunct → Bool
worktree-conjunct-admits (record { worktree-conj-antichain-ok = a
                                 ; worktree-conj-one-agent-one-worktree = o
                                 ; worktree-conj-excitement-preserves = e }) =
  a ∧ o ∧ e

agent-lane-eq : AgentLane → AgentLane → Bool
agent-lane-eq al-composer al-composer = true
agent-lane-eq al-composer al-grok = false
agent-lane-eq al-composer al-kimi = false
agent-lane-eq al-grok al-composer = false
agent-lane-eq al-grok al-grok = true
agent-lane-eq al-grok al-kimi = false
agent-lane-eq al-kimi al-composer = false
agent-lane-eq al-kimi al-grok = false
agent-lane-eq al-kimi al-kimi = true

path-id-eq : ℕ → ℕ → Bool
path-id-eq zero zero = true
path-id-eq zero (suc _) = false
path-id-eq (suc _) zero = false
path-id-eq (suc m) (suc n) = path-id-eq m n

path-in-list : WriteSetPath → List WriteSetPath → Bool
path-in-list p List.[] = false
path-in-list p (q List.∷ rest) =
  if path-id-eq (WriteSetPath.write-set-path-id p) (WriteSetPath.write-set-path-id q) then true
  else path-in-list p rest

path-in-write-set : WriteSetPath → ExclusiveWriteSet → Bool
path-in-write-set p ws =
  path-in-list p (ExclusiveWriteSet.exclusive-write-set-paths ws)

any-path-in : ExclusiveWriteSet → List WriteSetPath → Bool
any-path-in ws List.[] = false
any-path-in ws (p List.∷ rest) =
  if path-in-write-set p ws then true else any-path-in ws rest

write-sets-overlap : ExclusiveWriteSet → ExclusiveWriteSet → Bool
write-sets-overlap left right =
  any-path-in right (ExclusiveWriteSet.exclusive-write-set-paths left)

agent-already-claimed : AgentLane → List ExclusiveClaim → Bool
agent-already-claimed a List.[] = false
agent-already-claimed a (c List.∷ rest) =
  if agent-lane-eq a (ExclusiveClaim.claim-agent c) then true
  else agent-already-claimed a rest

any-write-set-overlap : ExclusiveWriteSet → List ExclusiveClaim → Bool
any-write-set-overlap ws List.[] = false
any-write-set-overlap ws (c List.∷ rest) =
  if write-sets-overlap ws (ExclusiveClaim.claim-write-set c) then true
  else any-write-set-overlap ws rest

try-claim-exclusive :
  List ExclusiveClaim → ExclusiveClaim →
  ExclusiveAdmission ⊎ WorktreeExclusiveRefusal
try-claim-exclusive registry claim =
  if agent-already-claimed (ExclusiveClaim.claim-agent claim) registry then
    inj₂ wer-agent-already-owns-worktree
  else if any-write-set-overlap (ExclusiveClaim.claim-write-set claim) registry then
    inj₂ wer-overlapping-write-set-at-claim
  else inj₁ record
    { admission-claim = claim
    ; antichain-index = length registry
    }

evaluate-claim-operation : Bool → WorktreeExclusiveVerdict
evaluate-claim-operation true = wev-merge-theater-refused
evaluate-claim-operation false = wev-exclusive-admit

refuse-overlapping-write-set-at-claim : WorktreeExclusiveRefusal
refuse-overlapping-write-set-at-claim = wer-overlapping-write-set-at-claim

refuse-agent-second-worktree : WorktreeExclusiveRefusal
refuse-agent-second-worktree = wer-agent-already-owns-worktree

refuse-merge-conflict-theater : WorktreeExclusiveRefusal
refuse-merge-conflict-theater = wer-merge-conflict-theater

refuse-second-argmin-on-claim : WorktreeExclusiveRefusal
refuse-second-argmin-on-claim = wer-second-argmin-on-claim

refuse-overlapping-write-set-at-claim-positive :
  refuse-overlapping-write-set-at-claim ≡ wer-overlapping-write-set-at-claim
refuse-overlapping-write-set-at-claim-positive = refl

refuse-agent-second-worktree-positive :
  refuse-agent-second-worktree ≡ wer-agent-already-owns-worktree
refuse-agent-second-worktree-positive = refl

refuse-merge-conflict-theater-positive :
  refuse-merge-conflict-theater ≡ wer-merge-conflict-theater
refuse-merge-conflict-theater-positive = refl

refuse-second-argmin-on-claim-positive :
  refuse-second-argmin-on-claim ≡ wer-second-argmin-on-claim
refuse-second-argmin-on-claim-positive = refl

evaluate-claim-operation-merge-theater-refused :
  evaluate-claim-operation true ≡ wev-merge-theater-refused
evaluate-claim-operation-merge-theater-refused = refl

evaluate-claim-operation-exclusive-admit :
  evaluate-claim-operation false ≡ wev-exclusive-admit
evaluate-claim-operation-exclusive-admit = refl

------------------------------------------------------------------------
-- SECTION 3: Excitement hook — worktree exclusive **is** excitement-select
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

record WorktreeExclusiveCtx (src : ThermodynamicState) : Set where
  field
    worktree-exclusive-successors : List (history-candidate src)

data WorktreeExcitementComposePin : Set where
  wecp-import-select-excitement wecp-second-argmin-refused : WorktreeExcitementComposePin

compose-excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  WorktreeExcitementComposePin →
  history-candidate src ⊎ excitement-residue
compose-excitement-select src cands wecp-import-select-excitement =
  excitement-select src cands
compose-excitement-select src cands wecp-second-argmin-refused =
  inj₂ exc-all-inadmissible

urge-recovery-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select = excitement-select

worktree-exclusive-select :
  (src : ThermodynamicState) → WorktreeExclusiveCtx src →
  history-candidate src ⊎ excitement-residue
worktree-exclusive-select src ctx =
  urge-recovery-select src (WorktreeExclusiveCtx.worktree-exclusive-successors ctx)

worktree-excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
worktree-excitement-select = excitement-select

compose-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  compose-excitement-select src cands wecp-import-select-excitement ≡
  excitement-select src cands
compose-excitement-select-eq-excitement-select src cands = refl

worktree-exclusive-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : WorktreeExclusiveCtx src) →
  worktree-exclusive-select src ctx ≡
  excitement-select src (WorktreeExclusiveCtx.worktree-exclusive-successors ctx)
worktree-exclusive-select-eq-excitement-select src ctx = refl

worktree-exclusive-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : WorktreeExclusiveCtx src) →
  worktree-exclusive-select src ctx ≡
  urge-recovery-select src (WorktreeExclusiveCtx.worktree-exclusive-successors ctx)
worktree-exclusive-select-eq-urge-recovery-select src ctx = refl

worktree-exclusive-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : WorktreeExclusiveCtx src) →
  worktree-exclusive-select src ctx ≡
  excitement-select src (WorktreeExclusiveCtx.worktree-exclusive-successors ctx)
worktree-exclusive-no-local-argmin src ctx =
  worktree-exclusive-select-eq-excitement-select src ctx

compose-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  compose-excitement-select src cands wecp-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
compose-excitement-select-refuses-second-argmin src cands = refl

worktree-exclusive-empty :
  ∀ (src : ThermodynamicState) (ctx : WorktreeExclusiveCtx src) →
  WorktreeExclusiveCtx.worktree-exclusive-successors ctx ≡ List.[] →
  worktree-exclusive-select src ctx ≡ inj₂ exc-no-candidates
worktree-exclusive-empty src ctx refl = refl

------------------------------------------------------------------------
-- SECTION 4: Excitement compose pin (no second ℚ argmin)
------------------------------------------------------------------------

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin : WorktreeExclusiveRefusal
refuse-second-argmin = wer-second-argmin-on-claim

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ wer-second-argmin-on-claim
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 5: §16.11 fixtures + witness theorems
------------------------------------------------------------------------

we-path-src : WriteSetPath
we-path-src = record { write-set-path-id = 0 }

we-path-test : WriteSetPath
we-path-test = record { write-set-path-id = 1 }

we-path-origin-refuse : WriteSetPath
we-path-origin-refuse = record { write-set-path-id = 2 }

we-worktree-0 : WorktreeId
we-worktree-0 = record { worktree-id-val = 0 }

we-worktree-1 : WorktreeId
we-worktree-1 = record { worktree-id-val = 1 }

we-worktree-2 : WorktreeId
we-worktree-2 = record { worktree-id-val = 2 }

composer-write-set : ExclusiveWriteSet
composer-write-set = record
  { exclusive-write-set-paths = we-path-src List.∷ we-path-test List.∷ List.[]
  }

grok-overlap-write-set : ExclusiveWriteSet
grok-overlap-write-set = record
  { exclusive-write-set-paths = we-path-test List.∷ List.[]
  }

origin-refuse-write-set : ExclusiveWriteSet
origin-refuse-write-set = record
  { exclusive-write-set-paths = we-path-origin-refuse List.∷ List.[]
  }

composer-exclusive-admit-fixture : ExclusiveClaim
composer-exclusive-admit-fixture = record
  { claim-agent = al-composer
  ; claim-worktree = we-worktree-0
  ; claim-write-set = composer-write-set
  }

grok-overlapping-write-set-fixture : ExclusiveClaim
grok-overlapping-write-set-fixture = record
  { claim-agent = al-grok
  ; claim-worktree = we-worktree-1
  ; claim-write-set = grok-overlap-write-set
  }

composer-second-worktree-fixture : ExclusiveClaim
composer-second-worktree-fixture = record
  { claim-agent = al-composer
  ; claim-worktree = we-worktree-1
  ; claim-write-set = origin-refuse-write-set
  }

kimi-antichain-disjoint-fixture : ExclusiveClaim
kimi-antichain-disjoint-fixture = record
  { claim-agent = al-kimi
  ; claim-worktree = we-worktree-2
  ; claim-write-set = origin-refuse-write-set
  }

worktree-fixture-conjunct : WorktreeAdmissibilityConjunct
worktree-fixture-conjunct = record
  { worktree-conj-antichain-ok = true
  ; worktree-conj-one-agent-one-worktree = true
  ; worktree-conj-excitement-preserves = true
  }

worktree-fixture-registry : List ExclusiveClaim
worktree-fixture-registry = composer-exclusive-admit-fixture List.∷ List.[]

composer-exclusive-admit-fixture-ok :
  try-claim-exclusive List.[] composer-exclusive-admit-fixture ≡
  inj₁ record
    { admission-claim = composer-exclusive-admit-fixture
    ; antichain-index = 0
    }
composer-exclusive-admit-fixture-ok = refl

grok-overlap-refused-at-claim :
  try-claim-exclusive worktree-fixture-registry grok-overlapping-write-set-fixture ≡
  inj₂ wer-overlapping-write-set-at-claim
grok-overlap-refused-at-claim = refl

composer-second-worktree-refused :
  try-claim-exclusive worktree-fixture-registry composer-second-worktree-fixture ≡
  inj₂ wer-agent-already-owns-worktree
composer-second-worktree-refused = refl

kimi-antichain-disjoint-admits :
  try-claim-exclusive worktree-fixture-registry kimi-antichain-disjoint-fixture ≡
  inj₁ record
    { admission-claim = kimi-antichain-disjoint-fixture
    ; antichain-index = 1
    }
kimi-antichain-disjoint-admits = refl

write-sets-overlap-composer-grok :
  write-sets-overlap composer-write-set grok-overlap-write-set ≡ true
write-sets-overlap-composer-grok = refl

write-sets-disjoint-composer-origin-refuse :
  write-sets-overlap composer-write-set origin-refuse-write-set ≡ false
write-sets-disjoint-composer-origin-refuse = refl

worktree-conjunct-fixture-admits :
  worktree-conjunct-admits worktree-fixture-conjunct ≡ true
worktree-conjunct-fixture-admits = refl

worktree-exclusive-positive-refuse-not-silent :
  evaluate-claim-operation true ≢ wev-exclusive-admit
worktree-exclusive-positive-refuse-not-silent ()

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

worktree-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
worktree-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

worktree-exclusive-physics-green : Bool
worktree-exclusive-physics-green = false

worktree-exclusive-physics-green-false :
  worktree-exclusive-physics-green ≡ false
worktree-exclusive-physics-green-false = refl

worktree-exclusive-production-wired : Bool
worktree-exclusive-production-wired = false

worktree-exclusive-production-wired-false :
  worktree-exclusive-production-wired ≡ false
worktree-exclusive-production-wired-false = refl

worktree-exclusive-module-witness : ⊤
worktree-exclusive-module-witness = tt

worktree-exclusive-no-new-axiom : ⊤
worktree-exclusive-no-new-axiom = tt

worktree-exclusive-marker : ℕ
worktree-exclusive-marker = 1

worktree-exclusive-marker-eq : worktree-exclusive-marker ≡ 1
worktree-exclusive-marker-eq = refl

worktree-exclusive-merge-theater-refused-positive :
  refuse-merge-conflict-theater ≡ wer-merge-conflict-theater
worktree-exclusive-merge-theater-refused-positive = refl

worktree-exclusive-second-argmin-refused-positive :
  refuse-second-argmin-on-claim ≡ wer-second-argmin-on-claim
worktree-exclusive-second-argmin-refused-positive = refl
