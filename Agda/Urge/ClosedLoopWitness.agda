-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ClosedLoopWitness — meso/acting §22.7 closed-loop witness.
--
-- URGE-FORMAL-MESO-AGDA-CLOSED-LOOP-WITNESS (umst-formal acting fiber only).
-- §22.7: messy witness residue counts + observed ΔF feed Excitement occupancy
-- surrogate. Compose `closed-loop-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.ClosedLoopWitness where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Integer.Base as ℤ using (ℤ; +_; ∣_∣)
open import Data.List as List using (List; []; _∷_; length)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Coprimality as Cop using (1-coprimeTo)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; mkℚ; _-_; _≤_)
open import Data.Rational.Properties as ℚ-Props using (_<?_; ≤-refl; ≤-trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; subst; sym; _≢_)
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

admissible-refl : ∀ (s : ThermodynamicState) → Admissible s s
admissible-refl s = admissible-any

------------------------------------------------------------------------
-- SECTION 1: Messy witness + occupancy feedback carriers (§22.7)
------------------------------------------------------------------------

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-all-excluded-by-cbf : excitement-residue
  exc-all-excluded-by-dec : excitement-residue
  exc-untagged-constant : excitement-residue
  exc-no-strict-improvement : excitement-residue

data closed-loop-residue : Set where
  clr-no-candidates : closed-loop-residue
  clr-all-inadmissible : closed-loop-residue
  clr-all-excluded-by-cbf : closed-loop-residue
  clr-all-excluded-by-dec : closed-loop-residue
  clr-untagged-constant : closed-loop-residue
  clr-no-strict-improvement : closed-loop-residue

record closed-loop-residue-counts : Set where
  field
    no-candidates : ℕ
    all-inadmissible : ℕ
    all-excluded-by-cbf : ℕ
    all-excluded-by-dec : ℕ
    untagged-constant : ℕ
    no-strict-improvement : ℕ

empty-closed-loop-residue-counts : closed-loop-residue-counts
empty-closed-loop-residue-counts = record
  { no-candidates = zero
  ; all-inadmissible = zero
  ; all-excluded-by-cbf = zero
  ; all-excluded-by-dec = zero
  ; untagged-constant = zero
  ; no-strict-improvement = zero
  }

closed-loop-residue-count-of :
  closed-loop-residue-counts → closed-loop-residue → ℕ
closed-loop-residue-count-of c clr-no-candidates =
  closed-loop-residue-counts.no-candidates c
closed-loop-residue-count-of c clr-all-inadmissible =
  closed-loop-residue-counts.all-inadmissible c
closed-loop-residue-count-of c clr-all-excluded-by-cbf =
  closed-loop-residue-counts.all-excluded-by-cbf c
closed-loop-residue-count-of c clr-all-excluded-by-dec =
  closed-loop-residue-counts.all-excluded-by-dec c
closed-loop-residue-count-of c clr-untagged-constant =
  closed-loop-residue-counts.untagged-constant c
closed-loop-residue-count-of c clr-no-strict-improvement =
  closed-loop-residue-counts.no-strict-improvement c

closed-loop-residue-counts-total : closed-loop-residue-counts → ℕ
closed-loop-residue-counts-total c =
  closed-loop-residue-counts.no-candidates c
  ℕ.+ closed-loop-residue-counts.all-inadmissible c
  ℕ.+ closed-loop-residue-counts.all-excluded-by-cbf c
  ℕ.+ closed-loop-residue-counts.all-excluded-by-dec c
  ℕ.+ closed-loop-residue-counts.untagged-constant c
  ℕ.+ closed-loop-residue-counts.no-strict-improvement c

increment-closed-loop-residue-count :
  closed-loop-residue-counts → closed-loop-residue → closed-loop-residue-counts
increment-closed-loop-residue-count c clr-no-candidates = record
  { no-candidates = suc (closed-loop-residue-counts.no-candidates c)
  ; all-inadmissible = closed-loop-residue-counts.all-inadmissible c
  ; all-excluded-by-cbf = closed-loop-residue-counts.all-excluded-by-cbf c
  ; all-excluded-by-dec = closed-loop-residue-counts.all-excluded-by-dec c
  ; untagged-constant = closed-loop-residue-counts.untagged-constant c
  ; no-strict-improvement = closed-loop-residue-counts.no-strict-improvement c
  }
increment-closed-loop-residue-count c clr-all-inadmissible = record
  { no-candidates = closed-loop-residue-counts.no-candidates c
  ; all-inadmissible = suc (closed-loop-residue-counts.all-inadmissible c)
  ; all-excluded-by-cbf = closed-loop-residue-counts.all-excluded-by-cbf c
  ; all-excluded-by-dec = closed-loop-residue-counts.all-excluded-by-dec c
  ; untagged-constant = closed-loop-residue-counts.untagged-constant c
  ; no-strict-improvement = closed-loop-residue-counts.no-strict-improvement c
  }
increment-closed-loop-residue-count c clr-all-excluded-by-cbf = record
  { no-candidates = closed-loop-residue-counts.no-candidates c
  ; all-inadmissible = closed-loop-residue-counts.all-inadmissible c
  ; all-excluded-by-cbf = suc (closed-loop-residue-counts.all-excluded-by-cbf c)
  ; all-excluded-by-dec = closed-loop-residue-counts.all-excluded-by-dec c
  ; untagged-constant = closed-loop-residue-counts.untagged-constant c
  ; no-strict-improvement = closed-loop-residue-counts.no-strict-improvement c
  }
increment-closed-loop-residue-count c clr-all-excluded-by-dec = record
  { no-candidates = closed-loop-residue-counts.no-candidates c
  ; all-inadmissible = closed-loop-residue-counts.all-inadmissible c
  ; all-excluded-by-cbf = closed-loop-residue-counts.all-excluded-by-cbf c
  ; all-excluded-by-dec = suc (closed-loop-residue-counts.all-excluded-by-dec c)
  ; untagged-constant = closed-loop-residue-counts.untagged-constant c
  ; no-strict-improvement = closed-loop-residue-counts.no-strict-improvement c
  }
increment-closed-loop-residue-count c clr-untagged-constant = record
  { no-candidates = closed-loop-residue-counts.no-candidates c
  ; all-inadmissible = closed-loop-residue-counts.all-inadmissible c
  ; all-excluded-by-cbf = closed-loop-residue-counts.all-excluded-by-cbf c
  ; all-excluded-by-dec = closed-loop-residue-counts.all-excluded-by-dec c
  ; untagged-constant = suc (closed-loop-residue-counts.untagged-constant c)
  ; no-strict-improvement = closed-loop-residue-counts.no-strict-improvement c
  }
increment-closed-loop-residue-count c clr-no-strict-improvement = record
  { no-candidates = closed-loop-residue-counts.no-candidates c
  ; all-inadmissible = closed-loop-residue-counts.all-inadmissible c
  ; all-excluded-by-cbf = closed-loop-residue-counts.all-excluded-by-cbf c
  ; all-excluded-by-dec = closed-loop-residue-counts.all-excluded-by-dec c
  ; untagged-constant = closed-loop-residue-counts.untagged-constant c
  ; no-strict-improvement = suc (closed-loop-residue-counts.no-strict-improvement c)
  }

map-excitement-residue : excitement-residue → closed-loop-residue
map-excitement-residue exc-no-candidates = clr-no-candidates
map-excitement-residue exc-all-inadmissible = clr-all-inadmissible
map-excitement-residue exc-all-excluded-by-cbf = clr-all-excluded-by-cbf
map-excitement-residue exc-all-excluded-by-dec = clr-all-excluded-by-dec
map-excitement-residue exc-untagged-constant = clr-untagged-constant
map-excitement-residue exc-no-strict-improvement = clr-no-strict-improvement

record closed-loop-observed-delta-f : Set where
  field
    src observed : ℚ

closed-loop-observed-delta-f-delta : closed-loop-observed-delta-f → ℚ
closed-loop-observed-delta-f-delta d =
  closed-loop-observed-delta-f.observed d ℚ.- closed-loop-observed-delta-f.src d

closed-loop-observed-delta-f-compute : (src observed : ℚ) → ℚ
closed-loop-observed-delta-f-compute src observed = observed ℚ.- src

closed-loop-observed-delta-f-delta-eq-compute :
  ∀ (d : closed-loop-observed-delta-f) →
  closed-loop-observed-delta-f-delta d ≡
  closed-loop-observed-delta-f-compute
    (closed-loop-observed-delta-f.src d)
    (closed-loop-observed-delta-f.observed d)
closed-loop-observed-delta-f-delta-eq-compute d = refl

record messy-witness : Set where
  field
    counts : closed-loop-residue-counts
    observed-delta-f : List closed-loop-observed-delta-f

empty-messy-witness : messy-witness
empty-messy-witness = record
  { counts = empty-closed-loop-residue-counts
  ; observed-delta-f = List.[]
  }

add-messy-observed-delta :
  messy-witness → closed-loop-observed-delta-f → messy-witness
add-messy-observed-delta w d = record
  { counts = messy-witness.counts w
  ; observed-delta-f = d List.∷ messy-witness.observed-delta-f w
  }

record-messy-residue : messy-witness → closed-loop-residue → messy-witness
record-messy-residue w r = record
  { counts = increment-closed-loop-residue-count (messy-witness.counts w) r
  ; observed-delta-f = messy-witness.observed-delta-f w
  }

record-messy-admit-residue : messy-witness → excitement-residue → messy-witness
record-messy-admit-residue w r =
  record-messy-residue w (map-excitement-residue r)

record excitement-occupancy-feedback : Set where
  field
    residue-total : ℕ
    delta-f-steps : ℕ
    occupancy-surrogate : ℕ

occupancy-from-witness : messy-witness → excitement-occupancy-feedback
occupancy-from-witness w = record
  { residue-total = closed-loop-residue-counts-total (messy-witness.counts w)
  ; delta-f-steps = length (messy-witness.observed-delta-f w)
  ; occupancy-surrogate =
      closed-loop-residue-counts-total (messy-witness.counts w) ℕ.* 1000
      ℕ.+ length (messy-witness.observed-delta-f w)
  }

------------------------------------------------------------------------
-- SECTION 2: §22.7 typed refusal + positive refuse
------------------------------------------------------------------------

data closed-loop-refusal : Set where
  excitement-residue-refusal : excitement-residue → closed-loop-refusal
  second-argmin : closed-loop-refusal
  f64-delta-f : closed-loop-refusal
  open-loop-isolation : closed-loop-refusal

data closed-loop-step-verdict : Set where
  clsv-accepted : excitement-occupancy-feedback → closed-loop-step-verdict
  clsv-refused : closed-loop-refusal → closed-loop-step-verdict

refuse-closed-loop-second-argmin : closed-loop-refusal
refuse-closed-loop-second-argmin = second-argmin

refuse-closed-loop-f64-delta-f : closed-loop-refusal
refuse-closed-loop-f64-delta-f = f64-delta-f

refuse-closed-loop-open-loop-isolation : closed-loop-refusal
refuse-closed-loop-open-loop-isolation = open-loop-isolation

------------------------------------------------------------------------
-- SECTION 3: Closed loop composes excitement-select (no argmin)
------------------------------------------------------------------------

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

closed-loop-excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
closed-loop-excitement-select = excitement-select

urge-recovery-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select = excitement-select

record closed-loop-ctx (src : ThermodynamicState) : Set where
  field
    closed-loop-successors : List (history-candidate src)

closed-loop-select :
  (src : ThermodynamicState) (ctx : closed-loop-ctx src) →
  history-candidate src ⊎ excitement-residue
closed-loop-select src ctx =
  urge-recovery-select src (closed-loop-ctx.closed-loop-successors ctx)

closed-loop-select-list :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
closed-loop-select-list src successors = urge-recovery-select src successors

closed-loop-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : closed-loop-ctx src) →
  closed-loop-select src ctx ≡
  excitement-select src (closed-loop-ctx.closed-loop-successors ctx)
closed-loop-select-eq-excitement-select src ctx = refl

closed-loop-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : closed-loop-ctx src) →
  closed-loop-select src ctx ≡
  urge-recovery-select src (closed-loop-ctx.closed-loop-successors ctx)
closed-loop-select-eq-urge-recovery-select src ctx = refl

closed-loop-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : closed-loop-ctx src) →
  closed-loop-select src ctx ≡
  excitement-select src (closed-loop-ctx.closed-loop-successors ctx)
closed-loop-no-local-argmin src ctx =
  closed-loop-select-eq-excitement-select src ctx

closed-loop-empty :
  ∀ (src : ThermodynamicState) (ctx : closed-loop-ctx src) →
  closed-loop-ctx.closed-loop-successors ctx ≡ List.[] →
  closed-loop-select src ctx ≡ inj₂ exc-no-candidates
closed-loop-empty src ctx refl = refl

strict-improvement :
  (src : ThermodynamicState) (c : history-candidate src) → Bool
strict-improvement src c =
  let tgt = ThermodynamicState.free-energy (history-candidate.cand-tgt c)
      srcF = ThermodynamicState.free-energy src
  in does (tgt ℚ.<? srcF)

strict-improvement-successors :
  (src : ThermodynamicState) → List (history-candidate src) →
  List (history-candidate src)
strict-improvement-successors src List.[] = List.[]
strict-improvement-successors src (h List.∷ t) with strict-improvement src h
... | true = h List.∷ strict-improvement-successors src t
... | false = strict-improvement-successors src t

witness-closed-loop-step-empty :
  (w : messy-witness) (src : ThermodynamicState) →
  messy-witness × closed-loop-step-verdict
witness-closed-loop-step-empty w src with closed-loop-select-list src List.[]
... | inj₁ _ = w , clsv-refused (excitement-residue-refusal exc-no-candidates)
... | inj₂ r = record-messy-admit-residue w r ,
             clsv-refused (excitement-residue-refusal r)

witness-closed-loop-step-improving :
  (w : messy-witness) (src : ThermodynamicState) →
  List (history-candidate src) →
  messy-witness × closed-loop-step-verdict
witness-closed-loop-step-improving w src List.[] =
  record-messy-admit-residue w exc-no-strict-improvement ,
  clsv-refused (excitement-residue-refusal exc-no-strict-improvement)
witness-closed-loop-step-improving w src (c List.∷ _) =
  let delta = record
        { src = ThermodynamicState.free-energy src
        ; observed = ThermodynamicState.free-energy (history-candidate.cand-tgt c)
        }
      w' = add-messy-observed-delta w delta
  in w' , clsv-accepted (occupancy-from-witness w')

witness-closed-loop-step :
  (w : messy-witness) (src : ThermodynamicState) →
  List (history-candidate src) →
  messy-witness × closed-loop-step-verdict
witness-closed-loop-step w src List.[] = witness-closed-loop-step-empty w src
witness-closed-loop-step w src (h List.∷ t) =
  witness-closed-loop-step-improving w src (strict-improvement-successors src (h List.∷ t))

------------------------------------------------------------------------
-- SECTION 4: §22.7 fixtures + witness theorems
------------------------------------------------------------------------

q10 : ℚ
q10 = mkℚ (+ 10) 0 (Cop.sym (Cop.1-coprimeTo ∣ + 10 ∣))

q3 : ℚ
q3 = mkℚ (+ 3) 0 (Cop.sym (Cop.1-coprimeTo ∣ + 3 ∣))

q2 : ℚ
q2 = mkℚ (+ 2) 0 (Cop.sym (Cop.1-coprimeTo ∣ + 2 ∣))

closed-loop-fixture-accept-src : ThermodynamicState
closed-loop-fixture-accept-src = record
  { density = 0ℚ
  ; free-energy = q10
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

closed-loop-fixture-accept-tgt : ThermodynamicState
closed-loop-fixture-accept-tgt = record
  { density = 0ℚ
  ; free-energy = q3
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

closed-loop-fixture-accept-admissible :
  Admissible closed-loop-fixture-accept-src closed-loop-fixture-accept-tgt
closed-loop-fixture-accept-admissible = admissible-any

closed-loop-fixture-accept-candidate :
  history-candidate closed-loop-fixture-accept-src
closed-loop-fixture-accept-candidate = record
  { cand-id = 1
  ; cand-tgt = closed-loop-fixture-accept-tgt
  ; cand-admissible = closed-loop-fixture-accept-admissible
  }

closed-loop-fixture-refuse-src : ThermodynamicState
closed-loop-fixture-refuse-src = record
  { density = 0ℚ
  ; free-energy = q2
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

closed-loop-fixture-refuse-tgt : ThermodynamicState
closed-loop-fixture-refuse-tgt = closed-loop-fixture-refuse-src

closed-loop-fixture-refuse-admissible :
  Admissible closed-loop-fixture-refuse-src closed-loop-fixture-refuse-tgt
closed-loop-fixture-refuse-admissible = admissible-refl closed-loop-fixture-refuse-src

closed-loop-fixture-refuse-candidate :
  history-candidate closed-loop-fixture-refuse-src
closed-loop-fixture-refuse-candidate = record
  { cand-id = 0
  ; cand-tgt = closed-loop-fixture-refuse-tgt
  ; cand-admissible = closed-loop-fixture-refuse-admissible
  }

closed-loop-fixture-accept-step :
  messy-witness × closed-loop-step-verdict
closed-loop-fixture-accept-step =
  witness-closed-loop-step empty-messy-witness closed-loop-fixture-accept-src
    (closed-loop-fixture-accept-candidate List.∷ List.[])

closed-loop-fixture-accept-w : messy-witness
closed-loop-fixture-accept-w = proj₁ closed-loop-fixture-accept-step

closed-loop-fixture-accept-v : closed-loop-step-verdict
closed-loop-fixture-accept-v = proj₂ closed-loop-fixture-accept-step

closed-loop-fixture-accept-feedback : excitement-occupancy-feedback
closed-loop-fixture-accept-feedback =
  occupancy-from-witness closed-loop-fixture-accept-w

closed-loop-fixture-accept-records-delta :
  excitement-occupancy-feedback.delta-f-steps closed-loop-fixture-accept-feedback ≡ 1 ×
  excitement-occupancy-feedback.residue-total closed-loop-fixture-accept-feedback ≡ 0 ×
  length (messy-witness.observed-delta-f closed-loop-fixture-accept-w) ≡ 1
closed-loop-fixture-accept-records-delta = refl , refl , refl

closed-loop-fixture-refuse-no-candidates-step :
  messy-witness × closed-loop-step-verdict
closed-loop-fixture-refuse-no-candidates-step =
  witness-closed-loop-step empty-messy-witness closed-loop-fixture-accept-src List.[]

closed-loop-fixture-refuse-no-candidates-w : messy-witness
closed-loop-fixture-refuse-no-candidates-w = proj₁ closed-loop-fixture-refuse-no-candidates-step

closed-loop-fixture-refuse-no-candidates-v : closed-loop-step-verdict
closed-loop-fixture-refuse-no-candidates-v = proj₂ closed-loop-fixture-refuse-no-candidates-step

closed-loop-fixture-refuse-no-candidates :
  closed-loop-fixture-refuse-no-candidates-v ≡
    clsv-refused (excitement-residue-refusal exc-no-candidates) ×
  closed-loop-residue-count-of
    (messy-witness.counts closed-loop-fixture-refuse-no-candidates-w)
    clr-no-candidates ≡ 1
closed-loop-fixture-refuse-no-candidates = refl , refl

closed-loop-fixture-refuse-no-strict-improvement-step :
  messy-witness × closed-loop-step-verdict
closed-loop-fixture-refuse-no-strict-improvement-step =
  witness-closed-loop-step empty-messy-witness closed-loop-fixture-refuse-src
    (closed-loop-fixture-refuse-candidate List.∷ List.[])

closed-loop-fixture-refuse-no-strict-improvement-w : messy-witness
closed-loop-fixture-refuse-no-strict-improvement-w =
  proj₁ closed-loop-fixture-refuse-no-strict-improvement-step

closed-loop-fixture-refuse-no-strict-improvement-v : closed-loop-step-verdict
closed-loop-fixture-refuse-no-strict-improvement-v =
  proj₂ closed-loop-fixture-refuse-no-strict-improvement-step

closed-loop-fixture-refuse-no-strict-improvement :
  closed-loop-fixture-refuse-no-strict-improvement-v ≡
    clsv-refused (excitement-residue-refusal exc-no-strict-improvement) ×
  closed-loop-residue-count-of
    (messy-witness.counts closed-loop-fixture-refuse-no-strict-improvement-w)
    clr-no-strict-improvement ≡ 1
closed-loop-fixture-refuse-no-strict-improvement = refl , refl

closed-loop-occupancy-surrogate-fixture-w : messy-witness
closed-loop-occupancy-surrogate-fixture-w =
  record-messy-admit-residue
    (record-messy-admit-residue empty-messy-witness exc-no-candidates)
    exc-no-strict-improvement

closed-loop-occupancy-surrogate-fixture-w' : messy-witness
closed-loop-occupancy-surrogate-fixture-w' =
  add-messy-observed-delta closed-loop-occupancy-surrogate-fixture-w
    (record { src = q10 ; observed = q3 })

closed-loop-occupancy-surrogate-fixture :
  excitement-occupancy-feedback.occupancy-surrogate
    (occupancy-from-witness closed-loop-occupancy-surrogate-fixture-w') ≡ 2001
closed-loop-occupancy-surrogate-fixture = refl

closed-loop-refuse-second-argmin-positive :
  refuse-closed-loop-second-argmin ≡ second-argmin
closed-loop-refuse-second-argmin-positive = refl

closed-loop-refuse-f64-delta-f-positive :
  refuse-closed-loop-f64-delta-f ≡ f64-delta-f
closed-loop-refuse-f64-delta-f-positive = refl

closed-loop-refuse-open-loop-isolation-positive :
  refuse-closed-loop-open-loop-isolation ≡ open-loop-isolation
closed-loop-refuse-open-loop-isolation-positive = refl

closed-loop-observed-delta-f-compute-fixture :
  closed-loop-observed-delta-f-compute q10 q3 ≡ q3 ℚ.- q10
closed-loop-observed-delta-f-compute-fixture = refl

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

------------------------------------------------------------------------
-- SECTION 5: Typed history + Landauer bridge (zero new postulates)
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
      step1 = subst (λ d → d ≤ ErasureProcess.dissipatedEntropy proc) (≡.sym hent) hSL
  in subst (λ d → HistoryTransition.entropy-drop t ≤ d) (≡.sym hdiss) step1

closed-loop-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
closed-loop-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 6: Excitement compose pin (no second ℚ argmin)
------------------------------------------------------------------------

urge-closed-loop-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-closed-loop-select = closed-loop-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin : closed-loop-refusal
refuse-second-argmin = second-argmin

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

closed-loop-witness-physics-green : Bool
closed-loop-witness-physics-green = false

closed-loop-witness-physics-green-false :
  closed-loop-witness-physics-green ≡ false
closed-loop-witness-physics-green-false = refl

closed-loop-witness-production-wired : Bool
closed-loop-witness-production-wired = false

closed-loop-witness-production-wired-false :
  closed-loop-witness-production-wired ≡ false
closed-loop-witness-production-wired-false = refl

closed-loop-witness-module-witness : ⊤
closed-loop-witness-module-witness = tt

closed-loop-witness-no-new-axiom : ⊤
closed-loop-witness-no-new-axiom = tt

closed-loop-witness-marker : ℕ
closed-loop-witness-marker = 1

closed-loop-witness-marker-eq : closed-loop-witness-marker ≡ 1
closed-loop-witness-marker-eq = refl

closed-loop-positive-refuse-not-silent :
  refuse-closed-loop-second-argmin ≢ f64-delta-f
closed-loop-positive-refuse-not-silent ()
