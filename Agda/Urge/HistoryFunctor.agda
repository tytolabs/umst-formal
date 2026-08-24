-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.HistoryFunctor — meso/acting §5.1 Admissible History Functor.
--
-- URGE-FORMAL-MESO-AGDA-HISTORY-FUNCTOR (umst-formal acting fiber only).
-- Git-style content-addressed bytes → typed gate-checked history with
-- second-law preservation (Set — not a new postulate).
--
-- Minimal thermodynamic head carriers (no Concrete.Gate K-infect); history
-- pins mirror `Urge.AdmitKleisli`. Sole physics postulate:
-- `Chem.SecondLaw.physicalSecondLaw`.
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
-- Zero extra postulate beyond Landauer. Unwired.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.HistoryFunctor where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; not; if_then_else_; _∧_; _∨_)
open import Data.Empty using (⊥-elim)
import Data.List as List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst; sym; trans)
open import Relation.Nullary using (does; yes; no)

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

mkState : ℚ → ℚ → ℚ → ℚ → ThermodynamicState
mkState d fe h s = record { density = d ; free-energy = fe ; hydration = h ; strength = s }

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers (mirror Urge.AdmitKleisli §1)
------------------------------------------------------------------------

record HistorySnapshot : Set where
  field
    commit-id : ℕ
    head      : ThermodynamicState

record HistoryTransition : Set where
  field
    prior              : HistorySnapshot
    post               : HistorySnapshot
    bath               : HeatBath
    dissipated-entropy : ℚ
    entropy-drop       : ℚ
    gate-admissible    : Admissible (HistorySnapshot.head prior) (HistorySnapshot.head post)

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

admissibleHistoryTransition : HistoryTransition → Set
admissibleHistoryTransition t = admitSecondLaw t

------------------------------------------------------------------------
-- SECTION 2: Git-style byte carriers (pre-gate ingress)
------------------------------------------------------------------------

RawCommitBytes : Set
RawCommitBytes = List.List ℕ

record RawGitCommit : Set where
  field
    commit-hash : ℕ
    payload     : RawCommitBytes

record RepoStateSlice : Set where
  field
    provenance-intact   : Bool
    physics-green-claim : Bool
    witness-present     : Bool

record RepoTransitionStep : Set where
  field
    before           : RepoStateSlice
    after            : RepoStateSlice
    provenance-stamp : Maybe String
    drops-provenance : Bool
    invents-green    : Bool

data TransitionVerdict : Set where
  Accept : TransitionVerdict
  Reject : TransitionVerdict

record TypedHistory : Set where
  field
    snapshot          : HistorySnapshot
    provenance-intact : Bool

record AdmissibleHistoryFunctor : Set where
  field
    decode : RawGitCommit → Maybe TypedHistory
    preserveCommitId :
      ∀ c h → decode c ≡ just h →
      RawGitCommit.commit-hash c ≡ HistorySnapshot.commit-id (TypedHistory.snapshot h)

history-functor-identity : String
history-functor-identity = "history_functor"

------------------------------------------------------------------------
-- SECTION 3: Second-law preservation
------------------------------------------------------------------------

preservationProp : HistoryTransition → Set
preservationProp t =
  admitSecondLaw t × Admissible (HistorySnapshot.head (HistoryTransition.prior t))
                  (HistorySnapshot.head (HistoryTransition.post t))

preservationProp-of-admissible :
  (t : HistoryTransition) → admissibleHistoryTransition t → preservationProp t
preservationProp-of-admissible t h = h , HistoryTransition.gate-admissible t

------------------------------------------------------------------------
-- SECTION 4: Provenance gate (mirrors umst-meta evaluate_transition)
------------------------------------------------------------------------

stamp-non-empty : String → Bool
stamp-non-empty "" = false
stamp-non-empty _  = true

evaluateTransition-stamp : Maybe String → RepoStateSlice → TransitionVerdict
evaluateTransition-stamp nothing _ = Reject
evaluateTransition-stamp (just stamp) after =
  if stamp-non-empty stamp
  then if (RepoStateSlice.provenance-intact after ∧
           not (RepoStateSlice.physics-green-claim after))
       then Accept
       else Reject
  else Reject

evaluateTransition : RepoTransitionStep → TransitionVerdict
evaluateTransition step =
  if RepoTransitionStep.invents-green step
  then Reject
  else if (RepoStateSlice.physics-green-claim (RepoTransitionStep.after step) ∧
            not (RepoStateSlice.witness-present (RepoTransitionStep.after step)))
       then Reject
       else if (RepoTransitionStep.drops-provenance step ∨
                (RepoStateSlice.provenance-intact (RepoTransitionStep.before step) ∧
                 not (RepoStateSlice.provenance-intact (RepoTransitionStep.after step))))
            then Reject
            else evaluateTransition-stamp (RepoTransitionStep.provenance-stamp step)
                 (RepoTransitionStep.after step)

provenanced-ok-step : RepoTransitionStep
provenanced-ok-step = record
  { before = record { provenance-intact = true ; physics-green-claim = false ; witness-present = false }
  ; after  = record { provenance-intact = true ; physics-green-claim = false ; witness-present = false }
  ; provenance-stamp = just "ucrs:t"
  ; drops-provenance = false
  ; invents-green = false
  }

evaluateTransition-rejects-invents-green :
  (step : RepoTransitionStep) → RepoTransitionStep.invents-green step ≡ true →
  evaluateTransition step ≡ Reject
evaluateTransition-rejects-invents-green step refl = refl

evaluateTransition-rejects-physics-green-without-witness :
  (step : RepoTransitionStep) →
  RepoStateSlice.physics-green-claim (RepoTransitionStep.after step) ≡ true →
  RepoStateSlice.witness-present (RepoTransitionStep.after step) ≡ false →
  RepoTransitionStep.invents-green step ≡ false →
  evaluateTransition step ≡ Reject
evaluateTransition-rejects-physics-green-without-witness step refl refl refl = refl

evaluateTransition-rejects-drops-provenance :
  (step : RepoTransitionStep) →
  RepoTransitionStep.drops-provenance step ≡ true →
  RepoTransitionStep.invents-green step ≡ false →
  RepoStateSlice.physics-green-claim (RepoTransitionStep.after step) ≡ false →
  evaluateTransition step ≡ Reject
evaluateTransition-rejects-drops-provenance step refl refl refl = refl

provenanced-ok-step-evaluates-accept :
  evaluateTransition provenanced-ok-step ≡ Accept
provenanced-ok-step-evaluates-accept = refl

------------------------------------------------------------------------
-- SECTION 5: Catalog decode (fixture — git bytes → typed history)
------------------------------------------------------------------------

fixture-state : ThermodynamicState
fixture-state = mkState 0ℚ 0ℚ 0ℚ 0ℚ

fixture-commit-hash : ℕ
fixture-commit-hash = 42

fixture-payload : RawCommitBytes
fixture-payload = List.[]

fixture-raw-commit : RawGitCommit
fixture-raw-commit = record { commit-hash = fixture-commit-hash ; payload = fixture-payload }

fixture-typed-history : TypedHistory
fixture-typed-history = record
  { snapshot = record { commit-id = fixture-commit-hash ; head = fixture-state }
  ; provenance-intact = true
  }

catalogDecode : RawGitCommit → Maybe TypedHistory
catalogDecode c with RawGitCommit.commit-hash c ≟ fixture-commit-hash
... | yes _ = just fixture-typed-history
... | no  _ = nothing

catalogDecode-fixture :
  catalogDecode fixture-raw-commit ≡ just fixture-typed-history
catalogDecode-fixture = refl

nothing-not-just : {A : Set} {x : A} → nothing {A = A} ≢ just x
nothing-not-just ()

catalogDecode-preserveCommitId :
  (c : RawGitCommit) (h : TypedHistory) →
  catalogDecode c ≡ just h →
  RawGitCommit.commit-hash c ≡ HistorySnapshot.commit-id (TypedHistory.snapshot h)
catalogDecode-preserveCommitId c h eq with RawGitCommit.commit-hash c ≟ fixture-commit-hash
... | yes p = trans p (sym (cong HistorySnapshot.commit-id (cong TypedHistory.snapshot (sym (just-injective eq)))))
... | no  _ = ⊥-elim (nothing-not-just eq)

catalogHistoryFunctor : AdmissibleHistoryFunctor
catalogHistoryFunctor = record
  { decode = catalogDecode
  ; preserveCommitId = catalogDecode-preserveCommitId
  }

catalog-decode-fixture :
  AdmissibleHistoryFunctor.decode catalogHistoryFunctor fixture-raw-commit ≡ just fixture-typed-history
catalog-decode-fixture = catalogDecode-fixture

------------------------------------------------------------------------
-- SECTION 6: Bridge to Landauer (zero new postulates)
------------------------------------------------------------------------

admitSecondLaw-from-landauer :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
  PhysicalSecondLaw proc entropyDecrease →
  ∀ (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
admitSecondLaw-from-landauer proc ΔS hSL t hent hdiss =
  subst (λ d → HistoryTransition.entropy-drop t ≤ d) (sym hdiss)
    (subst (λ d → d ≤ ErasureProcess.dissipatedEntropy proc) (sym hent) hSL)

preservationProp-from-landauer :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
  PhysicalSecondLaw proc entropyDecrease →
  ∀ (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  preservationProp t
preservationProp-from-landauer proc ΔS hSL t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS hSL t hent hdiss ,
  HistoryTransition.gate-admissible t

admissible-preserves-second-law :
  (t : HistoryTransition) → admissibleHistoryTransition t → admitSecondLaw t
admissible-preserves-second-law t h = h

historyFunctor-noNewPostulate :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  preservationProp t
historyFunctor-noNewPostulate proc ΔS t hent hdiss =
  preservationProp-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

historyFunctor-from-landauer :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  preservationProp t
historyFunctor-from-landauer proc ΔS t hent hdiss =
  historyFunctor-noNewPostulate proc ΔS t hent hdiss

physicalSecondLaw-discharge :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
physicalSecondLaw-discharge proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

history-functor-production-wired : Bool
history-functor-production-wired = false

history-functor-production-wired-false :
  history-functor-production-wired ≡ false
history-functor-production-wired-false = refl

history-functor-module-witness : ⊤
history-functor-module-witness = tt
