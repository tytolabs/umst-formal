-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/CompactionAsArrow.lean

  Meso acting Urge — §17.5 sophisticated compaction as composite arrow paying MI.
  Semantic squash is refused unless recorded as an admitted composite arrow whose
  `wasDerivedFrom` witness retains the chain — the composite *is* the residue.
  Compaction **pays MI** (Landauer lift); it is **not** delete-old-commits theater.

  Urge compaction composes `Excitement.select` — not a second argmin.
  Anchored in `AdmitKleisli` / `ExcitementImport` / `ProvenancePreserve`.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.AdmitKleisli
import Urge.ProvenancePreserve

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.ProvenancePreserve

namespace UMST.Urge.CompactionAsArrow

-- ================================================================
-- SECTION 1: Derivation chain + MI payment + composite arrow (§17.5)
-- ================================================================

/-- Provenance derivation chain retained on composite compaction arrows. -/
structure DerivationChainWitness where
  derivationChain : List Nat

/-- Whether the witness retains a non-empty derivation chain. -/
def retainsChain (w : DerivationChainWitness) : Prop :=
  w.derivationChain ≠ []

def retainsChainBool (w : DerivationChainWitness) : Bool :=
  match w.derivationChain with
  | [] => false
  | _ :: _ => true

theorem retainsChainBool_true_iff (w : DerivationChainWitness) :
    retainsChainBool w = true ↔ retainsChain w := by
  rcases w with ⟨chain⟩
  cases chain with
  | nil => simp [retainsChainBool, retainsChain]
  | cons h t => simp [retainsChainBool, retainsChain]

/-- MI payment witness — compaction must pay mutual-information cost. -/
structure MiPaymentWitness where
  miRequiredBits : Nat
  miPaidBits : Nat

/-- Whether MI cost was paid (strictly positive paid bits ≥ required). -/
def miPaid (m : MiPaymentWitness) : Prop :=
  0 < m.miPaidBits ∧ m.miRequiredBits ≤ m.miPaidBits

def miPaidBool (m : MiPaymentWitness) : Bool :=
  m.miPaidBits > 0 && m.miRequiredBits ≤ m.miPaidBits

theorem miPaidBool_true_iff (m : MiPaymentWitness) :
    miPaidBool m = true ↔ miPaid m := by
  rcases m with ⟨req, paid⟩
  unfold miPaidBool miPaid
  cases paid <;> simp

/-- Admitted composite compaction arrow — composite *is* the residue (§17.5). -/
structure CompactionArrow where
  compositeId : Nat
  compositeWitness : DerivationChainWitness
  compositeSourceCommit : Nat
  compositeExcitementSelected : Bool

-- ================================================================
-- SECTION 2: Typed refuse + gate (positive, not bool theater)
-- ================================================================

inductive CompactionVerdict where
  | accept
  | reject
  deriving DecidableEq, Repr

inductive CompactionAsArrowRefuse where
  | deleteOldCommitsTheater
  | miUnpaid
  | secondArgmin
  | missingDerivationWitness
  deriving DecidableEq, Repr

def refuseMiUnpaid : CompactionAsArrowRefuse :=
  .miUnpaid

def refuseSecondArgmin : CompactionAsArrowRefuse :=
  .secondArgmin

def refuseMissingDerivationWitness : CompactionAsArrowRefuse :=
  .missingDerivationWitness

/-- One compaction attempt before gating (§17.5 fixture surface). -/
structure CompactionAttempt where
  attemptDeleteOldCommits : Bool
  attemptMi : MiPaymentWitness
  attemptWitness : Option DerivationChainWitness
  attemptProvenanceIntact : Bool
  attemptExcitementSelected : Bool

/-- Build composite arrow from a non-empty derivation chain. -/
def compactionArrowFromChain (cid : Nat) (chain : List Nat) (sourceCommit : Nat)
    (excitementSelected : Bool) : CompactionArrow ⊕ CompactionAsArrowRefuse :=
  match chain with
  | [] => Sum.inr .missingDerivationWitness
  | _ :: _ =>
      Sum.inl
        { compositeId := cid
          compositeWitness := { derivationChain := chain }
          compositeSourceCommit := sourceCommit
          compositeExcitementSelected := excitementSelected }

/-- Gate a compaction attempt — composite arrow paying MI, not delete-old-commits. -/
def evaluateCompactionAttempt (a : CompactionAttempt) : CompactionVerdict :=
  if a.attemptDeleteOldCommits then
    .reject
  else if !miPaidBool a.attemptMi then
    .reject
  else
    match a.attemptWitness with
    | none => .reject
    | some w =>
        if retainsChainBool w then
          if a.attemptProvenanceIntact then
            if a.attemptExcitementSelected then .accept else .reject
          else .reject
        else .reject

/-- Evaluate attempt with typed refuse on reject path. -/
def evaluateCompactionAttemptRefuse (a : CompactionAttempt) :
    CompactionVerdict ⊕ CompactionAsArrowRefuse :=
  if a.attemptDeleteOldCommits then
    Sum.inr .deleteOldCommitsTheater
  else if !miPaidBool a.attemptMi then
    Sum.inr .miUnpaid
  else
    match a.attemptWitness with
    | none => Sum.inr .missingDerivationWitness
    | some w =>
        if retainsChainBool w then
          if a.attemptProvenanceIntact then
            if a.attemptExcitementSelected then Sum.inl .accept
            else Sum.inr .missingDerivationWitness
          else Sum.inr .missingDerivationWitness
        else Sum.inr .missingDerivationWitness

theorem evaluateCompactionAttemptRefuse_agrees (a : CompactionAttempt) :
    match evaluateCompactionAttemptRefuse a with
    | Sum.inl .accept => evaluateCompactionAttempt a = .accept
    | Sum.inl .reject => evaluateCompactionAttempt a = .reject
    | Sum.inr _ => evaluateCompactionAttempt a = .reject := by
  rcases a with ⟨del, mi, wit, prov, exc⟩
  simp only [evaluateCompactionAttemptRefuse, evaluateCompactionAttempt]
  by_cases hdel : del <;> simp [hdel]
  by_cases hmi : miPaidBool mi <;> simp [hmi]
  cases wit with
  | none => rfl
  | some w =>
    by_cases hchain : retainsChainBool w <;> simp [hchain]
    by_cases hprov : prov <;> simp [hprov]
    by_cases hexc : exc <;> simp [hexc]

-- ================================================================
-- SECTION 3: Landauer bridge — compaction pays MI (cited, not axiom)
-- ================================================================

/-- MI payment witness from nat MI bits (Landauer field cited, not re-derived). -/
def miPaymentFromLandauerBits (n : Nat) : MiPaymentWitness :=
  { miRequiredBits := n, miPaidBits := n }

theorem landauerBridgeMiPaidWhenNonzero (n : Nat) (h : 0 < n) :
    miPaidBool (miPaymentFromLandauerBits n) = true := by
  cases n with
  | zero => simp at h
  | succ k => simp [miPaymentFromLandauerBits, miPaidBool]

-- ================================================================
-- SECTION 4: Compaction composes Excitement.select (no second argmin)
-- ================================================================

/-- Kleisli composite pin — compaction chains inherited arrows, not squash. -/
abbrev compactionCompose := kleisliCompose

theorem compactionComposeAssocInherited (f g h : AdmitArrow) (s : ThermodynamicState) :
    compactionCompose (compactionCompose f g) h s = compactionCompose f (compactionCompose g h) s :=
  kleisliComposeAssocAt f g h s

-- ================================================================
-- SECTION 5: §17.5 fixtures + witness theorems
-- ================================================================

def fixtureMiPaid : MiPaymentWitness :=
  { miRequiredBits := 2, miPaidBits := 4 }

def fixtureWitness : DerivationChainWitness :=
  { derivationChain := [1, 2, 3] }

def fixtureAdmissible : CompactionAttempt :=
  { attemptDeleteOldCommits := false
    attemptMi := fixtureMiPaid
    attemptWitness := some fixtureWitness
    attemptProvenanceIntact := true
    attemptExcitementSelected := true }

def fixtureDeleteOldCommits : CompactionAttempt :=
  { attemptDeleteOldCommits := true
    attemptMi := fixtureMiPaid
    attemptWitness := some fixtureWitness
    attemptProvenanceIntact := true
    attemptExcitementSelected := true }

def fixtureMiUnpaid : CompactionAttempt :=
  { attemptDeleteOldCommits := false
    attemptMi := { miRequiredBits := 2, miPaidBits := 0 }
    attemptWitness := some fixtureWitness
    attemptProvenanceIntact := true
    attemptExcitementSelected := true }

theorem fixtureAdmissibleAccept :
    evaluateCompactionAttempt fixtureAdmissible = .accept := rfl

theorem fixtureDeleteOldCommitsReject :
    evaluateCompactionAttempt fixtureDeleteOldCommits = .reject := rfl

theorem fixtureMiUnpaidReject :
    evaluateCompactionAttempt fixtureMiUnpaid = .reject := rfl

theorem fixtureArrowFromChainOk :
    compactionArrowFromChain 42 [1, 2] 7 true =
      Sum.inl
        { compositeId := 42
          compositeWitness := { derivationChain := [1, 2] }
          compositeSourceCommit := 7
          compositeExcitementSelected := true } :=
  rfl

theorem fixtureArrowFromEmptyChainRefused :
    compactionArrowFromChain 1 [] 0 true = Sum.inr .missingDerivationWitness :=
  rfl

theorem positiveRefuseNotSilent :
    evaluateCompactionAttempt fixtureDeleteOldCommits ≠ .accept := by
  simp [evaluateCompactionAttempt, fixtureDeleteOldCommits]

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

theorem deleteOldCommitsRefused (a : CompactionAttempt)
    (h : a.attemptDeleteOldCommits = true) :
    evaluateCompactionAttemptRefuse a = Sum.inr .deleteOldCommitsTheater := by
  simp [evaluateCompactionAttemptRefuse, h]

end UMST.Urge.CompactionAsArrow
