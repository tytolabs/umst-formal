-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/CompactionComposite.lean

  Meso acting Urge — §17.5 compaction as composite Excitement arrow.
  Semantic squash is refused unless recorded as an admitted composite arrow whose
  `wasDerivedFrom` witness retains the chain — the composite *is* the residue.
  Compaction **pays MI** (Landauer lift); it is **not** delete-old-commits theater.

  Urge compaction composes `Excitement.select` — not a second argmin.
  Anchored in `AdmitKleisli` / `ProvenancePreserve`.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import Urge.AdmitKleisli
import Urge.ProvenancePreserve

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.ProvenancePreserve

namespace UMST.Urge.CompactionComposite

-- ================================================================
-- SECTION 1: Derivation chain + MI payment witnesses (§17.5)
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

theorem miPaid_intro (m : MiPaymentWitness) (hp : 0 < m.miPaidBits)
    (hr : m.miRequiredBits ≤ m.miPaidBits) : miPaid m :=
  ⟨hp, hr⟩

/-- Admitted composite compaction arrow — composite *is* the residue (§17.5). -/
structure CompositeCompactionArrow where
  compositeId : Nat
  compositeWitness : DerivationChainWitness
  compositeSourceCommit : Nat

-- ================================================================
-- SECTION 2: Compaction class + typed refuse (positive, not bool theater)
-- ================================================================

inductive CompactionClass where
  | gitGcSubstrate
  | compositeExcitementArrow
  deriving DecidableEq, Repr

inductive CompactionCompositeRefusal where
  | gitGcTheater
  | deleteOldCommitsTheater
  | semanticSquashWithoutComposite
  | secondArgmin
  | miUnpaid
  deriving DecidableEq, Repr

def refuseMiUnpaid : CompactionCompositeRefusal :=
  .miUnpaid

def refuseSecondArgmin : CompactionCompositeRefusal :=
  .secondArgmin

def refuseSemanticSquashWithoutComposite : CompactionCompositeRefusal :=
  .semanticSquashWithoutComposite

/-- One compaction attempt before gating (§17.5 fixture surface). -/
structure CompactionAttempt where
  attemptDeleteOldCommits : Bool
  attemptMi : MiPaymentWitness
  attemptWitness : Option DerivationChainWitness
  attemptProvenanceIntact : Bool

/-- Build composite arrow from a non-empty derivation chain. -/
def compositeArrowFromChain (cid : Nat) (chain : List Nat) (sourceCommit : Nat) :
    Option CompositeCompactionArrow :=
  match chain with
  | [] => none
  | _ :: _ =>
      some { compositeId := cid
             compositeWitness := { derivationChain := chain }
             compositeSourceCommit := sourceCommit }

/-- Classify compaction attempt without performing mutation. -/
def classifyCompaction (isGitGcSubstrateOnly : Bool) (isSemanticSquash : Bool)
    (witness : Option DerivationChainWitness) :
    CompactionClass ⊕ CompactionCompositeRefusal :=
  if isSemanticSquash then
    match witness with
    | some w =>
        if retainsChainBool w then
          Sum.inl .compositeExcitementArrow
        else
          Sum.inr .semanticSquashWithoutComposite
    | none => Sum.inr .semanticSquashWithoutComposite
  else if isGitGcSubstrateOnly then
    Sum.inl .gitGcSubstrate
  else
    match witness with
    | some w =>
        if retainsChainBool w then
          Sum.inl .compositeExcitementArrow
        else
          Sum.inr .gitGcTheater
    | none => Sum.inr .gitGcTheater

/-- Gate a compaction attempt — composite arrow paying MI, not delete-old-commits. -/
def evaluateCompactionAttempt (a : CompactionAttempt) :
    Bool ⊕ CompactionCompositeRefusal :=
  if a.attemptDeleteOldCommits then
    Sum.inr .deleteOldCommitsTheater
  else if !miPaidBool a.attemptMi then
    Sum.inr .miUnpaid
  else
    match a.attemptWitness with
    | none => Sum.inr .semanticSquashWithoutComposite
    | some w =>
        if retainsChainBool w then
          if a.attemptProvenanceIntact then
            Sum.inl true
          else
            Sum.inr .semanticSquashWithoutComposite
        else
          Sum.inr .semanticSquashWithoutComposite

theorem gateCompactionMiRefuseDelete (a : CompactionAttempt)
    (h : a.attemptDeleteOldCommits = true) :
    evaluateCompactionAttempt a = Sum.inr .deleteOldCommitsTheater := by
  simp [evaluateCompactionAttempt, h]

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
-- SECTION 4: Excitement compose (no second argmin)
-- ================================================================

/-- Kleisli composite pin — compaction chains inherited arrows, not squash. -/
abbrev compactionCompose := kleisliCompose

theorem compactionComposeAssocInherited (f g h : AdmitArrow) (s : ThermodynamicState) :
    compactionCompose (compactionCompose f g) h s = compactionCompose f (compactionCompose g h) s :=
  kleisliComposeAssocAt f g h s

-- ================================================================
-- SECTION 5: Honesty flags + catalog witnesses
-- ================================================================

def compactionCompositeMarker : Nat := 175

theorem compactionCompositeMarkerPos : 0 < compactionCompositeMarker := by decide

end UMST.Urge.CompactionComposite
