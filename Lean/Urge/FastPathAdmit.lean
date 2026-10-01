-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/FastPathAdmit.lean

  Meso acting Urge — §17.8 fast-path admission as typed predicate.
  Local commit uses a typed fast predicate (≤100ms budget constant),
  analogue of R23 PreservationWitness — no whole-tree re-scan.
  Merge / recovery pays the slow path (≤1s budget) with composed
  `Excitement.select` — **not** wall-clock GREEN, not a second argmin.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.ExcitementImport

namespace UMST.Urge.FastPathAdmit

-- ================================================================
-- SECTION 1: §17.8 typed budget constants (not wall-clock GREEN)
-- ================================================================

/-- Blueprint §17.8 local commit admission budget (milliseconds, typed). -/
def localCommitBudgetMs : Nat := 100

/-- Blueprint §17.8 merge / recovery slow-path budget (milliseconds, typed). -/
def mergeRecoveryBudgetMs : Nat := 1000

-- ================================================================
-- SECTION 2: Admission path classification
-- ================================================================

inductive AdmitPath where
  | fastLocal
  | fullMergeRecovery
  deriving DecidableEq, Repr

/-- Typed budget ceiling for each path class (not measured wall-clock). -/
def admitPathBudgetMs (p : AdmitPath) : Nat :=
  match p with
  | .fastLocal => localCommitBudgetMs
  | .fullMergeRecovery => mergeRecoveryBudgetMs

theorem admitPath_fastLocal_budget :
    admitPathBudgetMs .fastLocal = localCommitBudgetMs := rfl

theorem admitPath_mergeRecovery_budget :
    admitPathBudgetMs .fullMergeRecovery = mergeRecoveryBudgetMs := rfl

-- ================================================================
-- SECTION 3: Fast-path candidate + typed predicate
-- ================================================================

/-- Candidate for fast-path admission — local predicate inputs only. -/
structure FastPathCandidate where
  fpIsLocalAppend            : Bool
  fpRequiresWholeTreeRescan  : Bool
  fpIsMergeOrRecovery        : Bool

/-- Fast-path typed predicate — local append without whole-tree re-scan or merge. -/
def fastPathAdmitPred (c : FastPathCandidate) : Bool :=
  match c.fpIsLocalAppend, c.fpRequiresWholeTreeRescan, c.fpIsMergeOrRecovery with
  | true, false, false => true
  | _, _, _ => false

inductive FastPathAdmitRefusal where
  | refuseWholeTreeRescan
  | refuseMergeRecoverySlowPath
  | refuseWallClockSlaTheater
  | refuseBudgetExceeded (estimatedMs budgetMs : Nat)

/-- Classify admission path from candidate — honest refusal on inadmissible fast path. -/
def classifyAdmitPath (c : FastPathCandidate) : AdmitPath ⊕ FastPathAdmitRefusal :=
  if c.fpRequiresWholeTreeRescan then
    Sum.inr .refuseWholeTreeRescan
  else if c.fpIsMergeOrRecovery then
    Sum.inr .refuseMergeRecoverySlowPath
  else if fastPathAdmitPred c then
    Sum.inl .fastLocal
  else
    Sum.inr (.refuseBudgetExceeded (localCommitBudgetMs + 1) localCommitBudgetMs)

theorem classifyAdmitPath_fastLocal (c : FastPathCandidate)
    (hAppend : c.fpIsLocalAppend = true)
    (hRescan : c.fpRequiresWholeTreeRescan = false)
    (hMerge : c.fpIsMergeOrRecovery = false) :
    classifyAdmitPath c = Sum.inl .fastLocal := by
  unfold classifyAdmitPath fastPathAdmitPred
  rw [hRescan, hMerge, hAppend]
  rfl

theorem classifyAdmitPath_wholeTreeRescan (c : FastPathCandidate)
    (h : c.fpRequiresWholeTreeRescan = true) :
    classifyAdmitPath c = Sum.inr .refuseWholeTreeRescan := by
  unfold classifyAdmitPath
  rw [h]
  rfl

theorem classifyAdmitPath_mergeRecovery (c : FastPathCandidate)
    (hRescan : c.fpRequiresWholeTreeRescan = false)
    (hMerge : c.fpIsMergeOrRecovery = true) :
    classifyAdmitPath c = Sum.inr .refuseMergeRecoverySlowPath := by
  unfold classifyAdmitPath
  rw [hRescan, hMerge]
  rfl

/-- Positive refuse: wall-clock SLA theater is inadmissible — typed predicate only. -/
def refuseWallClockSlaTheater : Empty ⊕ FastPathAdmitRefusal :=
  Sum.inr .refuseWallClockSlaTheater

-- ================================================================
-- SECTION 4: Typed budget witness (declared ceiling, not measured)
-- ================================================================

structure LatencyBudgetWitness where
  lbPath            : AdmitPath
  lbBudgetMs        : Nat
  lbTypedPredicate  : Bool

def budgetWitnessFor (p : AdmitPath) : LatencyBudgetWitness :=
  { lbPath := p
    lbBudgetMs := admitPathBudgetMs p
    lbTypedPredicate := true }

theorem budgetWitnessFor_typed (p : AdmitPath) :
    (budgetWitnessFor p).lbTypedPredicate = true := rfl

theorem budgetWitnessFor_budget (p : AdmitPath) :
    (budgetWitnessFor p).lbBudgetMs = admitPathBudgetMs p := rfl

/-- Check surrogate estimated cost against typed budget — refuse if exceeded. -/
def checkTypedBudget (p : AdmitPath) (estimatedMs : Nat) :
    LatencyBudgetWitness ⊕ FastPathAdmitRefusal :=
  if _h : estimatedMs ≤ admitPathBudgetMs p then
    Sum.inl (budgetWitnessFor p)
  else
    Sum.inr (.refuseBudgetExceeded estimatedMs (admitPathBudgetMs p))

theorem checkTypedBudget_ok (p : AdmitPath) (estimatedMs : Nat)
    (h : estimatedMs ≤ admitPathBudgetMs p) :
    checkTypedBudget p estimatedMs = Sum.inl (budgetWitnessFor p) := by
  unfold checkTypedBudget
  rw [dif_pos h]

theorem checkTypedBudget_exceeded (p : AdmitPath) (estimatedMs : Nat)
    (h : admitPathBudgetMs p < estimatedMs) :
    checkTypedBudget p estimatedMs =
      Sum.inr (.refuseBudgetExceeded estimatedMs (admitPathBudgetMs p)) := by
  unfold checkTypedBudget
  rw [dif_neg (Nat.not_le_of_gt h)]

-- ================================================================
-- SECTION 5: Slow path composes Excitement (no second argmin)
-- ================================================================

/-- Merge / recovery slow path routes through `urgeRecovery` / `Excitement.select`. -/
noncomputable def slowPathRecovery {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecovery ctx

/-- Alias on bare `(prior, successors)` — same selector, no re-derivation. -/
noncomputable def excitementSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem slowPathRecovery_eq_urgeRecovery {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    slowPathRecovery ctx = urgeRecovery ctx :=
  rfl

/-- Slow-path admission class for merge/recovery candidates. -/
def classifySlowPath (c : FastPathCandidate) : AdmitPath ⊕ FastPathAdmitRefusal :=
  if c.fpIsMergeOrRecovery then
    Sum.inl .fullMergeRecovery
  else
    classifyAdmitPath c

theorem classifySlowPath_mergeRecovery (c : FastPathCandidate)
    (h : c.fpIsMergeOrRecovery = true) :
    classifySlowPath c = Sum.inl .fullMergeRecovery := by
  unfold classifySlowPath
  simp only [h, if_true]

end UMST.Urge.FastPathAdmit
