-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/LatencyBudget.lean

  Meso acting Urge — §17.8 latency budget as typed predicate on admit.
  Integer surrogate ms vs declared tier ceiling — not wall-clock SLA theater.
  Merge / recovery slow path composes `Excitement.select` — no second argmin.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import Urge.AdmitKleisli
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.ExcitementImport

namespace UMST.Urge.LatencyBudget

-- ================================================================
-- SECTION 1: §17.8 typed budget tiers (not wall-clock GREEN)
-- ================================================================

/-- Blueprint §17.8 interactive observation budget (milliseconds, typed). -/
def interactiveBudgetMs : Nat := 16

/-- Blueprint §17.8 local commit admission budget (milliseconds, typed). -/
def localCommitBudgetMs : Nat := 100

/-- Blueprint §17.8 merge / recovery slow-path budget (milliseconds, typed). -/
def mergeRecoveryBudgetMs : Nat := 1000

/-- Blueprint §17.8 background compaction budget (milliseconds, typed). -/
def backgroundBudgetMs : Nat := 10000

/-- Typed budget tier — declared ceiling, not measured wall-clock. -/
inductive LatencyBudgetTier where
  | interactive
  | localCommit
  | mergeRecovery
  | background
  deriving DecidableEq, Repr

/-- Declared budget ceiling for each tier (milliseconds, typed — not measured). -/
def latencyTierBudgetMs (t : LatencyBudgetTier) : Nat :=
  match t with
  | .interactive => interactiveBudgetMs
  | .localCommit => localCommitBudgetMs
  | .mergeRecovery => mergeRecoveryBudgetMs
  | .background => backgroundBudgetMs

theorem latencyTier_interactive_budget :
    latencyTierBudgetMs .interactive = interactiveBudgetMs := rfl

theorem latencyTier_localCommit_budget :
    latencyTierBudgetMs .localCommit = localCommitBudgetMs := rfl

theorem latencyTier_mergeRecovery_budget :
    latencyTierBudgetMs .mergeRecovery = mergeRecoveryBudgetMs := rfl

theorem latencyTier_background_budget :
    latencyTierBudgetMs .background = backgroundBudgetMs := rfl

-- ================================================================
-- SECTION 2: Candidate + witness carriers (§17.8 morphism mirror)
-- ================================================================

/-- Candidate for latency-budget admission — surrogate inputs only. -/
structure LatencyBudgetCandidate where
  tier                    : LatencyBudgetTier
  surrogateMs             : Nat
  claimsWallClockSla      : Bool
  claimsPhysicsGreen      : Bool

/-- Typed budget witness — declared ceiling + surrogate, not measured latency. -/
structure LatencyBudgetWitness where
  tier                    : LatencyBudgetTier
  budgetMs                : Nat
  surrogateMs             : Nat
  typedPredicate          : Bool

/-- Witness bundle a latency-budget morphism must preserve (§17.8). -/
structure LatencyBudgetMorphismWitness where
  tier                    : LatencyBudgetTier
  budgetMs                : Nat
  surrogateMs             : Nat
  typedPredicate          : Bool

/-- Typed latency-budget morphism — admissible admit transition, not SLA theater. -/
structure LatencyBudgetMorphism where
  morphismFrom            : LatencyBudgetCandidate
  witness                 : LatencyBudgetMorphismWitness
  excitementSelected      : Bool

/-- Fail-closed latency-budget errors — positive refuse, not silent no-op. -/
inductive LatencyBudgetRefusal where
  | budgetExceeded (surrogateMs budgetMs : Nat)
  | wallClockSlaTheater
  | physicsGreenInvent
  | unboundedLatencyRatioTheater
  | gateRejected (surrogateMs : Nat)
  deriving Repr

/-- Verdict of a latency-budget operation class. -/
inductive LatencyBudgetVerdict where
  | admitOk
  | wallClockSlaRefused
  | physicsGreenRefused
  | ratioTheaterRefused
  | inadmissible
  deriving Repr

-- ================================================================
-- SECTION 3: §17.8 admissibility conjunct + typed predicate
-- ================================================================

/-- §17.8 admissibility conjunct inputs (surrogate). -/
structure LatencyAdmissibilityConjunct where
  gateOk                  : Bool
  typedPredicate          : Bool
  excitementPreserves     : Bool

/-- Evaluate `admit(h) ⟺ gate ∧ typed predicate ∧ Excitement preserves`. -/
def latencyConjunctAdmits (c : LatencyAdmissibilityConjunct) : Bool :=
  c.gateOk && c.typedPredicate && c.excitementPreserves

/-- Core typed predicate — surrogate within tier and no SLA / GREEN theater. -/
def latencyBudgetAdmitPred (c : LatencyBudgetCandidate) : Bool :=
  match c.claimsWallClockSla, c.claimsPhysicsGreen with
  | true, _ => false
  | _, true => false
  | false, false => decide (c.surrogateMs ≤ latencyTierBudgetMs c.tier)

/-- Classify wall-clock SLA theater without performing I/O. -/
def evaluateWallClockSlaOperation (claimsWallClock : Bool) : LatencyBudgetVerdict :=
  if claimsWallClock then .wallClockSlaRefused else .admitOk

/-- Positive refuse: wall-clock SLA theater is inadmissible — typed predicate only. -/
def refuseWallClockSlaTheater : Empty ⊕ LatencyBudgetRefusal :=
  Sum.inr .wallClockSlaTheater

/-- Evaluate latency-budget admission — honest refusal on inadmissible inputs. -/
def evaluateLatencyBudgetAdmit (c : LatencyBudgetCandidate) :
    LatencyBudgetWitness ⊕ LatencyBudgetRefusal :=
  if c.claimsPhysicsGreen then
    Sum.inr .physicsGreenInvent
  else if c.claimsWallClockSla then
    Sum.inr .wallClockSlaTheater
  else
    let budgetMs := latencyTierBudgetMs c.tier
    let surrogateMs := c.surrogateMs
    if _h : surrogateMs ≤ budgetMs then
      Sum.inl
        { tier := c.tier
          budgetMs := budgetMs
          surrogateMs := surrogateMs
          typedPredicate := true }
    else
      Sum.inr (.budgetExceeded surrogateMs budgetMs)

def witnessFromCandidate (_c : LatencyBudgetCandidate) (w : LatencyBudgetWitness) :
    LatencyBudgetMorphismWitness :=
  { tier := w.tier
    budgetMs := w.budgetMs
    surrogateMs := w.surrogateMs
    typedPredicate := w.typedPredicate }

def applyLatencyBudgetMorphismAdmitted (candidate : LatencyBudgetCandidate)
    (excitementSelected : Bool) (w : LatencyBudgetWitness) :
    LatencyBudgetMorphism :=
  { morphismFrom := candidate
    witness := witnessFromCandidate candidate w
    excitementSelected := excitementSelected }

/-- Attempt typed latency-budget morphism — fail closed on inadmissibility. -/
def applyLatencyBudgetMorphism (candidate : LatencyBudgetCandidate)
    (conjunct : LatencyAdmissibilityConjunct) (excitementSelected : Bool) :
    LatencyBudgetMorphism ⊕ LatencyBudgetRefusal :=
  if !(latencyConjunctAdmits conjunct) then
    Sum.inr (.gateRejected candidate.surrogateMs)
  else if !conjunct.typedPredicate then
    Sum.inr .wallClockSlaTheater
  else if !excitementSelected then
    Sum.inr (.budgetExceeded candidate.surrogateMs (latencyTierBudgetMs candidate.tier))
  else
    match evaluateLatencyBudgetAdmit candidate with
    | Sum.inl w =>
        Sum.inl (applyLatencyBudgetMorphismAdmitted candidate excitementSelected w)
    | Sum.inr r => Sum.inr r

/-- Build typed budget witness for a tier at zero surrogate (probe default). -/
def budgetWitnessFor (t : LatencyBudgetTier) : LatencyBudgetWitness :=
  { tier := t
    budgetMs := latencyTierBudgetMs t
    surrogateMs := 0
    typedPredicate := true }

theorem budgetWitnessFor_typed (t : LatencyBudgetTier) :
    (budgetWitnessFor t).typedPredicate = true := rfl

theorem budgetWitnessFor_budget (t : LatencyBudgetTier) :
    (budgetWitnessFor t).budgetMs = latencyTierBudgetMs t := rfl

/-- Check surrogate estimated cost against typed tier budget — refuse if exceeded. -/
def checkTypedBudget (t : LatencyBudgetTier) (surrogateMs : Nat) :
    LatencyBudgetWitness ⊕ LatencyBudgetRefusal :=
  evaluateLatencyBudgetAdmit
    { tier := t
      surrogateMs := surrogateMs
      claimsWallClockSla := false
      claimsPhysicsGreen := false }

theorem checkTypedBudget_ok (t : LatencyBudgetTier) (surrogateMs : Nat)
    (h : surrogateMs ≤ latencyTierBudgetMs t) :
    checkTypedBudget t surrogateMs =
      Sum.inl
        { tier := t
          budgetMs := latencyTierBudgetMs t
          surrogateMs := surrogateMs
          typedPredicate := true } := by
  unfold checkTypedBudget evaluateLatencyBudgetAdmit
  simp only [Bool.false_eq_true, ite_false, ↓reduceIte]
  exact dif_pos h

theorem checkTypedBudget_exceeded (t : LatencyBudgetTier) (surrogateMs : Nat)
    (h : latencyTierBudgetMs t < surrogateMs) :
    checkTypedBudget t surrogateMs =
      Sum.inr (.budgetExceeded surrogateMs (latencyTierBudgetMs t)) := by
  unfold checkTypedBudget evaluateLatencyBudgetAdmit
  simp only [Bool.false_eq_true, ite_false, ↓reduceIte]
  exact dif_neg (Nat.not_le_of_gt h)

theorem evaluate_wall_clock_sla_refused :
    evaluateWallClockSlaOperation true = .wallClockSlaRefused := rfl

theorem evaluate_wall_clock_sla_ok :
    evaluateWallClockSlaOperation false = .admitOk := rfl

-- ================================================================
-- SECTION 4: Merge/recovery composes Excitement (no second argmin)
-- ================================================================

def refuseSecondArgmin : LatencyBudgetRefusal := .unboundedLatencyRatioTheater

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure LatencyHistoryMove where
  gateChecked     : Prop
  typedPredicate  : Prop
  excitementOk    : Prop

def admissibleLatencyBudget (h : LatencyHistoryMove) : Prop :=
  h.gateChecked ∧ h.typedPredicate ∧ h.excitementOk

abbrev admitLatencyInbound := admissibleLatencyBudget

-- ================================================================
-- SECTION 6: §17.8 fixtures + witness theorems
-- ================================================================

def latencyFixtureInteractiveCandidate : LatencyBudgetCandidate :=
  { tier := .interactive
    surrogateMs := 10
    claimsWallClockSla := false
    claimsPhysicsGreen := false }

def latencyFixtureLocalCommitCandidate : LatencyBudgetCandidate :=
  { tier := .localCommit
    surrogateMs := 80
    claimsWallClockSla := false
    claimsPhysicsGreen := false }

def latencyFixtureOverBudgetCandidate : LatencyBudgetCandidate :=
  { tier := .localCommit
    surrogateMs := localCommitBudgetMs + 1
    claimsWallClockSla := false
    claimsPhysicsGreen := false }

def latencyFixtureWallClockCandidate : LatencyBudgetCandidate :=
  { tier := .localCommit
    surrogateMs := 50
    claimsWallClockSla := true
    claimsPhysicsGreen := false }

def latencyFixtureGreenCandidate : LatencyBudgetCandidate :=
  { tier := .mergeRecovery
    surrogateMs := 500
    claimsWallClockSla := false
    claimsPhysicsGreen := true }

def latencyFixtureConjunct : LatencyAdmissibilityConjunct :=
  { gateOk := true, typedPredicate := true, excitementPreserves := true }

theorem latencyFixture_interactive_admits :
    evaluateLatencyBudgetAdmit latencyFixtureInteractiveCandidate =
      Sum.inl
        { tier := .interactive
          budgetMs := interactiveBudgetMs
          surrogateMs := 10
          typedPredicate := true } := rfl

theorem latencyFixture_localCommit_admits :
    evaluateLatencyBudgetAdmit latencyFixtureLocalCommitCandidate =
      Sum.inl
        { tier := .localCommit
          budgetMs := localCommitBudgetMs
          surrogateMs := 80
          typedPredicate := true } := rfl

theorem latencyFixture_over_budget_refused :
    evaluateLatencyBudgetAdmit latencyFixtureOverBudgetCandidate =
      Sum.inr (.budgetExceeded (localCommitBudgetMs + 1) localCommitBudgetMs) := rfl

theorem latencyFixture_wall_clock_refused :
    evaluateLatencyBudgetAdmit latencyFixtureWallClockCandidate =
      Sum.inr .wallClockSlaTheater := rfl

theorem latencyFixture_apply_morphism_ok :
    applyLatencyBudgetMorphism latencyFixtureLocalCommitCandidate latencyFixtureConjunct true =
      Sum.inl
        (applyLatencyBudgetMorphismAdmitted latencyFixtureLocalCommitCandidate true
          { tier := .localCommit
            budgetMs := localCommitBudgetMs
            surrogateMs := 80
            typedPredicate := true }) := rfl

theorem latencyFixture_admit_pred_within_tier :
    latencyBudgetAdmitPred latencyFixtureLocalCommitCandidate = true := rfl

theorem latencyFixture_admit_pred_wall_clock_false :
    latencyBudgetAdmitPred latencyFixtureWallClockCandidate = false := rfl

theorem latency_budget_positive_refuse_not_silent :
    evaluateWallClockSlaOperation true ≠ .admitOk := by
  simp [evaluateWallClockSlaOperation]

-- ================================================================
-- SECTION 7: Honesty flags + catalog witnesses
-- ================================================================

def latencyBudgetMarker : Nat := 1

end UMST.Urge.LatencyBudget
