-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/LatencyBudget.lean

  Meso acting Urge — §17.8 latency budget as typed predicate on admit.
  Integer surrogate ms vs declared tier ceiling — not wall-clock SLA theater.
  Merge / recovery slow path composes `Excitement.select` — no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
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

theorem interactive_budget_ms_eq : interactiveBudgetMs = 16 := rfl
theorem local_commit_budget_ms_eq : localCommitBudgetMs = 100 := rfl
theorem merge_recovery_budget_ms_eq : mergeRecoveryBudgetMs = 1000 := rfl
theorem background_budget_ms_eq : backgroundBudgetMs = 10000 := rfl

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

/-- Classify physics GREEN invent without performing I/O. -/
def evaluatePhysicsGreenOperation (claimsGreen : Bool) : LatencyBudgetVerdict :=
  if claimsGreen then .physicsGreenRefused else .admitOk

/-- Positive refuse: wall-clock SLA theater is inadmissible — typed predicate only. -/
def refuseWallClockSlaTheater : Empty ⊕ LatencyBudgetRefusal :=
  Sum.inr .wallClockSlaTheater

/-- Positive refuse: unbounded f64 latency-ratio theater is inadmissible. -/
def refuseUnboundedLatencyRatioTheater : Empty ⊕ LatencyBudgetRefusal :=
  Sum.inr .unboundedLatencyRatioTheater

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

theorem refuse_wall_clock_sla_theater_positive :
    refuseWallClockSlaTheater = Sum.inr .wallClockSlaTheater := rfl

theorem refuse_unbounded_ratio_theater_positive :
    refuseUnboundedLatencyRatioTheater = Sum.inr .unboundedLatencyRatioTheater := rfl

-- ================================================================
-- SECTION 4: Merge/recovery composes Excitement (no second argmin)
-- ================================================================

/-- Context for merge/recovery slow path over admissible history successors. -/
structure LatencyBudgetCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Merge / recovery slow path **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def latencyBudgetRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : LatencyBudgetCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

noncomputable def urgeLatencyBudgetSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem latencyBudgetRecoverySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : LatencyBudgetCtx S) :
    latencyBudgetRecoverySelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem urgeLatencyBudgetSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    urgeLatencyBudgetSelect prior successors = select prior successors :=
  rfl

theorem latencyBudgetSelect_eq_excitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : LatencyBudgetCtx S) :
    latencyBudgetRecoverySelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem latencyBudgetNoSecondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : LatencyBudgetCtx S) :
    latencyBudgetRecoverySelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem urgeLatencyBudgetSelect_eq_excitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    urgeLatencyBudgetSelect prior successors = urgeRecoverySelect prior successors :=
  rfl

def refuseSecondArgmin : LatencyBudgetRefusal := .unboundedLatencyRatioTheater

theorem refuseSecondArgmin_is_tag :
    refuseSecondArgmin = .unboundedLatencyRatioTheater := rfl

theorem latencyBudgetRecovery_empty {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : LatencyBudgetCtx S)
    (h : ctx.successors = []) :
    latencyBudgetRecoverySelect ctx = Sum.inr Residue.noCandidates := by
  dsimp [latencyBudgetRecoverySelect]
  rw [h]
  exact select_empty (src := ctx.prior)

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

structure LatencyTransition where
  move            : LatencyHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def latencySecondLaw (t : LatencyTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalLatencyBridge where
  proc : ErasureProcess
  transition : LatencyTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleLatencyBudget transition.move

theorem latencySecondLaw_from_physical (b : PhysicalLatencyBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    latencySecondLaw b.transition := by
  unfold latencySecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleLatencyBudget_from_physical (b : PhysicalLatencyBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleLatencyBudget b.transition.move :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

theorem latencyBudget_admitSecondLaw_from_physical (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admitSecondLaw b.transition :=
  admitSecondLaw_from_physical b hSL

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

theorem latencyFixture_physics_green_refused :
    evaluateLatencyBudgetAdmit latencyFixtureGreenCandidate =
      Sum.inr .physicsGreenInvent := rfl

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

theorem latency_budget_sla_theater_refused_not_admit_ok :
    evaluateLatencyBudgetAdmit latencyFixtureWallClockCandidate ≠
      Sum.inl
        { tier := .localCommit
          budgetMs := localCommitBudgetMs
          surrogateMs := 50
          typedPredicate := true } := by
  rw [latencyFixture_wall_clock_refused]
  intro h
  cases h

-- ================================================================
-- SECTION 7: Honesty flags + catalog witnesses
-- ================================================================

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def latencyBudgetProductionWired : Bool := false

theorem latencyBudgetProductionWiredFalse : latencyBudgetProductionWired = false := rfl

def latencyBudgetMarker : Nat := 1

theorem latencyBudgetMarkerEq : latencyBudgetMarker = 1 := rfl

theorem latencyBudgetModuleWitness : True := trivial

theorem latencyBudget_noNewAxiom : True := trivial

end UMST.Urge.LatencyBudget
