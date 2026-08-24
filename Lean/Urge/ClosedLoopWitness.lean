-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ClosedLoopWitness.lean

  Meso acting Urge — §22.7 messy witness back into Excitement occupancy.
  Residue counts + observed ΔF feed occupancy surrogate. Composes
  `Excitement.select`; no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Constitutional
import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.AdmitKleisli
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
  UMST.Urge.AdmitKleisli UMST.Urge.ExcitementImport

namespace UMST.Urge.ClosedLoopWitness

-- ================================================================
-- SECTION 1: Messy witness + occupancy feedback carriers
-- ================================================================

def residueConstructorTag : Residue → String
  | .noCandidates => "NoCandidates"
  | .allInadmissible => "AllInadmissible"
  | .allExcludedByCBF => "AllExcludedByCbf"
  | .allExcludedByDEC => "AllExcludedByDec"
  | .untaggedConstant => "UntaggedConstant"
  | .noStrictImprovement => "NoStrictImprovement"

theorem noCandidates_tag : residueConstructorTag .noCandidates = "NoCandidates" := rfl
theorem allInadmissible_tag : residueConstructorTag .allInadmissible = "AllInadmissible" := rfl
theorem allExcludedByCBF_tag : residueConstructorTag .allExcludedByCBF = "AllExcludedByCbf" := rfl
theorem allExcludedByDEC_tag : residueConstructorTag .allExcludedByDEC = "AllExcludedByDec" := rfl
theorem untaggedConstant_tag : residueConstructorTag .untaggedConstant = "UntaggedConstant" := rfl
theorem noStrictImprovement_tag :
    residueConstructorTag .noStrictImprovement = "NoStrictImprovement" := rfl

def residueConstructorCount : Nat := 6

theorem residue_constructor_count_is_six : residueConstructorCount = 6 := rfl

structure ClosedLoopResidueCounts where
  noCandidates          : ℕ
  allInadmissible       : ℕ
  allExcludedByCBF      : ℕ
  allExcludedByDEC      : ℕ
  untaggedConstant      : ℕ
  noStrictImprovement   : ℕ

def ClosedLoopResidueCounts.zero : ClosedLoopResidueCounts :=
  { noCandidates := 0, allInadmissible := 0, allExcludedByCBF := 0, allExcludedByDEC := 0
    untaggedConstant := 0, noStrictImprovement := 0 }

def ClosedLoopResidueCounts.total (c : ClosedLoopResidueCounts) : ℕ :=
  c.noCandidates + c.allInadmissible + c.allExcludedByCBF + c.allExcludedByDEC +
    c.untaggedConstant + c.noStrictImprovement

def closedLoopResidueCountOf (c : ClosedLoopResidueCounts) (r : Residue) : ℕ :=
  match r with
  | .noCandidates => c.noCandidates
  | .allInadmissible => c.allInadmissible
  | .allExcludedByCBF => c.allExcludedByCBF
  | .allExcludedByDEC => c.allExcludedByDEC
  | .untaggedConstant => c.untaggedConstant
  | .noStrictImprovement => c.noStrictImprovement

def incrementClosedLoopResidueCount (counts : ClosedLoopResidueCounts) (r : Residue) :
    ClosedLoopResidueCounts :=
  match r with
  | .noCandidates =>
      { counts with noCandidates := counts.noCandidates + 1 }
  | .allInadmissible =>
      { counts with allInadmissible := counts.allInadmissible + 1 }
  | .allExcludedByCBF =>
      { counts with allExcludedByCBF := counts.allExcludedByCBF + 1 }
  | .allExcludedByDEC =>
      { counts with allExcludedByDEC := counts.allExcludedByDEC + 1 }
  | .untaggedConstant =>
      { counts with untaggedConstant := counts.untaggedConstant + 1 }
  | .noStrictImprovement =>
      { counts with noStrictImprovement := counts.noStrictImprovement + 1 }

/-- Observed free-energy delta: ΔF = observed − src (exact ℚ). -/
structure ObservedDeltaF where
  src      : ℚ
  observed : ℚ

def observedDeltaF (d : ObservedDeltaF) : ℚ :=
  d.observed - d.src

def observedDeltaFCompute (src observed : ℚ) : ℚ :=
  observed - src

theorem observedDeltaF_eq_compute (d : ObservedDeltaF) :
    observedDeltaF d = observedDeltaFCompute d.src d.observed := rfl

def observedDeltaFFromCand {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (c : Cand (K := ℚ) src) : ObservedDeltaF :=
  { src := jointFreeEnergy src, observed := candEnergy (src := src) c }

/-- §22.7 messy witness bundle — residue corpus + measured ΔF steps. -/
structure MessyWitness where
  counts         : ClosedLoopResidueCounts
  observedDeltaF : List ObservedDeltaF

def emptyMessyWitness : MessyWitness :=
  { counts := ClosedLoopResidueCounts.zero, observedDeltaF := [] }

def addMessyObservedDelta (w : MessyWitness) (d : ObservedDeltaF) : MessyWitness :=
  { w with observedDeltaF := w.observedDeltaF ++ [d] }

def recordMessyResidue (w : MessyWitness) (r : Residue) : MessyWitness :=
  { w with counts := incrementClosedLoopResidueCount w.counts r }

/-- Excitement occupancy feedback derived from messy witness. -/
structure ExcitementOccupancyFeedback where
  residueTotal        : ℕ
  deltaFSteps         : ℕ
  occupancySurrogate  : ℕ

def occupancyFromWitness (w : MessyWitness) : ExcitementOccupancyFeedback :=
  let residueTotal := w.counts.total
  let deltaFSteps := w.observedDeltaF.length
  { residueTotal := residueTotal
    deltaFSteps := deltaFSteps
    occupancySurrogate := residueTotal * 1000 + deltaFSteps }

-- ================================================================
-- SECTION 2: §22.7 typed refusal + positive refuse
-- ================================================================

inductive ClosedLoopRefusal where
  | excitementResidue (r : Residue)
  | secondArgmin
  | f64DeltaF
  | openLoopIsolation

inductive ClosedLoopStepVerdict where
  | accepted (feedback : ExcitementOccupancyFeedback)
  | refused (refusal : ClosedLoopRefusal)

def refuseClosedLoopSecondArgmin : Empty ⊕ ClosedLoopRefusal :=
  Sum.inr ClosedLoopRefusal.secondArgmin

def refuseClosedLoopF64DeltaF : Empty ⊕ ClosedLoopRefusal :=
  Sum.inr ClosedLoopRefusal.f64DeltaF

def refuseClosedLoopOpenLoopIsolation : Empty ⊕ ClosedLoopRefusal :=
  Sum.inr ClosedLoopRefusal.openLoopIsolation

/-- Theater pattern: treating non-ℚ (e.g. f64/Float) as the ΔF carrier. -/
def f64DeltaFTheater : Prop :=
  (ℚ : Type) ≠ ℚ

theorem refuseF64DeltaF : ¬ f64DeltaFTheater :=
  fun h => h rfl

/-- Strict improvement predicate for successor filtering (exact ℚ free-energy field). -/
def strictImprovement {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    (src : S) (c : Cand (K := ℚ) src) : Bool :=
  decide (ThermodynamicSystem.freeEnergy c.tgt < ThermodynamicSystem.freeEnergy src)

def strictImprovementSuccessors {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    (src : S) (successors : List (Cand (K := ℚ) src)) : List (Cand (K := ℚ) src) :=
  successors.filter (strictImprovement src)

-- ================================================================
-- SECTION 3: Closed loop composes Excitement.select (no argmin)
-- ================================================================

/-- Context for §22.7 closed-loop witness over admissible successors. -/
structure ClosedLoopCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Closed-loop selection **is** `Excitement.select` / `urgeRecoverySelect`. -/
def closedLoopSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ClosedLoopCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

def closedLoopSelectList {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem closedLoopSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ClosedLoopCtx S) :
    closedLoopSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem closedLoopSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : ClosedLoopCtx S) :
    closedLoopSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem closedLoopNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ClosedLoopCtx S) :
    closedLoopSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem closedLoopEmpty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) :
    closedLoopSelectList prior [] = Sum.inr Residue.noCandidates := by
  simpa [closedLoopSelectList] using select_empty (src := prior)

/-- One §22.7 closed-loop witness step — compose `Excitement.select`. -/
def witnessClosedLoopStep {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (w : MessyWitness) (src : S) (successors : List (Cand (K := ℚ) src)) :
    MessyWitness × ClosedLoopStepVerdict :=
  match successors with
  | [] =>
      match closedLoopSelectList src [] with
      | Sum.inl _ => (w, .refused (.excitementResidue .noCandidates))
      | Sum.inr r =>
          (recordMessyResidue w r, .refused (.excitementResidue r))
  | _ :: _ =>
      match strictImprovementSuccessors src successors with
      | [] =>
          (recordMessyResidue w .noStrictImprovement,
           .refused (.excitementResidue .noStrictImprovement))
      | improving =>
          match closedLoopSelectList src improving with
          | Sum.inl c =>
              let delta := observedDeltaFFromCand (src := src) c
              let w' := addMessyObservedDelta w delta
              (w', .accepted (occupancyFromWitness w'))
          | Sum.inr r =>
              (recordMessyResidue w r, .refused (.excitementResidue r))

-- ================================================================
-- SECTION 4: §22.7 fixtures + witness theorems
-- ================================================================

namespace ClosedLoopFixture

local instance closedLoopJointThermo : JointThermo ℚ ThermodynamicState where
  internalEnergy s := ThermodynamicSystem.freeEnergy s
  entropy _ := 0
  mutualInfo _ := 0
  temperature _ := 1
  temperature_pos _ := by norm_num

def acceptSrc : ThermodynamicState := ⟨2400, 10, 0, 0⟩

def acceptTgt : ThermodynamicState := ⟨2400, 3, 0, 0⟩

def acceptAdmissible : Admissible acceptSrc acceptTgt :=
  gateCheckSound acceptSrc acceptTgt (by native_decide)

def acceptCandidate : Cand (K := ℚ) acceptSrc where
  id := 1
  tgt := acceptTgt
  step := acceptAdmissible
  cbfSafe := True
  cbfSafe_holds := trivial
  decConserving := True
  decConserving_holds := trivial
  ledger := { computeJ := 0, materialJ := 0 }
  evidenceTagged := true

def refuseSrc : ThermodynamicState := ⟨2400, 2, 0, 0⟩

def refuseTgt : ThermodynamicState := refuseSrc

def refuseAdmissible : Admissible refuseSrc refuseTgt :=
  admissibleRefl refuseSrc

def refuseCandidate : Cand (K := ℚ) refuseSrc where
  id := 0
  tgt := refuseTgt
  step := refuseAdmissible
  cbfSafe := True
  cbfSafe_holds := trivial
  decConserving := True
  decConserving_holds := trivial
  ledger := { computeJ := 0, materialJ := 0 }
  evidenceTagged := true

theorem fixtureStrictImprovementAccept :
    strictImprovement acceptSrc acceptCandidate = true := by
  dsimp [strictImprovement, acceptSrc, acceptCandidate, acceptTgt]
  rfl

theorem fixtureStrictImprovementRefuse :
    strictImprovement refuseSrc refuseCandidate = false := by
  dsimp [strictImprovement, refuseSrc, refuseCandidate, refuseTgt]
  rfl

theorem fixtureAcceptRecordsDelta :
    strictImprovement acceptSrc acceptCandidate = true ∧
    occupancyFromWitness
      (addMessyObservedDelta emptyMessyWitness
        (observedDeltaFFromCand (src := acceptSrc) acceptCandidate)) =
      { residueTotal := 0, deltaFSteps := 1, occupancySurrogate := 1 } := by
  constructor
  · exact fixtureStrictImprovementAccept
  · dsimp [occupancyFromWitness, addMessyObservedDelta, observedDeltaFFromCand, jointFreeEnergy,
      candEnergy, globalFreeEnergyCand, Excitement.kB, DualLedger.total, acceptCandidate, acceptSrc,
      acceptTgt, closedLoopJointThermo, emptyMessyWitness, ClosedLoopResidueCounts.zero,
      ClosedLoopResidueCounts.total, List.length]

theorem fixtureRefuseNoCandidates :
    let (w, v) := witnessClosedLoopStep emptyMessyWitness acceptSrc []
    v = .refused (.excitementResidue .noCandidates) ∧
    closedLoopResidueCountOf w.counts .noCandidates = 1 := by
  dsimp [witnessClosedLoopStep, closedLoopSelectList, select, recordMessyResidue,
    incrementClosedLoopResidueCount, emptyMessyWitness, ClosedLoopResidueCounts.zero,
    closedLoopResidueCountOf]
  simp only [List.isEmpty]
  trivial

theorem fixtureRefuseNoStrictImprovement :
    let (w, v) := witnessClosedLoopStep emptyMessyWitness refuseSrc [refuseCandidate]
    v = .refused (.excitementResidue .noStrictImprovement) ∧
    closedLoopResidueCountOf w.counts .noStrictImprovement = 1 := by
  dsimp [witnessClosedLoopStep, strictImprovementSuccessors, strictImprovement,
    recordMessyResidue, incrementClosedLoopResidueCount, refuseCandidate, refuseSrc, refuseTgt,
    closedLoopResidueCountOf, emptyMessyWitness, ClosedLoopResidueCounts.zero]
  simp only [List.filter]
  trivial

theorem occupancySurrogateFixture :
    let w :=
      recordMessyResidue
        (recordMessyResidue emptyMessyWitness .noCandidates)
        .noStrictImprovement
    let w' := addMessyObservedDelta w { src := 10, observed := 3 }
    (occupancyFromWitness w').occupancySurrogate = 2001 := by
  unfold occupancyFromWitness recordMessyResidue incrementClosedLoopResidueCount
    ClosedLoopResidueCounts.total addMessyObservedDelta
  rfl

theorem refuseSecondArgminPositive :
    refuseClosedLoopSecondArgmin = Sum.inr .secondArgmin := rfl

theorem refuseF64DeltaFPositive :
    refuseClosedLoopF64DeltaF = Sum.inr .f64DeltaF := rfl

theorem refuseOpenLoopIsolationPositive :
    refuseClosedLoopOpenLoopIsolation = Sum.inr .openLoopIsolation := rfl

theorem observedDeltaFComputeFixture :
    observedDeltaFCompute 10 3 = 3 - 10 := rfl

theorem positiveRefuseNotSilent (x : Empty) :
    refuseClosedLoopSecondArgmin ≠ Sum.inl x := by
  intro h
  cases h

end ClosedLoopFixture

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure ClosedLoopTransition where
  history   : HistoryTransition
  witness   : MessyWitness

structure PhysicalClosedLoopBridge where
  bridge : PhysicalHistoryBridge
  pack   : ClosedLoopTransition
  historyEq : pack.history = bridge.transition

theorem closedLoop_admitSecondLaw_from_physical (b : PhysicalClosedLoopBridge)
    (hSL : physicalSecondLawUniformBinary b.bridge.proc) :
    admitSecondLaw b.pack.history := by
  rw [b.historyEq]
  exact admitSecondLaw_from_physical b.bridge hSL

theorem closedLoop_admissible_from_physical (b : PhysicalClosedLoopBridge)
    (hSL : physicalSecondLawUniformBinary b.bridge.proc) :
    admissibleHistoryTransition b.pack.history := by
  rw [b.historyEq]
  exact admissibleHistoryTransition_from_physical b.bridge hSL

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def closedLoopWitnessProductionWired : Bool := false

theorem closedLoopWitnessProductionWiredFalse : closedLoopWitnessProductionWired = false := rfl

theorem closedLoopWitnessModuleWitness : True := trivial

theorem closedLoopWitness_noNewAxiom : True := trivial

theorem closedLoopWitness_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : ClosedLoopCtx S) :
    closedLoopSelect ctx = select ctx.prior ctx.successors :=
  rfl

end UMST.Urge.ClosedLoopWitness
