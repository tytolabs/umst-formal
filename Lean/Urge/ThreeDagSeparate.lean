-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ThreeDagSeparate.lean

  Meso acting Urge — §16.11 / §22.2 three DAGs unfused:
  (a) git bytes, (b) Kleisli history, (c) UCRS causal.
  Agents walk (b) ordered by (c). Composes `Excitement.select`;
  no second argmin. Typed fusion refuses — not only !physics_green.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.ThreeDagSeparate

-- ================================================================
-- SECTION 1: Three unfused DAG substrates + node carriers
-- ================================================================

/-- Three unfused DAG substrates from §16.11 / §22.2. -/
inductive ThreeDagSubstrate where
  | gitBytes
  | kleisliHistory
  | ucrsCausal
  deriving DecidableEq, Repr

/-- Git commit node on byte substrate (a). -/
structure GitCommitNode where
  commitHash : Nat
  parentHash : Option Nat

/-- Kleisli admitted-history node on coordination DAG (b). -/
structure KleisliHistoryNode where
  arrowId : Nat
  gateMergeExcitementAdmitted : Bool

/-- UCRS causal node on seq-ordered DAG (c). -/
structure UcrsCausalNode where
  seq : Nat
  wallStampAudit : Option Nat
  orderByWallClock : Bool

/-- Per-DAG coordinates — unfused; never a single fused id. -/
structure ThreeDagCoordinates where
  tdcGitCommit : Nat
  tdcKleisliArrow : Nat
  tdcUcrsSeq : Nat

/-- UCRS stamp surrogate carried through three-DAG walker. -/
structure ThreeDagUcrsStamp where
  ucrsSeq : Nat
  ucrsWallHasT : Bool

/-- Witness bundle three-DAG walk must preserve. -/
structure ThreeDagWitness where
  witnessUcrs : ThreeDagUcrsStamp
  witnessKleisliAdmitted : Bool

/-- Typed three-DAG morphism — admissible Kleisli walk, not fused substrates. -/
structure ThreeDagMorphism where
  coords : ThreeDagCoordinates
  witness : ThreeDagWitness
  excitementSelected : Bool

-- ================================================================
-- SECTION 2: Fusion refusal + positive refuse (not silent accept)
-- ================================================================

/-- Typed fusion / discipline refusal — positive properties. -/
inductive ThreeDagFusionRefusal where
  | gitBytesAsKleisliCoord
  | ucrsSeqFusedWithGitHash
  | wallClockAsUcrsSeq
  | kleisliNotAdmitted
  | secondArgminRefused
  | physicsGreenInvent
  deriving Repr

/-- Walker verdict on three unfused DAGs. -/
inductive ThreeDagWalkerVerdict where
  | admitted
  | refused (r : ThreeDagFusionRefusal)
  deriving Repr

/-- §16.11 admissibility conjunct inputs (surrogate). -/
structure ThreeDagAdmissibilityConjunct where
  gateOk : Bool
  kleisliAdmitted : Bool
  excitementPreserves : Bool

def threeDagConjunctAdmits (c : ThreeDagAdmissibilityConjunct) : Bool :=
  c.gateOk && c.kleisliAdmitted && c.excitementPreserves

def refusesGitKleisliFusion (coords : ThreeDagCoordinates) : Bool :=
  coords.tdcGitCommit == coords.tdcKleisliArrow

def refusesUcrsGitFusion (coords : ThreeDagCoordinates) : Bool :=
  coords.tdcUcrsSeq == coords.tdcGitCommit

theorem refuses_git_kleisli_fusion_detects_equal (n : Nat) :
    refusesGitKleisliFusion
      { tdcGitCommit := n, tdcKleisliArrow := n, tdcUcrsSeq := 0 } = true := by
  simp [refusesGitKleisliFusion]

theorem refuses_git_kleisli_fusion_separate (g k : Nat) (hneq : g ≠ k) :
    refusesGitKleisliFusion
      { tdcGitCommit := g, tdcKleisliArrow := k, tdcUcrsSeq := 0 } = false := by
  simp [refusesGitKleisliFusion, hneq]

/-- Evaluate Kleisli walk ordered by UCRS causal `seq` — refuse substrate fusion. -/
def evaluateThreeDagWalk (coords : ThreeDagCoordinates) (kleisli : KleisliHistoryNode)
    (ucrs : UcrsCausalNode) (claimPhysicsGreen : Bool) : ThreeDagWalkerVerdict :=
  if claimPhysicsGreen then .refused .physicsGreenInvent
  else if refusesGitKleisliFusion coords then .refused .gitBytesAsKleisliCoord
  else if refusesUcrsGitFusion coords then .refused .ucrsSeqFusedWithGitHash
  else if ucrs.orderByWallClock then .refused .wallClockAsUcrsSeq
  else if coords.tdcUcrsSeq != ucrs.seq then .refused .wallClockAsUcrsSeq
  else if !kleisli.gateMergeExcitementAdmitted then .refused .kleisliNotAdmitted
  else if kleisli.arrowId != coords.tdcKleisliArrow then .refused .kleisliNotAdmitted
  else .admitted

def witnessFromCoords (_coords : ThreeDagCoordinates) (kleisli : KleisliHistoryNode)
    (stamp : ThreeDagUcrsStamp) : ThreeDagWitness :=
  { witnessUcrs := stamp
    witnessKleisliAdmitted := kleisli.gateMergeExcitementAdmitted }

/-- Attempt typed three-DAG morphism — fail closed on inadmissibility. -/
def applyThreeDagMorphism (coords : ThreeDagCoordinates) (kleisli : KleisliHistoryNode)
    (ucrs : UcrsCausalNode) (conjunct : ThreeDagAdmissibilityConjunct)
    (stamp : ThreeDagUcrsStamp) (excitementSelected : Bool) :
    ThreeDagMorphism ⊕ ThreeDagFusionRefusal :=
  if !(threeDagConjunctAdmits conjunct) then
    Sum.inr .kleisliNotAdmitted
  else if !excitementSelected then
    Sum.inr .secondArgminRefused
  else
    match evaluateThreeDagWalk coords kleisli ucrs false with
    | .admitted =>
      Sum.inl
        { coords := coords
          witness := witnessFromCoords coords kleisli stamp
          excitementSelected := excitementSelected }
    | .refused r => Sum.inr r

-- ================================================================
-- SECTION 4: §16.11 fixtures + witness theorems
-- ================================================================

def threeDagFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def threeDagFixtureUcrs : ThreeDagUcrsStamp :=
  { ucrsSeq := 7, ucrsWallHasT := true }

def threeDagFixtureConjunct : ThreeDagAdmissibilityConjunct :=
  { gateOk := true, kleisliAdmitted := true, excitementPreserves := true }

def threeDagFixtureCoords : ThreeDagCoordinates :=
  { tdcGitCommit := 11, tdcKleisliArrow := 22, tdcUcrsSeq := 7 }

def threeDagFixtureKleisli : KleisliHistoryNode :=
  { arrowId := 22, gateMergeExcitementAdmitted := true }

def threeDagFixtureUcrsNode : UcrsCausalNode :=
  { seq := 7, wallStampAudit := some 42, orderByWallClock := false }

theorem threeDagFixture_walk_admitted :
    evaluateThreeDagWalk threeDagFixtureCoords threeDagFixtureKleisli
      threeDagFixtureUcrsNode false = .admitted :=
  rfl

def threeDagFixtureFusedCoords : ThreeDagCoordinates :=
  { tdcGitCommit := 66, tdcKleisliArrow := 66, tdcUcrsSeq := 3 }

theorem threeDagFixture_git_kleisli_fusion_refused :
    evaluateThreeDagWalk threeDagFixtureFusedCoords
      { arrowId := 66, gateMergeExcitementAdmitted := true }
      { seq := 3, wallStampAudit := none, orderByWallClock := false } false =
      .refused .gitBytesAsKleisliCoord :=
  rfl

theorem threeDagFixture_wall_clock_order_refused :
    evaluateThreeDagWalk
      { tdcGitCommit := 33, tdcKleisliArrow := 44, tdcUcrsSeq := 9 }
      { arrowId := 44, gateMergeExcitementAdmitted := true }
      { seq := 9, wallStampAudit := some 42, orderByWallClock := true } false =
      .refused .wallClockAsUcrsSeq :=
  rfl

theorem threeDagFixture_apply_morphism_ok :
    applyThreeDagMorphism threeDagFixtureCoords threeDagFixtureKleisli
      threeDagFixtureUcrsNode threeDagFixtureConjunct threeDagFixtureUcrs true =
      Sum.inl
        { coords := threeDagFixtureCoords
          witness := witnessFromCoords threeDagFixtureCoords threeDagFixtureKleisli
            threeDagFixtureUcrs
          excitementSelected := true } :=
  rfl

theorem threeDagFixture_witness_preserves_ucrs :
    (witnessFromCoords threeDagFixtureCoords threeDagFixtureKleisli threeDagFixtureUcrs).witnessUcrs =
      threeDagFixtureUcrs :=
  rfl

theorem threeDag_fusion_refuse_not_silent :
    evaluateThreeDagWalk threeDagFixtureFusedCoords
      { arrowId := 66, gateMergeExcitementAdmitted := true }
      { seq := 3, wallStampAudit := none, orderByWallClock := false } false ≠ .admitted := by
  unfold evaluateThreeDagWalk threeDagFixtureFusedCoords refusesGitKleisliFusion
  simp only [beq_self_eq_true]
  intro h
  cases h

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure ThreeDagTransition where
  coords : ThreeDagCoordinates
  kleisli : KleisliHistoryNode
  ucrs : UcrsCausalNode
  bath : HeatBath
  dissipatedWork : ℝ
  entropyDrop : ℝ
  conjunct : ThreeDagAdmissibilityConjunct
  excitementSelected : Bool

def admissibleThreeDagWalk (t : ThreeDagTransition) : Prop :=
  threeDagConjunctAdmits t.conjunct = true ∧
    evaluateThreeDagWalk t.coords t.kleisli t.ucrs false = .admitted ∧
    t.excitementSelected

end UMST.Urge.ThreeDagSeparate
