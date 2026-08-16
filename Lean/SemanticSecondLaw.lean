SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
/-
  UMST-Formal: SemanticSecondLaw.lean

  **HCOM-001 — Foundational semantic invariant** (Human Communication Blueprint §2).

  Communicative analogue of `LandauerLaw.physicalSecondLaw`:
    meaningful transitions preserve structural consistency in the geometric layer
    and account for the information (Landauer) cost of understanding or updating
    a shared model.

  **Single-axiom discipline:** this module adds **zero** Lean `axiom` declarations.
  The sole project axiom remains `physicalSecondLaw`.  `semanticSecondLaw` is the
  named foundational `Prop`; entropy accounting on physically bridged transitions
  is **derived** from `physicalSecondLaw` via `semanticSecondLaw_from_physical`.

  L₀ boundary: does **not** import `Gate.lean` or Kleisli composition.
  Connection to runtime semantic gate (P6) is via `CoordinationCost` reporting functors.

  Explicit non-claims:
    - Full `MeaningState` SDF geometry (HCOM-002 categorical layer — see `MeaningState.lean`).
    - Epistemic MI → joules without `PhysicalMiBridgeWitness` (see `CoordinationCost`).
    - Semantic truth or deployed NLU — reporting / admissibility predicates only.
-/

import LandauerLaw
import InfoTheory
import CoordinationCost

open Real Finset UMST.LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist
open UMST.CoordinationCost

namespace UMST.SemanticSecondLaw

-- ================================================================
-- SECTION 1: Semantic transition carrier (geometric layer scaffold)
-- ================================================================

/-- Cognitive / communicative heat bath at absolute temperature T > 0 [K].
    Mirrors `HeatBath` — semantic "temperature" scales Landauer understanding cost. -/
structure SemanticBath where
  bathTemp : {T : ℝ // 0 < T}

/-- Convert a physical heat bath to the semantic reporting bath (same carrier). -/
def semanticBathOf (hb : HeatBath) : SemanticBath where
  bathTemp := hb.bathTemp

/-- A meaningful communicative transition on a finite shared-model alphabet.
    `prior` / `post` are distributions over geometric meaning indices;
    `consistencyDefect` is 0 iff structural shapes are mutually consistent;
    `understandingWork` records dissipated semantic work [J] (Landauer-linked). -/
structure CommunicativeTransition (n : ℕ) where
  bath : SemanticBath
  prior : ProbDist n
  post : ProbDist n
  understandingWork : ℝ
  consistencyDefect : ℝ

/-- Structural consistency: no contradictory shapes in the shared context. -/
def structurallyConsistent {n : ℕ} (t : CommunicativeTransition n) : Prop :=
  t.consistencyDefect = 0

/-- Model-uncertainty reduction (nats) from updating the shared geometric state. -/
noncomputable def modelUncertaintyDrop {n : ℕ} (t : CommunicativeTransition n) : ℝ :=
  shannonEntropy t.prior - shannonEntropy t.post

/-- Proposal–outcome joint witness for MI preservation checks. -/
structure ProposalOutcomeWitness (n m : ℕ) where
  joint : JointDist n m

/-- MI preservation: mutual information between proposal and resulting state
    meets or exceeds the configured threshold (no free erasure of prior meaning). -/
def miPreserved (threshold : ℝ) {n m : ℕ} (w : ProposalOutcomeWitness n m) : Prop :=
  threshold ≤ mutualInformation w.joint

-- ================================================================
-- SECTION 2: Foundational invariant (named Prop — not a Lean axiom)
-- ================================================================

/-- **Semantic Second Law** (foundational invariant — blueprint §2):

    A meaningful communicative transition must:
      (1) preserve structural consistency (`consistencyDefect = 0`);
      (2) satisfy Clausius-style entropy accounting on the shared model:
          ΔS_model ≤ W_understanding / T;
      (3) preserve mutual information above `miThreshold` on the declared joint.

    This extends `physicalSecondLaw` in the semantic fiber without adding a
    second project axiom.  Physical realizations discharge (2) via
    `semanticSecondLaw_from_physical`; Landauer floors discharge via
    `understandingCostLandauerBound`. -/
def semanticSecondLaw {n m : ℕ} (miThreshold : ℝ)
    (t : CommunicativeTransition n) (w : ProposalOutcomeWitness n m) : Prop :=
  structurallyConsistent t ∧
  modelUncertaintyDrop t ≤ t.understandingWork / t.bath.bathTemp.val ∧
  miPreserved miThreshold w

/-- Admissible semantic transition: satisfies the foundational invariant. -/
def admissibleSemanticTransition {n m : ℕ} (miThreshold : ℝ)
    (t : CommunicativeTransition n) (w : ProposalOutcomeWitness n m) : Prop :=
  semanticSecondLaw miThreshold t w

-- ================================================================
-- SECTION 3: Understanding cost (Landauer-linked reporting)
-- ================================================================

/-- Landauer-style understanding-cost floor [J] for `bits` of resolved uncertainty
    at semantic bath temperature `T`.  Same reporting functor as `coordinationSavingJoules`. -/
noncomputable def understandingCostFloorJoules (bits T : ℝ) : ℝ :=
  coordinationSavingJoules bits T

/-- Understanding cost for model-uncertainty drop expressed in bits. -/
noncomputable def understandingCostForDropJoules {n : ℕ} (t : CommunicativeTransition n) : ℝ :=
  understandingCostFloorJoules (modelUncertaintyDrop t / log 2) t.bath.bathTemp.val

/-- Semantic work meets the Landauer floor for the declared uncertainty drop. -/
def understandingCostAccounted {n : ℕ} (t : CommunicativeTransition n) : Prop :=
  understandingCostForDropJoules t ≤ t.understandingWork

-- ================================================================
-- SECTION 4: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

/-- Physical realization of a semantic transition: same bath, work, and
    entropy drop as a uniform-binary erasure process. -/
structure PhysicalSemanticBridge where
  proc : ErasureProcess
  transition : CommunicativeTransition 2
  bathEq : transition.bath = semanticBathOf proc.bath
  workEq : transition.understandingWork = proc.work
  priorEq : transition.prior = uniformBinary
  postEq : transition.post = diracDist (0 : Fin 2)

/-- When a communicative transition is physically realized, `physicalSecondLaw`
    implies the semantic entropy-accounting conjunct of `semanticSecondLaw`. -/
theorem semantic_entropy_bound_from_physical (b : PhysicalSemanticBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    modelUncertaintyDrop b.transition ≤
      b.transition.understandingWork / b.transition.bath.bathTemp.val := by
  have hdrop :
      modelUncertaintyDrop b.transition =
        shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2)) := by
    unfold modelUncertaintyDrop
    rw [b.priorEq, b.postEq]
  have hwork :
      b.transition.understandingWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    have hbval :
        b.transition.bath.bathTemp.val = b.proc.bath.bathTemp.val := by
      simpa [semanticBathOf] using
        congrArg Subtype.val (congrArg SemanticBath.bathTemp b.bathEq)
    rw [b.workEq, hbval]
  rw [hdrop, hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

/-- Landauer bound on understanding work for a physically bridged transition. -/
theorem understandingCostLandauerBound (b : PhysicalSemanticBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    b.transition.understandingWork ≥
      b.transition.bath.bathTemp.val * log 2 := by
  have hbath :
      b.transition.bath.bathTemp.val = b.proc.bath.bathTemp.val := by
    simpa [semanticBathOf] using
      congrArg Subtype.val (congrArg SemanticBath.bathTemp b.bathEq)
  have h := landauerBound b.proc hSL
  rw [b.workEq.symm] at h
  rw [hbath.symm] at h
  exact h

/-- Consistency is mandatory for admissibility. -/
theorem semanticConsistency_required {n m : ℕ} (miThreshold : ℝ)
    (t : CommunicativeTransition n) (w : ProposalOutcomeWitness n m)
    (h : admissibleSemanticTransition miThreshold t w) :
    structurallyConsistent t := h.1

/-- MI preservation is mandatory for admissibility. -/
theorem semanticMiPreservation_required {n m : ℕ} (miThreshold : ℝ)
    (t : CommunicativeTransition n) (w : ProposalOutcomeWitness n m)
    (h : admissibleSemanticTransition miThreshold t w) :
    miPreserved miThreshold w := h.2.2

/-- Entropy accounting is mandatory for admissibility. -/
theorem semanticEntropyAccounting_required {n m : ℕ} (miThreshold : ℝ)
    (t : CommunicativeTransition n) (w : ProposalOutcomeWitness n m)
    (h : admissibleSemanticTransition miThreshold t w) :
    modelUncertaintyDrop t ≤ t.understandingWork / t.bath.bathTemp.val := h.2.1

/-- Physically bridged + consistent + MI-witnessed transition satisfies
    `semanticSecondLaw` when entropy accounting is discharged. -/
theorem semanticSecondLaw_from_physical_bridge (miThreshold : ℝ)
    (b : PhysicalSemanticBridge) (w : ProposalOutcomeWitness 2 2)
    (hConsistent : structurallyConsistent b.transition)
    (hMI : miPreserved miThreshold w)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    semanticSecondLaw miThreshold b.transition w := by
  refine ⟨hConsistent, ?_, hMI⟩
  exact semantic_entropy_bound_from_physical b hSL

-- ================================================================
-- SECTION 5: Canonical fixtures (0 sorry — gate / catalog witnesses)
-- ================================================================

/-- Consistent, zero-cost P0 transition (degenerate admissible witness). -/
noncomputable def consistentP0Transition : CommunicativeTransition 2 where
  bath := { bathTemp := ⟨300, by norm_num⟩ }
  prior := uniformBinary
  post := uniformBinary
  understandingWork := 0
  consistencyDefect := 0

/-- Zero uncertainty drop ⇒ zero Landauer understanding floor. -/
theorem understandingCost_zero_drop (t : CommunicativeTransition 2)
    (hdrop : modelUncertaintyDrop t = 0) :
    understandingCostForDropJoules t = 0 := by
  unfold understandingCostForDropJoules understandingCostFloorJoules
  rw [hdrop, zero_div, coordinationSaving_zero]

theorem consistentP0_zero_uncertainty_drop :
    modelUncertaintyDrop consistentP0Transition = 0 := by
  unfold modelUncertaintyDrop consistentP0Transition
  ring

theorem consistentP0_structurallyConsistent :
    structurallyConsistent consistentP0Transition := rfl

/-- Product joint has zero MI — admissible only at threshold ≤ 0. -/
noncomputable def productWitness {n m : ℕ} (p : ProbDist n) (q : ProbDist m) :
    ProposalOutcomeWitness n m where
  joint := productJoint p q

theorem productWitness_mi_zero {n m : ℕ} (p : ProbDist n) (q : ProbDist m) :
    mutualInformation (productWitness p q).joint = 0 :=
  mutualInformation_product_zero p q

theorem productWitness_miPreserved_at_zero {n m : ℕ} (p : ProbDist n) (q : ProbDist m) :
    miPreserved 0 (productWitness p q) := by
  unfold miPreserved
  rw [productWitness_mi_zero p q]

/-- Catalog witness marker: foundational semantic invariant module is present. -/
theorem semantic_second_law_module_witness : True := trivial

end UMST.SemanticSecondLaw
