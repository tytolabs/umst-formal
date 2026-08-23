-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/RefineCost.lean

  Meso acting chemistry — **Refine** as a costly morphism under the second-law +
  conservation spine (`Chem.SecondLaw` + `Chem.Conservation`).  **Contamination**
  is the reverse Refine morphism (endpoint swap — not a parallel chemistry axiom).

  Adds **zero** Lean `axiom` declarations.

  Fiber: meso/acting → `umst-formal` only.  No quantum theorems.
-/

import Chem.Conservation
import Chem.SecondLaw

open Real Finset UMST.LandauerLaw UMST.Chem.SecondLaw UMST.Chem.Conservation

namespace UMST.Chem.RefineCost

-- ================================================================
-- SECTION 1: Refine grade carriers (acting meso layer)
-- ================================================================

/-- L0 refine-grade family tags (scaffold — not bare purity floats). -/
inductive RefineGrade where
  | Feedstock
  | Concentrate
  | TailingsContaminated
  deriving DecidableEq, Repr

/-- Canonical feedstock grade (pre-refinement). -/
def feedstockGrade : RefineGrade := .Feedstock

/-- Canonical concentrate grade (post-refinement). -/
def concentrateGrade : RefineGrade := .Concentrate

/-- Canonical contaminated tailings grade (messy reverse endpoint). -/
def tailingsGrade : RefineGrade := .TailingsContaminated

/-- Refine is directed upgrade: feedstock → concentrate (structure only). -/
def canonicalRefineDirection (src tgt : RefineGrade) : Prop :=
  src = .Feedstock ∧ tgt = .Concentrate

/-- Contamination is directed downgrade: concentrate → tailings (reverse Refine). -/
def canonicalContaminationDirection (src tgt : RefineGrade) : Prop :=
  src = .Concentrate ∧ tgt = .TailingsContaminated

-- ================================================================
-- SECTION 2: Costly refine morphism (second law + conservation)
-- ================================================================

/-- A costly refine morphism: source/target grades bundled with a conserved
    thermochemical transition and explicit dissipated-work accounting. -/
structure RefineMorphism (n : ℕ) where
  source : RefineGrade
  target : RefineGrade
  transition : ConservedChemTransition n
  cost : ℝ
  cost_eq_work : cost = transition.thermo.dissipatedWork

/-- Dissipated work recorded on the morphism equals the thermochemical leg. -/
theorem refineMorphism_cost_work {n : ℕ} (m : RefineMorphism n) :
    m.cost = m.transition.thermo.dissipatedWork :=
  m.cost_eq_work

/-- Second-law admissibility on the thermochemical leg of a refine morphism. -/
def refineSecondLawAdmissible {n : ℕ} (m : RefineMorphism n) : Prop :=
  chemSecondLaw m.transition.thermo

/-- Landauer-style refinement work floor accounted on the thermochemical leg. -/
def refineWorkAccounted {n : ℕ} (m : RefineMorphism n) : Prop :=
  refinementWorkAccounted m.transition.thermo

/-- Linear conservation preserved on the thermochemical leg. -/
def refineLinearConservationPreserved {n : ℕ} (w : LinearConservationWitness n)
    (m : RefineMorphism n) : Prop :=
  linearConservationPreserved w m.transition

/-- Full admissibility: second law + linear conservation witness. -/
def admissibleRefineMorphism {n : ℕ} (w : LinearConservationWitness n)
    (m : RefineMorphism n) : Prop :=
  admissibleConservedTransition w m.transition

/-- Admissible refine morphisms satisfy the chemical second law. -/
theorem admissibleRefine_secondLaw {n : ℕ} (w : LinearConservationWitness n)
    (m : RefineMorphism n) (h : admissibleRefineMorphism w m) :
    refineSecondLawAdmissible m :=
  h.1

/-- Admissible refine morphisms satisfy linear conservation. -/
theorem admissibleRefine_linearConservation {n : ℕ} (w : LinearConservationWitness n)
    (m : RefineMorphism n) (h : admissibleRefineMorphism w m) :
    refineLinearConservationPreserved w m :=
  h.2

-- ================================================================
-- SECTION 3: Contamination = reverse Refine (endpoint swap)
-- ================================================================

/-- Reverse a refine morphism: contamination is **not** a third chemistry law —
    it reuses the thermochemical leg with swapped grade endpoints. -/
def reverseRefineMorphism {n : ℕ} (m : RefineMorphism n) : RefineMorphism n where
  source := m.target
  target := m.source
  transition := m.transition
  cost := m.cost
  cost_eq_work := m.cost_eq_work

/-- Alias: contamination morphism is reverse Refine. -/
def contaminationMorphism {n : ℕ} (m : RefineMorphism n) : RefineMorphism n :=
  reverseRefineMorphism m

/-- Contamination reverses refine grade endpoints. -/
theorem contamination_reverses_endpoints {n : ℕ} (m : RefineMorphism n) :
    (contaminationMorphism m).source = m.target ∧
    (contaminationMorphism m).target = m.source :=
  ⟨rfl, rfl⟩

/-- Double reverse restores grade endpoints. -/
theorem reverseRefine_involutive_grades {n : ℕ} (m : RefineMorphism n) :
    (reverseRefineMorphism (reverseRefineMorphism m)).source = m.source ∧
    (reverseRefineMorphism (reverseRefineMorphism m)).target = m.target :=
  ⟨rfl, rfl⟩

/-- Contamination preserves second-law admissibility of the shared thermochemical leg. -/
theorem contamination_preserves_secondLaw {n : ℕ} (m : RefineMorphism n)
    (h : refineSecondLawAdmissible m) :
    refineSecondLawAdmissible (contaminationMorphism m) :=
  h

/-- Contamination preserves linear conservation on the shared thermochemical leg. -/
theorem contamination_preserves_linearConservation {n : ℕ}
    (w : LinearConservationWitness n) (m : RefineMorphism n)
    (h : refineLinearConservationPreserved w m) :
    refineLinearConservationPreserved w (contaminationMorphism m) :=
  h

/-- Admissible refine ⇒ admissible contamination (reverse morphism). -/
theorem admissibleContamination_of_admissibleRefine {n : ℕ}
    (w : LinearConservationWitness n) (m : RefineMorphism n)
    (h : admissibleRefineMorphism w m) :
    admissibleRefineMorphism w (contaminationMorphism m) :=
  ⟨h.1, h.2⟩

-- ================================================================
-- SECTION 4: Physical bridge (zero new axioms)
-- ================================================================

/-- Physical bridge yields an admissible refine morphism at zero composition delta. -/
theorem admissibleRefine_from_physical_bridge (b : PhysicalChemBridge)
    (w : LinearConservationWitness 2)
    (src tgt : RefineGrade)
    (hDelta : conservedCompositionDelta ⟨b.transition, fun _ => 0, fun _ => 0⟩ = fun _ => 0)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleRefineMorphism w
      { source := src
        target := tgt
        transition := ⟨b.transition, fun _ => 0, fun _ => 0⟩
        cost := b.transition.dissipatedWork
        cost_eq_work := rfl } :=
  admissible_from_physical_bridge b w hDelta hSL

/-- Physical bridge discharges refine second-law admissibility. -/
theorem refineSecondLaw_from_physical (b : PhysicalChemBridge)
    (src tgt : RefineGrade)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    refineSecondLawAdmissible
      { source := src
        target := tgt
        transition := ⟨b.transition, fun _ => 0, fun _ => 0⟩
        cost := b.transition.dissipatedWork
        cost_eq_work := rfl } :=
  chemSecondLaw_from_physical b hSL

/-- Physical bridge discharges refinement work accounting. -/
theorem refineWorkAccounted_from_physical (b : PhysicalChemBridge)
    (src tgt : RefineGrade)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    refineWorkAccounted
      { source := src
        target := tgt
        transition := ⟨b.transition, fun _ => 0, fun _ => 0⟩
        cost := b.transition.dissipatedWork
        cost_eq_work := rfl } := by
  unfold refineWorkAccounted refinementWorkAccounted refinementWorkFloor
  have hdrop : assemblageEntropyDrop b.transition = log 2 := by
    unfold assemblageEntropyDrop
    rw [b.priorEq, b.postEq]
    exact binaryErasureEntropyDrop
  rw [hdrop]
  exact refinementLandauerBound b hSL

-- ================================================================
-- SECTION 5: Canonical fixtures + honesty posture
-- ================================================================

/-- Coherent P0 refine morphism at zero cost (catalog witness). -/
noncomputable def coherentP0RefineMorphism : RefineMorphism 2 where
  source := feedstockGrade
  target := concentrateGrade
  transition :=
    { thermo := coherentP0Transition
      priorComp := fun _ => 0
      postComp := fun _ => 0 }
  cost := 0
  cost_eq_work := rfl

theorem coherentP0Refine_secondLaw : refineSecondLawAdmissible coherentP0RefineMorphism :=
  coherentP0_chemSecondLaw

theorem coherentP0Refine_workAccounted : refineWorkAccounted coherentP0RefineMorphism := by
  unfold refineWorkAccounted refinementWorkAccounted refinementWorkFloor coherentP0RefineMorphism
  rw [coherentP0_zero_entropy_drop]
  simp only [coherentP0Transition]
  norm_num

/-- Coherent P0 contamination is reverse refine at zero cost. -/
noncomputable def coherentP0Contamination : RefineMorphism 2 :=
  reverseRefineMorphism coherentP0RefineMorphism

theorem coherentP0Contamination_is_reverse :
    coherentP0Contamination = reverseRefineMorphism coherentP0RefineMorphism :=
  rfl

theorem coherentP0Contamination_endpoints :
    coherentP0Contamination.source = concentrateGrade ∧
    coherentP0Contamination.target = feedstockGrade := by
  unfold coherentP0Contamination reverseRefineMorphism coherentP0RefineMorphism
  exact ⟨rfl, rfl⟩

theorem canonicalRefine_fixture : canonicalRefineDirection feedstockGrade concentrateGrade := by
  exact ⟨rfl, rfl⟩

theorem canonicalContamination_fixture :
    canonicalContaminationDirection concentrateGrade tailingsGrade := by
  exact ⟨rfl, rfl⟩

/-- Physics GREEN unauthorized on this scaffold. -/
def refinePhysicsGreen : Bool := false

theorem refinePhysicsGreenFalse : refinePhysicsGreen = false := rfl

/-- Production wiring stays open (REFINE-00 / CAT-01 lift only). -/
def refineCostProductionWired : Bool := false

theorem refineCostProductionWiredFalse : refineCostProductionWired = false := rfl

/-- Catalog witness: meso chemistry refine-cost module present. -/
theorem refineCostModuleWitness : True := trivial

end UMST.Chem.RefineCost
