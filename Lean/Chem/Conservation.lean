-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/Conservation.lean

  Meso acting chemistry — linear/affine conservation lift for chemical assemblages.
  Conservation axes are **typed closures** under the sole axiom stack anchored in
  `LandauerLaw.physicalSecondLaw` via `Chem.SecondLaw`.  Adds **zero** Lean `axiom`
  declarations.

  Fiber: meso/acting → `umst-formal` only.  No quantum theorems.
-/

import Chem.SecondLaw

open Real Finset UMST.LandauerLaw UMST.Chem.SecondLaw

namespace UMST.Chem.Conservation

-- ================================================================
-- SECTION 1: Conservation resource axes (linear vs affine)
-- ================================================================

/-- Conservation axes for chemical assemblages (design scaffold — not SpeciesId). -/
inductive ConservationAxis where
  | Mass
  | Charge
  | AtomCount
  | Enthalpy
  deriving DecidableEq, Repr

/-- Species composition vector (macroscopic bookkeeping units). -/
abbrev Composition (n : ℕ) := Fin n → ℝ

/-- Composition change between prior and post assemblage states. -/
def compositionDelta {n : ℕ} (prior post : Composition n) : Fin n → ℝ :=
  fun i => post i - prior i

/-- Linear conservation closure: stoichiometric coefficients balance the delta. -/
def linearConservationClosed {n : ℕ} (coeff : Fin n → ℤ) (delta : Fin n → ℝ) : Prop :=
  (∑ i, (coeff i : ℝ) * delta i) = 0

/-- Linear conservation witness for one axis. -/
structure LinearConservationWitness (n : ℕ) where
  coeff : Fin n → ℤ

/-- Witness certifies linear closure on a composition delta. -/
def linearWitnessClosed {n : ℕ} (w : LinearConservationWitness n)
    (delta : Fin n → ℝ) : Prop :=
  linearConservationClosed w.coeff delta

/-- Affine conservation witness: linear closure plus nonnegative slack
    discharged only with dissipative work under the second law. -/
structure AffineConservationWitness (n : ℕ) where
  coeff : Fin n → ℤ
  slack : ℝ
  slack_nonneg : 0 ≤ slack

/-- Affine closure: linear balance with recorded slack (weakening axis). -/
def affineConservationClosed {n : ℕ} (w : AffineConservationWitness n)
    (delta : Fin n → ℝ) : Prop :=
  (∑ i, (w.coeff i : ℝ) * delta i) + w.slack = 0

/-- Dissipative witness for affine slack: slack · T ≤ dissipated work. -/
def affineDissipativeWitness (w : AffineConservationWitness n) (T dissipatedWork : ℝ) :
    Prop :=
  w.slack * T ≤ dissipatedWork

/-- Full affine conservation accounting (closure + dissipative witness). -/
def affineConservationAccounted {n : ℕ} (w : AffineConservationWitness n)
    (delta : Fin n → ℝ) (T dissipatedWork : ℝ) : Prop :=
  affineConservationClosed w delta ∧ affineDissipativeWitness w T dissipatedWork

-- ================================================================
-- SECTION 2: Chem transition with conservation + second law
-- ================================================================

/-- Thermochemical transition bundled with prior/post compositions. -/
structure ConservedChemTransition (n : ℕ) where
  thermo : ThermochemicalTransition n
  priorComp : Composition n
  postComp : Composition n

/-- Composition delta for a conserved transition. -/
def conservedCompositionDelta {n : ℕ} (t : ConservedChemTransition n) : Fin n → ℝ :=
  compositionDelta t.priorComp t.postComp

/-- Linear conservation preserved on a conserved transition. -/
def linearConservationPreserved {n : ℕ} (w : LinearConservationWitness n)
    (t : ConservedChemTransition n) : Prop :=
  linearWitnessClosed w (conservedCompositionDelta t)

/-- Admissible conserved transition: second law + linear conservation witness. -/
def admissibleConservedTransition {n : ℕ} (w : LinearConservationWitness n)
    (t : ConservedChemTransition n) : Prop :=
  admissibleThermochemicalTransition t.thermo ∧
  linearConservationPreserved w t

-- ================================================================
-- SECTION 3: Derived lemmas (zero new axioms)
-- ================================================================

/-- Linear witness closure is definitional on zero delta. -/
theorem linearConservation_zero_delta {n : ℕ} (w : LinearConservationWitness n) :
    linearWitnessClosed w (fun _ => 0) := by
  unfold linearWitnessClosed linearConservationClosed
  simp

/-- Affine witness with zero slack reduces to linear closure. -/
theorem affine_zero_slack_linear {n : ℕ} (w : AffineConservationWitness n)
    (hslack : w.slack = 0) (delta : Fin n → ℝ) :
    affineConservationClosed w delta ↔ linearConservationClosed w.coeff delta := by
  unfold affineConservationClosed linearConservationClosed
  simpa [hslack] using (Eq.symm zero_add)

/-- When slack is zero, dissipative witness holds for any nonnegative work at T ≥ 0. -/
theorem affineDissipative_zero_slack {n : ℕ} (w : AffineConservationWitness n)
    (hslack : w.slack = 0) (T dissipatedWork : ℝ) (_hT : 0 ≤ T) (_hW : 0 ≤ dissipatedWork) :
    affineDissipativeWitness w T dissipatedWork := by
  unfold affineDissipativeWitness
  rw [hslack, zero_mul]
  linarith

/-- Physical bridge + linear witness ⇒ admissible conserved transition at zero composition delta. -/
theorem admissible_from_physical_bridge (b : PhysicalChemBridge)
    (w : LinearConservationWitness 2)
    (hDelta : conservedCompositionDelta ⟨b.transition, fun _ => 0, fun _ => 0⟩ = fun _ => 0)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleConservedTransition w ⟨b.transition, fun _ => 0, fun _ => 0⟩ := by
  refine ⟨chemSecondLaw_from_physical b hSL, ?_⟩
  unfold linearConservationPreserved linearWitnessClosed conservedCompositionDelta at *
  rw [hDelta]
  exact linearConservation_zero_delta w

/-- Second law is mandatory for admissible conserved transitions. -/
theorem conserved_second_law_required {n : ℕ} (w : LinearConservationWitness n)
    (t : ConservedChemTransition n)
    (h : admissibleConservedTransition w t) :
    chemSecondLaw t.thermo := h.1

/-- Linear conservation is mandatory for admissible conserved transitions. -/
theorem conserved_linear_required {n : ℕ} (w : LinearConservationWitness n)
    (t : ConservedChemTransition n)
    (h : admissibleConservedTransition w t) :
    linearConservationPreserved w t := h.2

/-- Affine accounting with zero slack inherits physical second-law entropy bound. -/
theorem affine_entropy_from_physical (b : PhysicalChemBridge)
    (w : AffineConservationWitness 2) (hslack : w.slack = 0)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    affineDissipativeWitness w b.transition.bath.bathTemp.val b.transition.dissipatedWork := by
  have hbath :
      b.transition.bath.bathTemp.val = b.proc.bath.bathTemp.val := by
    simpa [chemHeatBathOf] using
      congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  have hT : 0 < b.transition.bath.bathTemp.val := by rw [hbath]; exact b.proc.bath.bathTemp.property
  have hW : 0 < b.transition.dissipatedWork := by rw [b.workEq]; exact landauerBound_pos b.proc hSL
  exact affineDissipative_zero_slack w hslack _ _ (le_of_lt hT) (le_of_lt hW)

/-- Catalog witness: meso chemistry conservation module is present. -/
theorem chem_conservation_module_witness : True := trivial

end UMST.Chem.Conservation
