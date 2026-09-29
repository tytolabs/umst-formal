-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  C-CONVEX-1 (W-32): `ConvexPhiDissipation` — convex φ, φ ≥ 0, φ(0) = 0 ⇒ non-negative dissipation;
  passive `SecondLaw` case for any GSM cartridge.

  Zero new Lean axioms; `physics_green` stays false (typed scaffold, not measured physics).
-/

import Process

import Mathlib.Analysis.Convex.Deriv

open Real Set UMST.ProcessFamily UMST.Core UMST.Real

local notation "SecondLawₚ" => UMST.ProcessFamily.SecondLaw

namespace UMST.ConvexPhiDissipation

/-- Scalar-rate GSM dissipation hypotheses (convex, nonnegative, pinned at zero). -/
structure GsmDissipationPotential where
  φ : ℝ → ℝ
  convex : ConvexOn ℝ univ φ
  nonneg : ∀ sDot, 0 ≤ φ sDot
  zero : φ 0 = 0
  diff : Differentiable ℝ φ

/-- Thermodynamic power paired with the rate derivative (1D rate channel). -/
noncomputable def dissipationPower (P : GsmDissipationPotential) (sDot : ℝ) : ℝ :=
  sDot * deriv P.φ sDot

/-- Convex subgradient inequality: φ(ṡ) ≤ ṡ · ∂φ/∂ṡ. -/
theorem convex_phi_le_dissipationPower (P : GsmDissipationPotential) (sDot : ℝ) :
    P.φ sDot ≤ dissipationPower P sDot := by
  dsimp [dissipationPower]
  rcases lt_trichotomy sDot 0 with hneg | rfl | hpos
  · have hsDot : sDot ∈ univ := mem_univ _
    have h0 : (0 : ℝ) ∈ univ := mem_univ _
    have hφ0 : P.φ 0 = 0 := P.zero
    have hle := P.convex.deriv_le_slope (hx := hsDot) (hy := h0) (hxy := hneg)
      (Differentiable.differentiableAt P.diff)
    dsimp [slope] at hle
    rw [hφ0] at hle
    field_simp at hle
    simpa [mul_comm] using (le_div_iff_of_neg hneg).1 hle
  · simp [P.zero, dissipationPower, mul_zero]
  · have hsDot : sDot ∈ univ := mem_univ _
    have h0 : (0 : ℝ) ∈ univ := mem_univ _
    have hφ0 : P.φ 0 = 0 := P.zero
    have hle := P.convex.slope_le_deriv (hx := h0) (hy := hsDot) hpos
      (Differentiable.differentiableAt P.diff)
    dsimp [slope] at hle
    rw [hφ0, sub_zero] at hle
    field_simp at hle
    simpa [mul_comm] using (div_le_iff₀ hpos).1 hle

/-- **Non-negative dissipation** from convex φ ≥ 0 with φ(0) = 0. -/
theorem convex_phi_dissipation_nonneg (P : GsmDissipationPotential) (sDot : ℝ) :
    0 ≤ dissipationPower P sDot :=
  le_trans (P.nonneg sDot) (convex_phi_le_dissipationPower P sDot)

/-- Alias aligned with cartridge doc wording. -/
theorem convex_phi_nonneg_dissipation (P : GsmDissipationPotential) (sDot : ℝ) :
    0 ≤ dissipationPower P sDot :=
  convex_phi_dissipation_nonneg P sDot

/-- A GSM cartridge packages a dissipation potential obeying the convex passive pin. -/
structure GsmCartridge where
  dissip : GsmDissipationPotential

/-- Passive transition data: free-energy descent within the core mass budget. -/
structure PassiveGsmTransition (old new : RealThermodynamicState) : Prop where
  mass : CoreMassCond ℝ RealThermodynamicState old new
  freeEnergyDescent : new.freeEnergy ≤ old.freeEnergy

/-- **Passive SecondLaw** for any GSM cartridge: Clausius–Duhem + mass edge ⇒ `SecondLawₚ`. -/
theorem gsmCartridge_passive_secondLaw (_C : GsmCartridge) {old new : RealThermodynamicState}
    (h : PassiveGsmTransition old new) :
    SecondLawₚ .transition (.thermodynamic old new) := by
  rcases h with ⟨hm, hd⟩
  exact ⟨hm, hd⟩

theorem gsmCartridge_passive_secondLaw_of_descent (_C : GsmCartridge)
    {old new : RealThermodynamicState}
    (hm : CoreMassCond ℝ RealThermodynamicState old new)
    (hd : new.freeEnergy ≤ old.freeEnergy) :
    SecondLawₚ .transition (.thermodynamic old new) :=
  gsmCartridge_passive_secondLaw _C ⟨hm, hd⟩

/-- Local dissipation nonnegativity available for every GSM cartridge at any rate. -/
theorem gsmCartridge_dissipation_nonneg (C : GsmCartridge) (sDot : ℝ) :
    0 ≤ dissipationPower C.dissip sDot :=
  convex_phi_dissipation_nonneg C.dissip sDot

def convexPhiDissipationCellId : String := "C-CONVEX-1"

def convexPhiDissipationPhysicsGreen : Bool := false

theorem convexPhiDissipationPhysicsGreen_false : convexPhiDissipationPhysicsGreen = false := rfl

end UMST.ConvexPhiDissipation
