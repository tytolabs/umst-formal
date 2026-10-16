-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: AdaptiveSeamLensLaws.lean

  Laws L-A, L-D and L-I of the adaptive unfold hierarchy (`workspace/docs/blueprints/UMST_UNFOLD_ADAPTIVE_HIERARCHY.md`,
  section 12), as instances of the `.transition` case of `SecondLaw` and of the one inequality.

  * **L-A, transfer lens.** A restriction `R` from the fine to the coarse state and a prolongation `P` back, both
    additive, define the lens `get = R`, `put s v = (s − P (R s)) + P v`: the fine state keeps its component in
    `ker R` (the projection `Π = id − P R`) and takes the coarse update through `P`. GetPut holds for any `R`, `P`
    (`lens_getPut`); PutGet holds when `R P = id` (`lens_putGet`), and `Π` then lands in `ker R` (`proj_mem_ker`). The
    round trip `put s (get s)` is the identity, so the freeze of a fine state is the identity transition, which
    `SecondLaw` admits (`lens_roundTrip_secondLaw`, from `SecondLaw_transition_refl`).
  * **L-D, power-preserving seam.** Two subsystems at one bath, each satisfying the one inequality, joined by an
    interconnection whose port powers cancel (`W₁ + W₂ = 0`), form a composite with no supplied work that still
    satisfies it (`seam_oneInequality`, from `oneInequality_chain`): with no information term the composite free
    energy does not rise (`seam_creates_no_energy`); a composite whose free energy rises under a power-preserving
    seam without information breaks one subsystem's inequality (`seam_refused`).
  * **L-I, GENERIC degeneracy.** For `ż = L ∇E + M ∇S` with `L` antisymmetric, `M` symmetric positive semidefinite,
    `L ∇S = 0` and `M ∇E = 0`, the energy rate `∇E · ż` vanishes (`generic_energy_rate`) and the entropy rate
    `∇S · ż` is non-negative (`generic_entropy_rate_nonneg`). A step whose free energy falls by `T σ` with `σ ≥ 0`
    the entropy produced is the `.transition` case of `SecondLaw` through the passive route
    (`generic_step_secondLaw`).

  Zero `axiom`, zero `sorry`.
-/

import OneInequalitySecondLaw
import Convex.PassiveRoute
import Mathlib.Data.Matrix.Basic

open UMST.ProcessFamily UMST.Core UMST.Real UMST.LandauerLaw UMST.OneInequalitySecondLaw

namespace UMST.AdaptiveSeamLensLaws

section Lens

variable {S V : Type} [AddCommGroup S] [AddCommGroup V]

/-- The transfer lens of a restriction `R` and a prolongation `P`: `get = R`. -/
def lensGet (R : S →+ V) (s : S) : V := R s

/-- `put s v = (s − P (R s)) + P v`: the component of `s` in `ker R` is kept and the coarse update enters through `P`. -/
def lensPut (R : S →+ V) (P : V →+ S) (s : S) (v : V) : S := (s - P (R s)) + P v

/-- **L-A GetPut**: putting back what was got changes nothing. -/
theorem lens_getPut (R : S →+ V) (P : V →+ S) (s : S) : lensPut R P s (lensGet R s) = s := by
  simp [lensPut, lensGet]

/-- **L-A PutGet**: with `R P = id`, getting what was put returns it. -/
theorem lens_putGet (R : S →+ V) (P : V →+ S) (hRP : ∀ v, R (P v) = v) (s : S) (v : V) :
    lensGet R (lensPut R P s v) = v := by
  simp [lensPut, lensGet, map_add, map_sub, hRP]

/-- With `R P = id`, the projection `Π = id − P R` lands in `ker R`. -/
theorem proj_mem_ker (R : S →+ V) (P : V →+ S) (hRP : ∀ v, R (P v) = v) (s : S) : R (s - P (R s)) = 0 := by
  simp [map_sub, hRP]

/-- **L-A as a `SecondLaw` instance**: the round trip of a frozen fine state is the identity transition. -/
theorem lens_roundTrip_secondLaw (R : S →+ V) (P : V →+ S) (ρ : S → ℝ) (ψ : S → ℝ) (s : S) :
    SecondLaw .transition
      (.thermodynamic ⟨ρ s, ψ s⟩ ⟨ρ (lensPut R P s (lensGet R s)), ψ (lensPut R P s (lensGet R s))⟩) := by
  rw [lens_getPut]
  exact SecondLaw_transition_refl _

end Lens

section Seam

/-- **L-D**: two admissible subsystems at one bath joined by a power-preserving interconnection (`W₁ + W₂ = 0`)
    satisfy the one inequality with no supplied work. -/
theorem seam_oneInequality (s₁ s₂ : Step) (hT : s₁.bath.bathTemp.val = s₂.bath.bathTemp.val)
    (h₁ : oneInequality s₁) (h₂ : oneInequality s₂) (hseam : s₁.wIn + s₂.wIn = 0) :
    (s₁.chain s₂ hT).deltaF ≤ kB * s₁.bath.bathTemp.val * (s₁.infoI + s₂.infoI) := by
  have h := oneInequality_chain s₁ s₂ hT h₁ h₂
  simp only [oneInequality, Step.chain] at h ⊢
  linarith

/-- **L-D, no energy created**: without an information term the composite free energy does not rise. -/
theorem seam_creates_no_energy (s₁ s₂ : Step) (hT : s₁.bath.bathTemp.val = s₂.bath.bathTemp.val)
    (h₁ : oneInequality s₁) (h₂ : oneInequality s₂) (hseam : s₁.wIn + s₂.wIn = 0)
    (hI : s₁.infoI + s₂.infoI = 0) : (s₁.chain s₂ hT).deltaF ≤ 0 := by
  have h := seam_oneInequality s₁ s₂ hT h₁ h₂ hseam
  rw [hI, mul_zero] at h
  exact h

/-- **L-D refusal**: a composite whose free energy rises under a power-preserving seam without information breaks one
    subsystem's inequality. -/
theorem seam_refused (s₁ s₂ : Step) (hT : s₁.bath.bathTemp.val = s₂.bath.bathTemp.val)
    (hseam : s₁.wIn + s₂.wIn = 0) (hI : s₁.infoI + s₂.infoI = 0) (hrise : 0 < (s₁.chain s₂ hT).deltaF) :
    ¬ (oneInequality s₁ ∧ oneInequality s₂) :=
  fun ⟨h₁, h₂⟩ => absurd (seam_creates_no_energy s₁ s₂ hT h₁ h₂ hseam hI) (not_le.2 hrise)

end Seam

section Generic

open Matrix

variable {n : Type} [Fintype n] {α : Type} [LinearOrderedField α]

/-- An antisymmetric matrix gives a vanishing quadratic form. -/
theorem quad_antisymm_zero (L : Matrix n n α) (hL : Lᵀ = -L) (g : n → α) : g ⬝ᵥ (L *ᵥ g) = 0 := by
  have h : g ⬝ᵥ (L *ᵥ g) = -(g ⬝ᵥ (L *ᵥ g)) := by
    calc g ⬝ᵥ (L *ᵥ g) = (Lᵀ *ᵥ g) ⬝ᵥ g := by
          rw [dotProduct_mulVec, mulVec_transpose]
      _ = -(g ⬝ᵥ (L *ᵥ g)) := by
          rw [hL, neg_mulVec, neg_dotProduct, dotProduct_comm]
  linarith

/-- **L-I, energy conserved**: `∇E · (L ∇E + M ∇S) = 0` for `L` antisymmetric, `M` symmetric and `M ∇E = 0`. -/
theorem generic_energy_rate (L M : Matrix n n α) (hL : Lᵀ = -L) (hM : Mᵀ = M) (gE gS : n → α)
    (hME : M *ᵥ gE = 0) : gE ⬝ᵥ (L *ᵥ gE + M *ᵥ gS) = 0 := by
  rw [dotProduct_add, quad_antisymm_zero L hL gE, zero_add, dotProduct_mulVec, ← hM, vecMul_transpose, hME,
    zero_dotProduct]

/-- **L-I, entropy produced**: `∇S · (L ∇E + M ∇S) ≥ 0` for `L` antisymmetric, `L ∇S = 0` and `M` positive
    semidefinite. -/
theorem generic_entropy_rate_nonneg (L M : Matrix n n α) (hL : Lᵀ = -L) (gE gS : n → α) (hLS : L *ᵥ gS = 0)
    (hMpsd : ∀ x : n → α, 0 ≤ x ⬝ᵥ (M *ᵥ x)) : 0 ≤ gS ⬝ᵥ (L *ᵥ gE + M *ᵥ gS) := by
  have h0 : gS ⬝ᵥ (L *ᵥ gE) = 0 := by
    have hL' : L = -Lᵀ := by rw [hL, neg_neg]
    rw [dotProduct_mulVec, hL', vecMul_neg, vecMul_transpose, hLS, neg_zero, zero_dotProduct]
  rw [dotProduct_add, h0, zero_add]
  exact hMpsd gS

end Generic

/-- **L-I as a `SecondLaw` instance**: a thermal-seam step at temperature `T > 0` whose free energy falls by `T σ`,
    with `σ ≥ 0` the entropy produced, is the `.transition` case through the passive route. -/
theorem generic_step_secondLaw {ρ ρ' ψ T σ : ℝ} (hT : 0 < T) (hσ : 0 ≤ σ)
    (hm : CoreMassCond ℝ RealThermodynamicState ⟨ρ, ψ⟩ ⟨ρ', ψ - T * σ⟩) :
    SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - T * σ⟩) :=
  UMST.Convex.PassiveRoute.passive_inequality_secondLaw hm (mul_nonneg hT.le hσ) (by dsimp only; linarith)

end UMST.AdaptiveSeamLensLaws
