-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Constants/SecondLawElastic.lean

  Elastic moduli bounded by the second law. A linear-elastic body loaded away from its natural (unstrained)
  state stores free energy; released, it relaxes passively to the natural state, whose free energy is zero. Each
  theorem takes that relaxation as a `.transition` case of `UMST.ProcessFamily.SecondLaw` (free energy does not
  rise) and concludes a bound on a modulus. The hypothesis is quantified over every loaded state where the bound
  needs several loading modes.

  * `relaxation_stiffness_nonneg`: a mode storing ½·k·s² (strain s ≠ 0) has k ≥ 0.
  * `relaxation_modulus_pos`: a body held at stress σ ≠ 0 by a modulus E ≠ 0 stores σ²/(2E) (uniaxial stress for
    Young's modulus, pure shear for the shear modulus); the relaxation forces E > 0.
  * `twoMode_stiffness_nonneg`: two independent quadratic modes ½·a·x² + ½·b·y² relaxing from every (x, y) give
    a ≥ 0 and b ≥ 0.
  * `isotropic_poisson_bounds`, `isotropic_young_nonneg`: an isotropic solid stores ½·K·e² + ½·G·γ² in a
    volumetric strain e and an engineering shear γ; with 3K + G > 0 the Poisson ratio
    ν = (3K − 2G)/(2(3K + G)) lies in [−1, 1/2] and Young's modulus E = 9KG/(3K + G) is nonnegative.
  * `sls_relaxed_le_instantaneous`: a standard linear solid stores ½·G∞·ε² + ½·G₁·ξ² (ξ the Maxwell arm's elastic
    strain); its relaxed modulus satisfies 0 ≤ G∞ ≤ G∞ + G₁ = G₀, the instantaneous modulus.
  * `orthotropic_poisson_sq_le`: an orthotropic lamina in plane stress stores
    σ₁²/(2E₁) − ν₁₂·σ₁·σ₂/E₁ + σ₂²/(2E₂); relaxation from every stress state forces E₁ > 0, E₂ > 0 and
    ν₁₂² ≤ E₁/E₂.

  Each result is a bound, never a value: the law fixes the sign or the interval, and the registry value is a
  measurement or a citation inside it. Zero Lean axioms; physics enters only as the `SecondLaw` hypothesis.
-/

import Process

open UMST.ProcessFamily UMST.Real

namespace UMST.Constants.SecondLawElastic

/-- **Stiffness**: a mode storing ½·k·s² at a strain `s ≠ 0` that relaxes passively has `k ≥ 0`. -/
theorem relaxation_stiffness_nonneg {ρ ρ' k s : ℝ} (hs : s ≠ 0)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * k * s ^ 2⟩ ⟨ρ', 0⟩)) : 0 ≤ k := by
  have h0 : (0 : ℝ) ≤ 1 / 2 * k * s ^ 2 := h.2
  have hs2 : 0 < s ^ 2 := by positivity
  by_contra hk
  push_neg at hk
  nlinarith

/-- **Modulus**: a body held at stress `σ ≠ 0` by a modulus `E ≠ 0` stores σ²/(2E); its passive relaxation
    forces `E > 0`. -/
theorem relaxation_modulus_pos {ρ ρ' E σ : ℝ} (hσ : σ ≠ 0) (hE : E ≠ 0)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, σ ^ 2 / (2 * E)⟩ ⟨ρ', 0⟩)) : 0 < E := by
  have h0 : (0 : ℝ) ≤ σ ^ 2 / (2 * E) := h.2
  rcases lt_or_gt_of_ne hE with hneg | hpos
  · have : σ ^ 2 / (2 * E) < 0 := div_neg_of_pos_of_neg (by positivity) (by linarith)
    linarith
  · exact hpos

/-- **Two modes**: ½·a·x² + ½·b·y² relaxing passively from every `(x, y)` gives `a ≥ 0` and `b ≥ 0`. -/
theorem twoMode_stiffness_nonneg {ρ ρ' a b : ℝ}
    (h : ∀ x y : ℝ, SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * a * x ^ 2 + 1 / 2 * b * y ^ 2⟩ ⟨ρ', 0⟩)) :
    0 ≤ a ∧ 0 ≤ b := by
  have ha : (0 : ℝ) ≤ 1 / 2 * a * 1 ^ 2 + 1 / 2 * b * 0 ^ 2 := (h 1 0).2
  have hb : (0 : ℝ) ≤ 1 / 2 * a * 0 ^ 2 + 1 / 2 * b * 1 ^ 2 := (h 0 1).2
  constructor <;> nlinarith

/-- Poisson ratio of an isotropic solid from its bulk modulus `K` and shear modulus `G`. -/
noncomputable def poissonRatio (K G : ℝ) : ℝ := (3 * K - 2 * G) / (2 * (3 * K + G))

/-- Young's modulus of an isotropic solid from its bulk modulus `K` and shear modulus `G`. -/
noncomputable def youngModulus (K G : ℝ) : ℝ := 9 * K * G / (3 * K + G)

/-- **Poisson ratio**: an isotropic solid storing ½·K·e² + ½·G·γ² that relaxes passively from every volumetric
    strain `e` and shear `γ`, with `3K + G > 0`, has `−1 ≤ ν ≤ 1/2`. -/
theorem isotropic_poisson_bounds {ρ ρ' K G : ℝ} (hpos : 0 < 3 * K + G)
    (h : ∀ e γ : ℝ, SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * K * e ^ 2 + 1 / 2 * G * γ ^ 2⟩ ⟨ρ', 0⟩)) :
    -1 ≤ poissonRatio K G ∧ poissonRatio K G ≤ 1 / 2 := by
  obtain ⟨hK, hG⟩ := twoMode_stiffness_nonneg h
  have hd : 0 < 2 * (3 * K + G) := by linarith
  unfold poissonRatio
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

/-- **Young's modulus**: under the same relaxation, `E = 9KG/(3K + G) ≥ 0`. -/
theorem isotropic_young_nonneg {ρ ρ' K G : ℝ} (hpos : 0 < 3 * K + G)
    (h : ∀ e γ : ℝ, SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * K * e ^ 2 + 1 / 2 * G * γ ^ 2⟩ ⟨ρ', 0⟩)) :
    0 ≤ youngModulus K G := by
  obtain ⟨hK, hG⟩ := twoMode_stiffness_nonneg h
  unfold youngModulus
  exact div_nonneg (by positivity) hpos.le

/-- **Standard linear solid**: storing ½·G∞·ε² + ½·G₁·ξ² and relaxing passively from every total strain `ε` and
    arm strain `ξ`, the relaxed modulus satisfies `0 ≤ G∞ ≤ G∞ + G₁`, the instantaneous modulus. -/
theorem sls_relaxed_le_instantaneous {ρ ρ' Ginf G1 : ℝ}
    (h : ∀ ε ξ : ℝ,
      SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * Ginf * ε ^ 2 + 1 / 2 * G1 * ξ ^ 2⟩ ⟨ρ', 0⟩)) :
    0 ≤ Ginf ∧ Ginf ≤ Ginf + G1 := by
  obtain ⟨hinf, h1⟩ := twoMode_stiffness_nonneg h
  exact ⟨hinf, by linarith⟩

/-- Plane-stress free energy of an orthotropic lamina at stresses `σ₁`, `σ₂` in its material axes. -/
noncomputable def orthotropicEnergy (E1 E2 ν12 σ1 σ2 : ℝ) : ℝ :=
  σ1 ^ 2 / (2 * E1) - ν12 * σ1 * σ2 / E1 + σ2 ^ 2 / (2 * E2)

/-- **Orthotropic Poisson ratio**: a lamina with nonzero moduli that relaxes passively from every plane stress
    state has `E₁ > 0`, `E₂ > 0` and `ν₁₂² ≤ E₁/E₂`. -/
theorem orthotropic_poisson_sq_le {ρ ρ' E1 E2 ν12 : ℝ} (hE1 : E1 ≠ 0) (hE2 : E2 ≠ 0)
    (h : ∀ σ1 σ2 : ℝ, SecondLaw .transition (.thermodynamic ⟨ρ, orthotropicEnergy E1 E2 ν12 σ1 σ2⟩ ⟨ρ', 0⟩)) :
    0 < E1 ∧ 0 < E2 ∧ ν12 ^ 2 ≤ E1 / E2 := by
  have p1 : 0 < E1 := relaxation_modulus_pos (σ := 1) one_ne_zero hE1 (by
    refine ⟨(h 1 0).1, ?_⟩
    have h10 : (0 : ℝ) ≤ orthotropicEnergy E1 E2 ν12 1 0 := (h 1 0).2
    show (0 : ℝ) ≤ 1 ^ 2 / (2 * E1)
    simpa [orthotropicEnergy] using h10)
  have p2 : 0 < E2 := relaxation_modulus_pos (σ := 1) one_ne_zero hE2 (by
    refine ⟨(h 0 1).1, ?_⟩
    have h01 : (0 : ℝ) ≤ orthotropicEnergy E1 E2 ν12 0 1 := (h 0 1).2
    show (0 : ℝ) ≤ 1 ^ 2 / (2 * E2)
    simpa [orthotropicEnergy] using h01)
  refine ⟨p1, p2, ?_⟩
  have hν : (0 : ℝ) ≤ orthotropicEnergy E1 E2 ν12 ν12 1 := (h ν12 1).2
  have key : ν12 ^ 2 / E1 ≤ 1 / E2 := by
    have e : orthotropicEnergy E1 E2 ν12 ν12 1 = (1 / E2 - ν12 ^ 2 / E1) / 2 := by
      unfold orthotropicEnergy
      field_simp
      ring
    rw [e] at hν
    linarith
  rw [div_le_div_iff₀ p1 p2] at key
  rw [le_div_iff₀ p2]
  linarith

end UMST.Constants.SecondLawElastic
