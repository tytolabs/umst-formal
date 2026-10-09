-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Constants/SecondLawSolidInelastic.lean

  Material parameters of an inelastic solid (plasticity with hardening, phase-field fracture, creep, oxidation, fibre
  pull-out) bounded by the second law. Each hypothesis is a `.transition` case of `UMST.ProcessFamily.SecondLaw`:
  either the passive relaxation of a loaded state to its natural state (free energy zero), or a passive step whose
  dissipated energy leaves the free energy (`Constants.SecondLawDissipation`).

  * `coupledWell_bounds`: a plastic strain x and a hardening variable y storing ½·k·(x² + y² + 2c·x·y), relaxing
    from every (x, y), with k ≠ 0, have k > 0 and −1 ≤ c ≤ 1.
  * `doubleWell_modulus_nonneg`: a phase field φ ∉ {0, 1} storing k·φ²·(1 − φ)² and relaxing has k ≥ 0.
  * `griffith_fracture_energy_nonneg`: a crack extension ΔA > 0 dissipates G_c·ΔA; the second law gives G_c ≥ 0.
  * `griffith_toughness_nonneg`: with G_c ≥ 0 from a crack extension and E > 0 from an elastic relaxation, the
    toughness K = √(E·G_c) is nonnegative and K² = E·G_c.
  * `norton_coefficient_nonneg`: steady creep at stress σ > 0 with rate A·σⁿ dissipates σ·A·σⁿ·dt; A ≥ 0.
  * `parabolic_rate_nonneg`: a scale of thickness x > 0 growing at k_p/(2x) under a reaction affinity a > 0
    dissipates a·k_p/(2x)·dt; k_p ≥ 0.
  * `frictional_bond_nonneg`: a fibre whose bond stress is b·√f_c (f_c > 0) sliding over a slip area s > 0 dissipates
    b·√f_c·s; b ≥ 0.

  Each result is a bound, never a value: the registry value is a citation or a recorded choice inside it. Zero Lean
  axioms; physics enters only as the `SecondLaw` hypothesis.
-/

import Constants.SecondLawDissipation

open UMST.ProcessFamily UMST.Real UMST.Constants.SecondLawDissipation

namespace UMST.Constants.SecondLawSolidInelastic

/-- Free energy of a plastic strain `x` and a hardening variable `y` with modulus `k` and cross coupling `c`. -/
noncomputable def coupledWell (k c x y : ℝ) : ℝ := 1 / 2 * k * (x ^ 2 + y ^ 2 + 2 * c * x * y)

/-- **Coupled well**: a plastic strain and a hardening variable storing ½·k·(x² + y² + 2c·x·y) that relax passively
    from every `(x, y)`, with `k ≠ 0`, have `k > 0` and `−1 ≤ c ≤ 1`. -/
theorem coupledWell_bounds {ρ ρ' k c : ℝ} (hk : k ≠ 0)
    (h : ∀ x y : ℝ, SecondLaw .transition (.thermodynamic ⟨ρ, coupledWell k c x y⟩ ⟨ρ', 0⟩)) :
    0 < k ∧ -1 ≤ c ∧ c ≤ 1 := by
  have h10 : (0 : ℝ) ≤ coupledWell k c 1 0 := (h 1 0).2
  have h11 : (0 : ℝ) ≤ coupledWell k c 1 1 := (h 1 1).2
  have h1m : (0 : ℝ) ≤ coupledWell k c 1 (-1) := (h 1 (-1)).2
  unfold coupledWell at h10 h11 h1m
  have kpos : 0 < k := lt_of_le_of_ne (by nlinarith) (Ne.symm hk)
  refine ⟨kpos, ?_, ?_⟩
  · -- ½·k·(2 + 2c) ≥ 0 with k > 0
    by_contra hc
    push_neg at hc
    nlinarith
  · -- ½·k·(2 − 2c) ≥ 0 with k > 0
    by_contra hc
    push_neg at hc
    nlinarith

/-- **Double well**: a phase field `φ ∉ {0, 1}` storing k·φ²·(1 − φ)² that relaxes passively has `k ≥ 0`. -/
theorem doubleWell_modulus_nonneg {ρ ρ' k φ : ℝ} (h0 : φ ≠ 0) (h1 : φ ≠ 1)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, k * (φ ^ 2 * (1 - φ) ^ 2)⟩ ⟨ρ', 0⟩)) : 0 ≤ k := by
  have hs : (0 : ℝ) ≤ k * (φ ^ 2 * (1 - φ) ^ 2) := h.2
  have h1' : 1 - φ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hq : 0 < φ ^ 2 * (1 - φ) ^ 2 := by positivity
  by_contra hk
  push_neg at hk
  nlinarith

/-- **Griffith fracture energy**: a crack extension `ΔA > 0` that dissipates G_c·ΔA obeys the second law only when
    `G_c ≥ 0`. -/
theorem griffith_fracture_energy_nonneg {ρ ρ' ψ Gc dA : ℝ} (hA : 0 < dA)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - Gc * dA⟩)) : 0 ≤ Gc :=
  dissipation_coefficient_nonneg hA h

/-- **Fracture toughness**: with `G_c ≥ 0` from a crack extension and `E > 0` from the relaxation of a body held at
    stress `σ ≠ 0` (stored σ²/(2E)), the toughness `K = √(E·G_c)` is nonnegative and `K² = E·G_c`. -/
theorem griffith_toughness_nonneg {ρ ρ' ψ Gc dA E σ : ℝ} (hA : 0 < dA) (hσ : σ ≠ 0) (hE : E ≠ 0)
    (hG : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - Gc * dA⟩))
    (hR : SecondLaw .transition (.thermodynamic ⟨ρ, σ ^ 2 / (2 * E)⟩ ⟨ρ', 0⟩)) :
    0 ≤ Real.sqrt (E * Gc) ∧ Real.sqrt (E * Gc) ^ 2 = E * Gc := by
  have hGc : 0 ≤ Gc := griffith_fracture_energy_nonneg hA hG
  have h0 : (0 : ℝ) ≤ σ ^ 2 / (2 * E) := hR.2
  have hEpos : 0 < E := by
    rcases lt_or_gt_of_ne hE with hneg | hpos
    · have : σ ^ 2 / (2 * E) < 0 := div_neg_of_pos_of_neg (by positivity) (by linarith)
      linarith
    · exact hpos
  exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt (mul_nonneg hEpos.le hGc)⟩

/-- **Norton creep**: steady creep at stress `σ > 0` with rate A·σⁿ over `dt > 0` dissipates σ·(A·σⁿ)·dt; the second
    law gives `A ≥ 0` for every exponent `n`. -/
theorem norton_coefficient_nonneg {ρ ρ' ψ A σ n dt : ℝ} (hσ : 0 < σ) (hdt : 0 < dt)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - σ * (A * σ ^ n) * dt⟩)) : 0 ≤ A := by
  have hp : 0 < σ ^ n := Real.rpow_pos_of_pos hσ n
  have hq : 0 < σ * σ ^ n * dt := by positivity
  have e : σ * (A * σ ^ n) * dt = A * (σ * σ ^ n * dt) := by ring
  rw [e] at h
  exact dissipation_coefficient_nonneg hq h

/-- **Parabolic scaling**: a scale of thickness `x > 0` growing at k_p/(2x) under a reaction affinity `a > 0` over
    `dt > 0` dissipates a·(k_p/(2x))·dt; the second law gives `k_p ≥ 0`. -/
theorem parabolic_rate_nonneg {ρ ρ' ψ a kp x dt : ℝ} (ha : 0 < a) (hx : 0 < x) (hdt : 0 < dt)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - a * (kp / (2 * x)) * dt⟩)) : 0 ≤ kp := by
  have hq : 0 < a / (2 * x) * dt := by positivity
  have e : a * (kp / (2 * x)) * dt = kp * (a / (2 * x) * dt) := by
    field_simp
    ring
  rw [e] at h
  exact dissipation_coefficient_nonneg hq h

/-- **Frictional bond**: a fibre whose bond stress is b·√f_c (`f_c > 0`) sliding over a slip area `s > 0` dissipates
    b·√f_c·s; the second law gives `b ≥ 0`. -/
theorem frictional_bond_nonneg {ρ ρ' ψ b fc s : ℝ} (hfc : 0 < fc) (hs : 0 < s)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - b * Real.sqrt fc * s⟩)) : 0 ≤ b := by
  have hr : 0 < Real.sqrt fc := Real.sqrt_pos.mpr hfc
  have hq : 0 < Real.sqrt fc * s := by positivity
  have e : b * Real.sqrt fc * s = b * (Real.sqrt fc * s) := by ring
  rw [e] at h
  exact dissipation_coefficient_nonneg hq h

end UMST.Constants.SecondLawSolidInelastic
