-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Constants/SecondLawDissipation.lean

  Dissipation coefficients bounded by the second law. A passive step whose dissipated energy leaves the free energy
  (no supplied power: ψ_new = ψ_old − D) satisfies the `.transition` case of `UMST.ProcessFamily.SecondLaw` only
  when D ≥ 0. Writing D as a coefficient times a positive measure of the step bounds the coefficient.

  * `dissipation_coefficient_nonneg`: D = c·q with q > 0 gives c ≥ 0.
  * `viscosity_nonneg`: a Newtonian dashpot (or a Maxwell arm with η = E·τ, or a rate channel φ = ½·η·ṡ²) at rate
    r ≠ 0 over a time dt > 0 dissipates η·r²·dt; the second law gives η ≥ 0.
  * `bingham_nonneg`: a Bingham fluid dissipates (τ₀·|r| + η_p·r²)·dt; the second law at every rate r gives a
    yield stress τ₀ ≥ 0 and a plastic viscosity η_p ≥ 0.
  * `lossModulus_nonneg`: a linear viscoelastic solid in a harmonic strain cycle of amplitude ε₀ ≠ 0 returns its
    stored energy and dissipates π·E″·ε₀² per cycle; the second law gives E″ ≥ 0 and, for a storage modulus E′ > 0,
    a loss factor tan δ = E″/E′ ≥ 0.

  Each result is a bound, never a value. Zero Lean axioms; physics enters only as the `SecondLaw` hypothesis.
-/

import Process

open UMST.ProcessFamily UMST.Real

namespace UMST.Constants.SecondLawDissipation

/-- **Dissipation coefficient**: a passive step that dissipates `c·q` (`q > 0`) out of the free energy obeys the
    second law only when `c ≥ 0`. -/
theorem dissipation_coefficient_nonneg {ρ ρ' ψ c q : ℝ} (hq : 0 < q)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - c * q⟩)) : 0 ≤ c := by
  have hd : ψ - c * q ≤ ψ := h.2
  by_contra hc
  push_neg at hc
  nlinarith

/-- **Viscosity**: a dashpot at rate `r ≠ 0` over `dt > 0` dissipates η·r²·dt; the second law gives `η ≥ 0`. -/
theorem viscosity_nonneg {ρ ρ' ψ η r dt : ℝ} (hr : r ≠ 0) (hdt : 0 < dt)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - η * r ^ 2 * dt⟩)) : 0 ≤ η := by
  have hq : 0 < r ^ 2 * dt := by positivity
  exact dissipation_coefficient_nonneg hq (by simpa only [mul_assoc] using h)

/-- **Bingham fluid**: dissipating (τ₀·|r| + η_p·r²)·dt at every rate `r` under the second law gives a yield
    stress `τ₀ ≥ 0` and a plastic viscosity `η_p ≥ 0`. -/
theorem bingham_nonneg {ρ ρ' ψ τ0 ηp dt : ℝ} (hdt : 0 < dt)
    (h : ∀ r : ℝ, SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - (τ0 * |r| + ηp * r ^ 2) * dt⟩)) :
    0 ≤ τ0 ∧ 0 ≤ ηp := by
  -- At every positive rate the dissipation per unit rate, τ₀ + η_p·r, is nonnegative.
  have per : ∀ r : ℝ, 0 < r → 0 ≤ τ0 + ηp * r := by
    intro r hr
    have hc : 0 ≤ τ0 * |r| + ηp * r ^ 2 := dissipation_coefficient_nonneg hdt (h r)
    rw [abs_of_pos hr] at hc
    have hm : r * 0 ≤ r * (τ0 + ηp * r) := by nlinarith
    exact le_of_mul_le_mul_left hm hr
  constructor
  · -- A negative yield stress is undone at a small enough rate.
    by_contra hτ
    push_neg at hτ
    have hk : 0 < |ηp| + 1 := by positivity
    set r := -τ0 / (2 * (|ηp| + 1)) with hrdef
    have hr : 0 < r := div_pos (by linarith) (by linarith)
    have hkr : (|ηp| + 1) * r = -τ0 / 2 := by rw [hrdef]; field_simp; ring
    have hle : ηp * r ≤ |ηp| * r := mul_le_mul_of_nonneg_right (le_abs_self ηp) hr.le
    have := per r hr
    nlinarith
  · -- A negative plastic viscosity is undone at a large enough rate.
    by_contra hη
    push_neg at hη
    set r := 2 * (|τ0| + 1) / -ηp with hrdef
    have hr : 0 < r := div_pos (by positivity) (by linarith)
    have hne : -ηp ≠ 0 := by linarith
    have hηr : ηp * r = -(2 * (|τ0| + 1)) := by
      rw [hrdef, mul_div_assoc', div_eq_iff hne]
      ring
    have := per r hr
    have := le_abs_self τ0
    have := abs_nonneg τ0
    linarith

/-- **Loss modulus**: a harmonic strain cycle of amplitude `ε₀ ≠ 0` that dissipates π·E″·ε₀² obeys the second
    law only when `E″ ≥ 0`; for a storage modulus `E′ > 0` the loss factor `E″/E′` is nonnegative. -/
theorem lossModulus_nonneg {ρ ρ' ψ E' E'' ε0 : ℝ} (hε : ε0 ≠ 0) (hE' : 0 < E')
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - E'' * (Real.pi * ε0 ^ 2)⟩)) :
    0 ≤ E'' ∧ 0 ≤ E'' / E' := by
  have hq : 0 < Real.pi * ε0 ^ 2 := by positivity
  have h0 := dissipation_coefficient_nonneg hq h
  exact ⟨h0, div_nonneg h0 hE'.le⟩

end UMST.Constants.SecondLawDissipation
