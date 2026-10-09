-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Constants/SecondLawPoroContinuum.lean

  Transport, reaction and poroelastic constants bounded by the second law. Each theorem takes a passive step as a
  `.transition` case of `UMST.ProcessFamily.SecondLaw` (free energy does not rise) and concludes a bound on one
  constant. Two kinds of step occur, as in `Constants.SecondLawDissipation` and `Constants.SecondLawElastic`:

  * a dissipating step, ψ_new = ψ − D, whose dissipation D is the constant times a positive measure of the step;
  * a relaxation of a loaded state to the natural state (free energy zero), whose stored energy is a quadratic form
    in the constant.

  Results:

  * `reaction_rate_nonneg`: a reaction with affinity A > 0 advancing at rate ξ̇ over dt > 0 dissipates A·ξ̇·dt;
    the second law gives ξ̇ ≥ 0.
  * `reaction_rate_constant_nonneg`: a rate law ξ̇ = k·g with a positive driving factor g gives k ≥ 0.
  * `fick_diffusivity_nonneg`: Fickian diffusion at a concentration gradient g ≠ 0 with thermodynamic factor
    χ = ∂μ/∂c > 0 dissipates D·χ·g²·dt; the second law gives D ≥ 0.
  * `darcy_permeability_nonneg`: Darcy flow at a pressure gradient g ≠ 0 through a fluid of viscosity μ > 0
    dissipates (κ/μ)·g²·dt; the second law gives κ ≥ 0.
  * `biot_coefficient_bounds`: a poroelastic skeleton with solid-matrix bulk modulus K_s > 0, drained bulk modulus
    K and skeleton pore compliance n = 1/N, related to the Biot coefficient b and porosity φ by K = K_s·(1 − b) and
    b − φ = K_s·n, whose drained mode and pore mode relax passively, has φ ≤ b ≤ 1.
  * `biot_storage_pos`: the Biot storage coefficient 1/M = n + φ·c_f (c_f the fluid compliance 1/K_f) of such a
    skeleton with φ > 0 and a fluid of nonzero compliance is positive, and the Biot modulus M with M·(1/M) = 1 is
    positive.
  * `isotropic_moduli_pos`: an isotropic solid storing ½·K·e² + ½·G·γ² with K ≠ 0 and G ≠ 0 that relaxes from
    every volumetric strain e and shear γ has K > 0, G > 0 and −1 < ν < 1/2.

  Each result is a bound, never a value: the law fixes the sign or the interval, and the registry value is a
  measurement, a citation or a choice inside it. Zero Lean axioms; physics enters only as the `SecondLaw`
  hypothesis; the Biot relations enter as hypotheses on the constants.
-/

import Process
import Constants.SecondLawDissipation
import Constants.SecondLawElastic

open UMST.ProcessFamily UMST.Real

namespace UMST.Constants.SecondLawPoroContinuum

/-- **Reaction rate**: a reaction with affinity `A > 0` advancing at rate `ξ̇` over `dt > 0` dissipates A·ξ̇·dt;
    the second law gives `ξ̇ ≥ 0`. -/
theorem reaction_rate_nonneg {ρ ρ' ψ A r dt : ℝ} (hA : 0 < A) (hdt : 0 < dt)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - A * r * dt⟩)) : 0 ≤ r := by
  have hq : 0 < A * dt := mul_pos hA hdt
  exact SecondLawDissipation.dissipation_coefficient_nonneg hq (by
    have e : A * r * dt = r * (A * dt) := by ring
    rw [e] at h
    exact h)

/-- **Rate constant**: a reaction with affinity `A > 0` and rate law ξ̇ = k·g, `g > 0`, dissipates A·(k·g)·dt;
    the second law gives `k ≥ 0`. -/
theorem reaction_rate_constant_nonneg {ρ ρ' ψ A k g dt : ℝ} (hA : 0 < A) (hg : 0 < g) (hdt : 0 < dt)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - A * (k * g) * dt⟩)) : 0 ≤ k := by
  have hq : 0 < A * g * dt := by positivity
  exact SecondLawDissipation.dissipation_coefficient_nonneg hq (by
    have e : A * (k * g) * dt = k * (A * g * dt) := by ring
    rw [e] at h
    exact h)

/-- **Diffusivity**: Fickian diffusion at a gradient `g ≠ 0` with thermodynamic factor `χ > 0` over `dt > 0`
    dissipates D·χ·g²·dt; the second law gives `D ≥ 0`. -/
theorem fick_diffusivity_nonneg {ρ ρ' ψ D χ g dt : ℝ} (hχ : 0 < χ) (hg : g ≠ 0) (hdt : 0 < dt)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - D * χ * g ^ 2 * dt⟩)) : 0 ≤ D := by
  have hq : 0 < χ * g ^ 2 * dt := by positivity
  exact SecondLawDissipation.dissipation_coefficient_nonneg hq (by
    have e : D * χ * g ^ 2 * dt = D * (χ * g ^ 2 * dt) := by ring
    rw [e] at h
    exact h)

/-- **Permeability**: Darcy flow at a pressure gradient `g ≠ 0` through a fluid of viscosity `μ > 0` over
    `dt > 0` dissipates (κ/μ)·g²·dt; the second law gives `κ ≥ 0`. -/
theorem darcy_permeability_nonneg {ρ ρ' ψ κ μ g dt : ℝ} (hμ : 0 < μ) (hg : g ≠ 0) (hdt : 0 < dt)
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - κ / μ * g ^ 2 * dt⟩)) : 0 ≤ κ := by
  have hq : 0 < (1 / μ) * g ^ 2 * dt := by positivity
  exact SecondLawDissipation.dissipation_coefficient_nonneg hq (by
    have e : κ / μ * g ^ 2 * dt = κ * ((1 / μ) * g ^ 2 * dt) := by ring
    rw [e] at h
    exact h)

/-- **Biot coefficient**: with `K = K_s·(1 − b)` and `b − φ = K_s·n` (`K_s > 0`), a drained mode storing ½·K·s²
    and a pore mode storing ½·n·s² that relax passively at a strain `s ≠ 0` give `φ ≤ b ≤ 1`. -/
theorem biot_coefficient_bounds {ρ ρ' K Ks n φ b s : ℝ} (hs : s ≠ 0) (hKs : 0 < Ks)
    (hK : K = Ks * (1 - b)) (hn : b - φ = Ks * n)
    (hdrained : SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * K * s ^ 2⟩ ⟨ρ', 0⟩))
    (hpore : SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * n * s ^ 2⟩ ⟨ρ', 0⟩)) :
    φ ≤ b ∧ b ≤ 1 := by
  have hK0 : 0 ≤ K := SecondLawElastic.relaxation_stiffness_nonneg hs hdrained
  have hn0 : 0 ≤ n := SecondLawElastic.relaxation_stiffness_nonneg hs hpore
  constructor
  · nlinarith
  · by_contra hb
    push_neg at hb
    nlinarith

/-- **Biot storage**: with `m = n + φ·c_f`, `φ > 0`, a pore mode storing ½·n·s² and a fluid mode storing
    ½·c_f·s² (`c_f ≠ 0`) that relax passively at a strain `s ≠ 0`, the storage coefficient `m = 1/M` is positive
    and so is the Biot modulus `M` with `M·m = 1`. -/
theorem biot_storage_pos {ρ ρ' n cf φ m M s : ℝ} (hs : s ≠ 0) (hφ : 0 < φ) (hcf : cf ≠ 0)
    (hm : m = n + φ * cf) (hM : M * m = 1)
    (hpore : SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * n * s ^ 2⟩ ⟨ρ', 0⟩))
    (hfluid : SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * cf * s ^ 2⟩ ⟨ρ', 0⟩)) :
    0 < m ∧ 0 < M := by
  have hn0 : 0 ≤ n := SecondLawElastic.relaxation_stiffness_nonneg hs hpore
  have hcf0 : 0 < cf := lt_of_le_of_ne (SecondLawElastic.relaxation_stiffness_nonneg hs hfluid) (Ne.symm hcf)
  have hm0 : 0 < m := by rw [hm]; positivity
  refine ⟨hm0, ?_⟩
  by_contra hM0
  push_neg at hM0
  nlinarith

/-- **Isotropic moduli**: an isotropic solid storing ½·K·e² + ½·G·γ² with `K ≠ 0`, `G ≠ 0` that relaxes passively
    from every `(e, γ)` has `K > 0`, `G > 0` and `−1 < ν < 1/2`. -/
theorem isotropic_moduli_pos {ρ ρ' K G : ℝ} (hK : K ≠ 0) (hG : G ≠ 0)
    (h : ∀ e γ : ℝ, SecondLaw .transition (.thermodynamic ⟨ρ, 1 / 2 * K * e ^ 2 + 1 / 2 * G * γ ^ 2⟩ ⟨ρ', 0⟩)) :
    0 < K ∧ 0 < G ∧ -1 < SecondLawElastic.poissonRatio K G ∧ SecondLawElastic.poissonRatio K G < 1 / 2 := by
  obtain ⟨hK0, hG0⟩ := SecondLawElastic.twoMode_stiffness_nonneg h
  have hKp : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hK)
  have hGp : 0 < G := lt_of_le_of_ne hG0 (Ne.symm hG)
  have hd : 0 < 2 * (3 * K + G) := by linarith
  unfold SecondLawElastic.poissonRatio
  refine ⟨hKp, hGp, ?_, ?_⟩
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_lt_iff₀ hd]; linarith

end UMST.Constants.SecondLawPoroContinuum
