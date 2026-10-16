-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: UnfoldProxStepLaws.lean

  Law L3 of the unfold solver family (`workspace/docs/blueprints/UMST_UNFOLD_CROSS_DOMAIN.md`, section 6): each
  accepted proximal or minimising-movement step satisfies the discrete inequality, and an anti-dissipative step is
  refused. A step from `x₀` with step size `τ > 0` minimises the incremental potential
  `J(x) = ψ(x) − w(x) + τ φ(d x)` over the states, with `ψ` the free energy, `w` the work the loading supplies
  (`w x₀ = 0`), `φ` the dissipation potential (`φ 0 = 0`) and `d x` the rate of the increment (`d x₀ = 0`).

  * **Discrete inequality from minimality** (`prox_step_le`): `ψ x⁺ − ψ x₀ + τ φ(d x⁺) ≤ w x⁺ − w x₀`; with `φ ≥ 0`
    the free-energy change is at most the supplied work (`prox_step_deltaF_le`). An anti-dissipative candidate, one
    that breaks the inequality, is no minimiser (`prox_step_refused`).
  * **Discrete inequality from stationarity** (`prox_step_stationary_le`): on a scalar state with rate
    `v = (x⁺ − x₀) / τ`, supporting lines of the convex `ψ` (slope `a`) and `φ` (slope `b`) at the step's point,
    with the first-order condition `a + b = f` against the load `f`, give `ψ x⁺ − ψ x₀ + τ φ(v) ≤ f (x⁺ − x₀)`: the
    convexity of `ψ` and `φ` makes a stationary point of the implicit step a step that satisfies the inequality. The
    slope of `φ` makes the dissipation rate non-negative, `b v ≥ φ(v) ≥ 0` (`prox_dissipation_rate_nonneg`).
  * **SecondLaw instances.** The step is the one inequality with ΔF the free-energy change, W_in the supplied work
    and no information term (`prox_step_oneInequality`); a passive step (no supplied work) with the mass condition of
    the gate is the `.transition` case of `SecondLaw` through the passive route (`prox_step_passive_secondLaw`,
    from `Convex.PassiveRoute.passive_inequality_secondLaw`).

  Zero `axiom`, zero `sorry`.
-/

import OneInequalitySecondLaw
import Convex.PassiveRoute

open UMST.ProcessFamily UMST.Core UMST.Real UMST.LandauerLaw UMST.OneInequalitySecondLaw

namespace UMST.UnfoldProxStepLaws

section Field

variable {α X : Type} [LinearOrderedField α]

/-- The incremental potential of a proximal step: `ψ x − w x + τ φ(d x)`. -/
def incremental (ψ w : X → α) (φ : α → α) (d : X → α) (τ : α) (x : X) : α := ψ x - w x + τ * φ (d x)

/-- `xp` minimises the incremental potential. -/
def IsProxStep (ψ w : X → α) (φ : α → α) (d : X → α) (τ : α) (xp : X) : Prop :=
  ∀ x, incremental ψ w φ d τ xp ≤ incremental ψ w φ d τ x

/-- **L3 from minimality**: an accepted step satisfies `ψ x⁺ − ψ x₀ + τ φ(d x⁺) ≤ w x⁺ − w x₀`. -/
theorem prox_step_le {ψ w : X → α} {φ : α → α} {d : X → α} {τ : α} {x₀ xp : X}
    (hφ0 : φ 0 = 0) (hd0 : d x₀ = 0) (hmin : IsProxStep ψ w φ d τ xp) :
    ψ xp - ψ x₀ + τ * φ (d xp) ≤ w xp - w x₀ := by
  have h := hmin x₀
  simp only [incremental, hd0, hφ0, mul_zero, add_zero] at h
  linarith

/-- **L3, the inequality ΔF ≤ W_in**: with a non-negative dissipation potential the free-energy change of an accepted
    step is at most the supplied work. -/
theorem prox_step_deltaF_le {ψ w : X → α} {φ : α → α} {d : X → α} {τ : α} {x₀ xp : X}
    (hτ : 0 ≤ τ) (hφ : ∀ v, 0 ≤ φ v) (hφ0 : φ 0 = 0) (hd0 : d x₀ = 0) (hmin : IsProxStep ψ w φ d τ xp) :
    ψ xp - ψ x₀ ≤ w xp - w x₀ := by
  have h := prox_step_le hφ0 hd0 hmin
  have := mul_nonneg hτ (hφ (d xp))
  linarith

/-- **L3 refusal**: a candidate that breaks the discrete inequality is no minimiser. -/
theorem prox_step_refused {ψ w : X → α} {φ : α → α} {d : X → α} {τ : α} {x₀ xp : X}
    (hφ0 : φ 0 = 0) (hd0 : d x₀ = 0) (hanti : w xp - w x₀ < ψ xp - ψ x₀ + τ * φ (d xp)) :
    ¬ IsProxStep ψ w φ d τ xp :=
  fun hmin => absurd (prox_step_le hφ0 hd0 hmin) (not_le.2 hanti)

/-- **L3 from stationarity** (scalar state): supporting lines of the convex `ψ` and `φ` at the step's point with the
    first-order condition `a + b = f` give `ψ x⁺ − ψ x₀ + τ φ(v) ≤ f (x⁺ − x₀)`, where `τ v = x⁺ − x₀`. -/
theorem prox_step_stationary_le {ψ : α → α} {φ : α → α} {τ x₀ xp v a b f : α}
    (hv : τ * v = xp - x₀) (hφ0 : φ 0 = 0) (hτ : 0 ≤ τ)
    (hψ : ψ x₀ ≥ ψ xp + a * (x₀ - xp)) (hφ : φ 0 ≥ φ v + b * (0 - v)) (hstat : a + b = f) :
    ψ xp - ψ x₀ + τ * φ v ≤ f * (xp - x₀) := by
  rw [hφ0] at hφ
  have h1 : τ * φ v ≤ τ * (b * v) := mul_le_mul_of_nonneg_left (by linarith) hτ
  have h2 : τ * (b * v) = b * (xp - x₀) := by rw [← hv]; ring
  rw [← hstat]
  nlinarith

/-- The slope of a convex `φ` with `φ 0 = 0` and `φ ≥ 0` makes the dissipation rate non-negative: `b v ≥ φ(v) ≥ 0`. -/
theorem prox_dissipation_rate_nonneg {φ : α → α} {v b : α} (hφ0 : φ 0 = 0) (hφv : 0 ≤ φ v)
    (hφ : φ 0 ≥ φ v + b * (0 - v)) : φ v ≤ b * v ∧ 0 ≤ b * v := by
  rw [hφ0] at hφ
  constructor <;> nlinarith

end Field

section SecondLaw

variable {X : Type}

/-- An accepted step as one step of the one inequality: ΔF the free-energy change, W_in the supplied work, no
    information. -/
def proxStep (b : HeatBath) (ψ w : X → ℝ) (x₀ xp : X) : Step := ⟨b, ψ xp - ψ x₀, w xp - w x₀, 0⟩

/-- **L3 as the one inequality**: an accepted step with a non-negative dissipation potential satisfies
    ΔF ≤ W_in + k_B T I with I = 0. -/
theorem prox_step_oneInequality (b : HeatBath) {ψ w : X → ℝ} {φ : ℝ → ℝ} {d : X → ℝ} {τ : ℝ} {x₀ xp : X}
    (hτ : 0 ≤ τ) (hφ : ∀ v, 0 ≤ φ v) (hφ0 : φ 0 = 0) (hd0 : d x₀ = 0) (hmin : IsProxStep ψ w φ d τ xp) :
    oneInequality (proxStep b ψ w x₀ xp) := by
  have h := prox_step_deltaF_le hτ hφ hφ0 hd0 hmin
  simp only [oneInequality, proxStep, mul_zero, add_zero]
  exact h

/-- **L3 through the passive route**: a passive accepted step (no supplied work) whose states carry the mass
    condition of the gate is the `.transition` case of `SecondLaw`. -/
theorem prox_step_passive_secondLaw {ψ : X → ℝ} {φ : ℝ → ℝ} {d : X → ℝ} {τ ρ ρ' : ℝ} {x₀ xp : X}
    (hτ : 0 ≤ τ) (hφ : ∀ v, 0 ≤ φ v) (hφ0 : φ 0 = 0) (hd0 : d x₀ = 0)
    (hmin : IsProxStep ψ (fun _ => 0) φ d τ xp)
    (hm : CoreMassCond ℝ RealThermodynamicState ⟨ρ, ψ x₀⟩ ⟨ρ', ψ xp⟩) :
    SecondLaw .transition (.thermodynamic ⟨ρ, ψ x₀⟩ ⟨ρ', ψ xp⟩) := by
  have h := prox_step_le hφ0 hd0 hmin
  exact UMST.Convex.PassiveRoute.passive_inequality_secondLaw hm (mul_nonneg hτ (hφ (d xp))) (by simpa using h)

end SecondLaw

end UMST.UnfoldProxStepLaws
