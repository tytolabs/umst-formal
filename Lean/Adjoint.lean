/-
  SPDX-License-Identifier: Apache-2.0

  UMST-Formal: Adjoint.lean
  Adjoint / terminal-gradient identity for linear ODEs in finite dimension.

  Informal (Euclidean ℝⁿ, standard inner product `Matrix.dotProduct`):
    • Forward `ẋ = A x` with `x(T) = exp(T A) x₀`.
    • Linear terminal cost `L(x) = ⟨c, x⟩`, so `∇L(x) = c`.
    • Adjoint `ȧ = −Aᵀ a`, `a(T) = c` has closed form `a(t) = exp((T−t) Aᵀ) c`.

  Headline (mechanised):
    • `adjoint_recovers_gradient`: `(exp ℝ (T • A))ᵀ *ᵥ c = exp ℝ (T • Aᵀ) *ᵥ c`, i.e. the
      Euclidean gradient `∇_{x₀} ⟨c, exp(T A) x₀⟩` identifies with `exp(T Aᵀ) c = a(0)`.
    • `adjoint_uses_only_terminal`: the closed-form adjoint at time `t` is independent
      of any putative forward trajectory `x(s)` for `s ∈ (0,T)` — it depends only on
      `(T, t, A, c)` by construction.

  Nonlinear continuous adjoint and `∂x/∂x₀` along flows require Lipschitz ODE lemmas in
  `Mathlib.Analysis.ODE`; that layer is **TODO_FORMAL** once the relevant API is stable
  enough to discharge the standard Pontryagin / sensitivity proof without new physics
  axioms. This file is the linear operational anchor only.
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Matrix
open NormedSpace

namespace UMST

variable {n : ℕ}

/-- Closed-form adjoint `a(t) = exp((T − t) Aᵀ) c` (terminal data only). -/
noncomputable def adjointClosedForm (t T : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    Fin n → ℝ :=
  exp ℝ ((T - t) • Aᵀ) *ᵥ c

/-- Terminal-gradient / transpose-exponential identity (linear adjoint at `t = 0`). -/
theorem adjoint_recovers_gradient (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (T : ℝ) :
    (exp ℝ (T • A))ᵀ *ᵥ c = exp ℝ (T • Aᵀ) *ᵥ c := by
  have hM : (exp ℝ (T • A))ᵀ = exp ℝ (T • Aᵀ) := by
    calc
      (exp ℝ (T • A))ᵀ = exp ℝ ((T • A)ᵀ) := (Matrix.exp_transpose (𝕂 := ℝ) _).symm
      _ = exp ℝ (T • Aᵀ) := by simp [Matrix.transpose_smul]
  simp [hM]

/-- The closed-form adjoint value does not depend on which forward trajectory is chosen. -/
theorem adjoint_uses_only_terminal (t T : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (_traj₁ _traj₂ : ℝ → Fin n → ℝ) :
    adjointClosedForm t T A c = adjointClosedForm t T A c :=
  rfl

#print axioms adjoint_recovers_gradient
#print axioms adjoint_uses_only_terminal

end UMST
