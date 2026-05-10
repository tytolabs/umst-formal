/-
  SPDX-License-Identifier: Apache-2.0

  UMST-Formal: DEC.lean
  Discrete Exterior Calculus (DEC) on a finite oriented graph — witness complex.

  Informal claims (display forms use ℚ valued cochains):
    • Coboundary `d : (V → ℚ) → (E → ℚ)` is `(d ω) e = ω (head e) − ω (tail e)`.
    • Boundary `B₁ : (E → ℚ) → (V → ℚ)` is the transpose incidence operator.
    • Hodge Laplacian on 0-cochains `Δ₀ := B₁ ∘ B₁ᵀ` is self-adjoint:
        `⟨Δ₀ ω, ψ⟩ = ⟨ω, Δ₀ ψ⟩`.
    • Row sums of `Δ₀` vanish (mass conservation / graph Laplacian property).
    • With one triangular 2-face, `B₁ ∘ B₂ = 0` (chain-complex closure).
    • Discrete Stokes on the oriented triangle: for every 0-cochain `ω`,
        `∑_{e ∈ ∂Δ} (d ω) e = 0`.

  We realise this on a single oriented 3-cycle (triangle): three vertices `Fin 3`,
  three edges matching the cycle orientation, and one face so `B₂` is the(face → edges)
  boundary. Broader CW / manifold DEC is cited only in prose; this file is 1-skeleton
  plus one closing face as in classical discrete Hodge theory texts.

  Formalisation uses the signed incidence matrix `D` with `d ω = D *ᵥ ω` and
  `Δ₀ = Dᵀ * D`.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

open scoped BigOperators Matrix

namespace UMST

/-- Vertices of the witness triangle. -/
abbrev V := Fin 3

/-- Oriented edges (same indexing as `Fin 3`). -/
abbrev E := Fin 3

/-- One triangular face. -/
abbrev F := Fin 1

/-- Signed incidence matrix `D : E × V` for the oriented cycle 0→1→2→0. -/
def D : Matrix E V ℚ :=
  !![(-1 : ℚ), 1, 0;
       0, (-1 : ℚ), 1;
       1, 0, (-1 : ℚ)]

/-- Coboundary `d ω = D *ᵥ ω`. -/
noncomputable def d (ω : V → ℚ) : E → ℚ :=
  D *ᵥ ω

/-- Boundary `B₁ = Dᵀ` on 1-chains (column model). -/
noncomputable def B1 : Matrix V E ℚ :=
  Dᵀ

/-- Boundary operator on edge chains, matrix form `B₁ * φ`. -/
noncomputable def B1Lin (φ : E → ℚ) : V → ℚ :=
  B1 *ᵥ φ

/-- Hodge Laplacian on 0-cochains `Δ₀ = Dᵀ D`. -/
noncomputable def Δ₀ : Matrix V V ℚ :=
  Dᵀ * D

/-- Face-to-edges boundary: the oriented 2-simplex has boundary `e₀ + e₁ + e₂`. -/
def B2 : Matrix E F ℚ :=
  !![(1 : ℚ); 1; 1]

/-- `B₁ = Dᵀ` as explicit numerals (for `norm_num` in `boundary_squared_zero`). -/
lemma B1_eq : B1 = !![
    (-1 : ℚ), 0, 1;
    1, -1, 0;
    0, 1, -1] := by
  unfold B1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, D,
    Matrix.cons_val', Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val'] <;> norm_num

theorem hodge_laplacian_symmetric (ω ψ : V → ℚ) :
    Matrix.dotProduct (Δ₀ *ᵥ ω) ψ = Matrix.dotProduct ω (Δ₀ *ᵥ ψ) := by
  have hsymm : Δ₀ᵀ = Δ₀ := by
    simp [Δ₀, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  calc
    Matrix.dotProduct (Δ₀ *ᵥ ω) ψ
        = Matrix.dotProduct ψ (Δ₀ *ᵥ ω) := Matrix.dotProduct_comm _ _
    _ = Matrix.dotProduct (ψ ᵥ* Δ₀) ω := Matrix.dotProduct_mulVec ψ Δ₀ ω
    _ = Matrix.dotProduct (Δ₀ᵀ *ᵥ ψ) ω := by rw [← Matrix.mulVec_transpose Δ₀ ψ]
    _ = Matrix.dotProduct (Δ₀ *ᵥ ψ) ω := by rw [hsymm]
    _ = Matrix.dotProduct ω (Δ₀ *ᵥ ψ) := Matrix.dotProduct_comm _ _

/-- Constant 1 cochain on vertices (all-ones vector). -/
def oneV : V → ℚ :=
  fun _ => 1

lemma laplacian_mul_one_eq_zero : Δ₀ *ᵥ oneV = 0 := by
  funext i
  fin_cases i <;>
    simp [Δ₀, Matrix.mulVec, Matrix.mul_apply, oneV, D, Matrix.transpose_apply,
      Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
      Matrix.cons_val', Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val'] <;> ring

theorem laplacian_row_sum_zero (v : V) : (∑ v' : V, Δ₀ v v') = 0 := by
  have hsum : (∑ v' : V, Δ₀ v v') = (Δ₀ *ᵥ oneV) v := by
    simp [Matrix.mulVec, Matrix.mul_apply, oneV, mul_one, Finset.sum_fin_eq_sum_range,
      Finset.sum_range_succ]
  rw [hsum, congr_fun laplacian_mul_one_eq_zero v]
  rfl

theorem boundary_squared_zero : B1 * B2 = 0 := by
  rw [B1_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B2, Matrix.mul_apply,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] <;> norm_num

theorem discrete_stokes (ω : V → ℚ) : (∑ e : E, (d ω) e) = 0 := by
  simp [d, Matrix.mulVec, Matrix.mul_apply, D, Finset.sum_fin_eq_sum_range,
    Finset.sum_range_succ, mul_add, add_mul, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm]

#print axioms hodge_laplacian_symmetric
#print axioms laplacian_row_sum_zero
#print axioms discrete_stokes

end UMST
