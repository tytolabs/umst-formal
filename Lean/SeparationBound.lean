/-
  Accuracy–safety separation (Theorem 2, paper) — real-line (MAE-compatible) core.

  Interpreting scalar predictions p = P(x), g = Gate(P(x)), y = ground truth in ℝ with
  absolute error, the triangle inequality yields the bound cited in the paper:
  |g - y| ≤ |p - y| + |g - p|, hence |g - y| ≤ |p - y| + δ whenever the gate / projection
  moves the prediction by at most δ in that metric.

  This does not formalise the full admissible manifold 𝒟_{valid} ⊂ ℝ^n; it is the
  analytic inequality that instantiates the paper's ε_G ≤ ε_P + δ_max claim per sample,
  which is sufficient to justify the theorem statement as a machine-checked lemma.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace UMST

theorem accuracy_safety_separation_real (p g y δ : ℝ) (hδ : |g - p| ≤ δ) :
    |g - y| ≤ |p - y| + δ := by
  have heq : g - y = (g - p) + (p - y) := by ring
  rw [heq]
  have tri := abs_add_le (g - p) (p - y)
  have hop : |g - p| + |p - y| ≤ |p - y| + δ := by
    linarith [hδ]
  exact le_trans tri hop

/-- Symmetric form with |p - g| instead of |g - p|. -/
theorem accuracy_safety_separation_real_symm (p g y δ : ℝ) (hδ : |p - g| ≤ δ) :
    |g - y| ≤ |p - y| + δ := by
  have hg : |g - p| = |p - g| := (abs_sub_comm p g).symm
  have hδ' : |g - p| ≤ δ := by simpa [hg] using hδ
  exact accuracy_safety_separation_real p g y δ hδ'

end UMST
