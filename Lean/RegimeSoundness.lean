/-
  SPDX-License-Identifier: Apache-2.0

  UMST-Formal: RegimeSoundness.lean
  Soundness of the cartridge regime-warning predicate on a rational hyperbox.

  Informal:
    • Regime = axis-aligned box `∏_i [lo_i, hi_i]` on `Fin n → ℚ`.
    • `in_regime p` iff every coordinate lies in its interval.
    • `warning_set p = { i | p i < lo i ∨ hi i < p i }`.

  Headline:
    • `warnings_empty_iff_in_regime`
    • `warning_dimension_violated`
    • `in_regime_decidable`
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Empty
import Mathlib.Tactic

namespace UMST

variable {n : ℕ} (lo hi : Fin n → ℚ) (p : Fin n → ℚ)

def in_regime : Prop :=
  ∀ i, lo i ≤ p i ∧ p i ≤ hi i

def warning_set : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i < lo i ∨ hi i < p i)

theorem warnings_empty_iff_in_regime :
    warning_set lo hi p = ∅ ↔ in_regime lo hi p := by
  classical
  constructor
  · intro he i
    by_contra h'
    have mem : i ∈ warning_set lo hi p := by
      simp [warning_set, Finset.mem_filter]
      rcases not_and_or.mp h' with h1 | h2
      · exact Or.inl (lt_of_not_ge h1)
      · exact Or.inr (lt_of_not_ge h2)
    rw [he] at mem
    exact Finset.not_mem_empty _ mem
  · intro hp
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro i
    simp [warning_set, Finset.mem_filter, Finset.mem_univ, not_or, not_lt, hp i]

theorem warning_dimension_violated (i : Fin n) (h : i ∈ warning_set lo hi p) :
    ¬(lo i ≤ p i ∧ p i ≤ hi i) := by
  simp only [warning_set, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases h with h1 | h2
  · intro ⟨hl, _⟩; exact not_le_of_lt h1 hl
  · intro ⟨_, hr⟩; exact not_le_of_lt h2 hr

instance in_regime_decidable : Decidable (in_regime lo hi p) := by
  classical
  dsimp [in_regime]
  infer_instance

#print axioms warnings_empty_iff_in_regime

end UMST
