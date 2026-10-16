-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: UnfoldTermination.lean

  Law L-E of the unfold solver family (`workspace/docs/blueprints/UMST_UNFOLD_ADAPTIVE_HIERARCHY.md`, section 12) for
  the plain `unfold`: a run whose every step posts a spend of at least `ε > 0` and whose measured spends sum to at
  most the budget `B` takes at most `B / ε` steps, so at most `⌊B / ε⌋` (`steps_mul_le`, `steps_le_div`,
  `steps_le_floor`). The floor comes from the erase case of `SecondLaw`: a step that erases at least `b` bits at the
  bath temperature `T` spends at least `b k_B T ln 2`, and with the rational lower enclosure
  `0.6931471803 < ln 2` at least `ε_lo = b k_B T · 0.6931471803` (`erase_spend_ge_enclosure`), so an unfold whose
  steps are such erasures stops within `⌊B / ε_lo⌋` steps (`unfold_terminates_of_secondLaw`).

  Zero `axiom`, zero `sorry`.
-/

import Mathlib.Data.Complex.ExponentialBounds
import UnfoldKleisli

open Real UMST.LandauerLaw UMST.ProcessFamily UMST.InfoTheory

namespace UMST.UnfoldTermination

section Field

variable {α : Type} [LinearOrderedField α]

/-- **L-E**: spends each at least `ε` summing to at most `B` number at most `B / ε` (cleared form `n ε ≤ B`). -/
theorem steps_mul_le (ε B : α) (spends : List α) (hfloor : ∀ w ∈ spends, ε ≤ w) (hB : spends.sum ≤ B) :
    (spends.length : α) * ε ≤ B := by
  have key : ∀ l : List α, (∀ w ∈ l, ε ≤ w) → (l.length : α) * ε ≤ l.sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons w l ih =>
      intro h
      have hw := h w (List.mem_cons_self w l)
      have hl := ih fun v hv => h v (List.mem_cons_of_mem w hv)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons]
      linarith
  exact le_trans (key spends hfloor) hB

/-- **L-E** with the division: at most `B / ε` steps. -/
theorem steps_le_div {ε B : α} (hε : 0 < ε) (spends : List α) (hfloor : ∀ w ∈ spends, ε ≤ w)
    (hB : spends.sum ≤ B) : (spends.length : α) ≤ B / ε := by
  rw [le_div_iff₀ hε]
  exact steps_mul_le ε B spends hfloor hB

/-- **L-E** as a step count: at most `⌊B / ε⌋` steps. -/
theorem steps_le_floor [FloorSemiring α] {ε B : α} (hε : 0 < ε) (spends : List α)
    (hfloor : ∀ w ∈ spends, ε ≤ w) (hB : spends.sum ≤ B) : spends.length ≤ ⌊B / ε⌋₊ :=
  Nat.le_floor (steps_le_div hε spends hfloor hB)

end Field

/-- The lower end of the rational enclosure of `ln 2` (Mathlib `Real.log_two_gt_d9`). -/
def ln2Lower : ℚ := 6931471803 / 10000000000

theorem ln2Lower_lt_log_two : ((ln2Lower : ℚ) : ℝ) < log 2 := by
  have h := Real.log_two_gt_d9
  have e : ((ln2Lower : ℚ) : ℝ) = 0.6931471803 := by norm_num [ln2Lower]
  rw [e]; exact h

/-- **The Landauer floor enclosed from below**: an erasure of `bits ≥ b` bits obeying the erase case of `SecondLaw`
    spends at least `b k_B T ln2Lower`. -/
theorem erase_spend_ge_enclosure (bath : HeatBath) (W : ℝ) (b bits : ℕ) (hb : b ≤ bits)
    (h : SecondLaw (.erase ⟨bath, W⟩)
      (.transformation (uniformDist (2 ^ bits) (pow_pos two_pos bits)) (diracDist (0 : Fin (2 ^ bits))))) :
    (b : ℝ) * (kB * bath.bathTemp.val * (ln2Lower : ℝ)) ≤ kB * W := by
  have hc := UMST.CostOfInformation.bitErasure_cost bath W bits h
  have hkT : 0 < kB * bath.bathTemp.val := mul_pos kB_pos bath.bathTemp.property
  have hl := ln2Lower_lt_log_two
  have hlo : (0 : ℝ) ≤ (ln2Lower : ℝ) := by norm_num [ln2Lower]
  have hbb : (b : ℝ) ≤ bits := by exact_mod_cast hb
  have h1 : kB * bath.bathTemp.val * (ln2Lower : ℝ) ≤ kB * bath.bathTemp.val * log 2 :=
    mul_le_mul_of_nonneg_left hl.le hkT.le
  have h2 : (0 : ℝ) ≤ kB * bath.bathTemp.val * (ln2Lower : ℝ) := mul_nonneg hkT.le hlo
  calc (b : ℝ) * (kB * bath.bathTemp.val * (ln2Lower : ℝ))
      ≤ (bits : ℝ) * (kB * bath.bathTemp.val * (ln2Lower : ℝ)) := mul_le_mul_of_nonneg_right hbb h2
    _ ≤ (bits : ℝ) * (kB * bath.bathTemp.val * log 2) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ ≤ kB * W := hc

/-- **L-E from `SecondLaw`**: an unfold whose every step is an erasure of at least `b > 0` bits obeying the erase
    case, and whose measured spends `k_B W` sum to at most `B`, stops within `⌊B / (b k_B T ln2Lower)⌋` steps. -/
theorem unfold_terminates_of_secondLaw (bath : HeatBath) (b : ℕ) (hb : 0 < b) (B : ℝ) (steps : List (ℝ × ℕ))
    (hsl : ∀ p ∈ steps, b ≤ p.2 ∧ SecondLaw (.erase ⟨bath, p.1⟩)
      (.transformation (uniformDist (2 ^ p.2) (pow_pos two_pos p.2)) (diracDist (0 : Fin (2 ^ p.2)))))
    (hB : (steps.map fun p => kB * p.1).sum ≤ B) :
    steps.length ≤ ⌊B / ((b : ℝ) * (kB * bath.bathTemp.val * (ln2Lower : ℝ)))⌋₊ := by
  have hε : 0 < (b : ℝ) * (kB * bath.bathTemp.val * (ln2Lower : ℝ)) := by
    have : (0 : ℝ) < (ln2Lower : ℝ) := by norm_num [ln2Lower]
    exact mul_pos (by exact_mod_cast hb) (mul_pos (mul_pos kB_pos bath.bathTemp.property) this)
  have h := steps_le_floor hε (steps.map fun p => kB * p.1) (by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    exact erase_spend_ge_enclosure bath p.1 b p.2 (hsl p hp).1 (hsl p hp).2) hB
  simpa using h

end UMST.UnfoldTermination
