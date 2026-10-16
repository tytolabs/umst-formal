-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: Culture/CarryingCapacity.lean

  The carrying capacity of a culture (the Game-of-Life sandbox's concurrency cap) as a consequence of the one predicate
  `SecondLaw`. Over a window of `T > 0` ticks:

  * an age cap (every life lasts at most `τ` ticks) bounds the live count summed over the ticks by `τ` times the lives
    the window holds, those that died in it (`D_T`) and those alive at its end (`N_T`):
    `Σ_t N_t ≤ τ (D_T + N_T)` (`liveTicks_le`);
  * each death erases one bit of its cell's record; the erase case makes that cost at least `ln 2` (units of `k_B T`)
    per bit, the measure-feedback case recovers at most the fraction `i` of it, and the supplied power `W` per tick
    pays the rest: `D_T ln 2 (1 − i) ≤ T W` (`deathCost_le`, stated over any field with `ln 2` a parameter `ℓ`;
    `deathCost_le_of_secondLaw` derives its premises from `SecondLaw` over ℝ);
  * so the mean live count obeys `N̄ ≤ τ (W / (ℓ (1 − i)) + N_T / T)` (`meanLive_le`), and with a rational enclosure
    `ℓ_lo ≤ ℓ` the same bound holds with `ℓ_lo` (`meanLive_le_of_enclosure`); `Real.log 2` lies in
    `[0.6931471803, 0.6931471808]` (`log_two_mem_enclosure`).

  Zero `axiom`, zero `sorry`.
-/

import Mathlib.Data.Complex.ExponentialBounds
import CostOfInformation

open Real UMST.LandauerLaw UMST.ProcessFamily UMST.InfoTheory UMST.InfoTheory.JointDist

namespace UMST.Culture.CarryingCapacity

section Field

variable {α : Type*} [LinearOrderedField α]

/-- The live count summed over the window's ticks is the sum of the lives' durations within it. -/
def liveTicks (durations : List α) : α := durations.sum

/-- **Age cap**: lives of at most `τ` ticks give at most `τ` live ticks each. -/
theorem liveTicks_le_length (τ : α) (durations : List α) (h : ∀ d ∈ durations, d ≤ τ) :
    liveTicks durations ≤ τ * durations.length := by
  induction durations with
  | nil => simp [liveTicks]
  | cons d ds ih =>
    have hd := h d (List.mem_cons_self d ds)
    have hds := ih (fun e he => h e (List.mem_cons_of_mem d he))
    simp only [liveTicks, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at hds ⊢
    linarith

/-- **Age cap over a window**: every life in the window either died in it or is alive at its end, so
    `Σ_t N_t ≤ τ (D_T + N_T)`. -/
theorem liveTicks_le (τ : α) (dead alive : List α) (h : ∀ d ∈ dead ++ alive, d ≤ τ) :
    liveTicks (dead ++ alive) ≤ τ * ((dead.length : α) + alive.length) := by
  have := liveTicks_le_length τ (dead ++ alive) h
  rw [List.length_append, Nat.cast_add] at this
  exact this

/-- **Death cost**: erasure of `D` bits costing at least `D ℓ`, recovery of at most `i D ℓ`, and the net paid by `T W`
    give `D ℓ (1 − i) ≤ T W`. -/
theorem deathCost_le {D ℓ i T W Werase Wrec : α} (herase : D * ℓ ≤ Werase) (hrec : Wrec ≤ i * (D * ℓ))
    (hbudget : Werase - Wrec ≤ T * W) : D * ℓ * (1 - i) ≤ T * W := by
  nlinarith

/-- **The carrying capacity**: the mean live count over the window obeys `N̄ ≤ τ (W / (ℓ (1 − i)) + N_T / T)`. -/
theorem meanLive_le {τ T W ℓ i : α} (dead alive : List α) (hτ : 0 ≤ τ) (hT : 0 < T) (hℓ : 0 < ℓ) (hi : i < 1)
    (hage : ∀ d ∈ dead ++ alive, d ≤ τ) (hcost : (dead.length : α) * ℓ * (1 - i) ≤ T * W) :
    liveTicks (dead ++ alive) / T ≤ τ * (W / (ℓ * (1 - i)) + (alive.length : α) / T) := by
  have hk : 0 < ℓ * (1 - i) := mul_pos hℓ (by linarith)
  have hD : (dead.length : α) ≤ T * W / (ℓ * (1 - i)) := by
    rw [le_div_iff₀ hk]; linarith
  have hlive := liveTicks_le τ dead alive hage
  rw [div_le_iff₀ hT]
  have e : τ * (W / (ℓ * (1 - i)) + (alive.length : α) / T) * T =
      τ * (T * W / (ℓ * (1 - i)) + alive.length) := by
    field_simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left (add_le_add_right hD (alive.length : α)) hτ
  linarith

/-- **With a rational enclosure** `ℓ_lo ≤ ℓ` of `ln 2`, the bound holds with the enclosure's lower end. -/
theorem meanLive_le_of_enclosure {τ T W ℓ ℓlo i : α} (dead alive : List α) (hτ : 0 ≤ τ) (hT : 0 < T)
    (hlo : 0 < ℓlo) (hℓ : ℓlo ≤ ℓ) (hi : i < 1) (hW : 0 ≤ W)
    (hage : ∀ d ∈ dead ++ alive, d ≤ τ) (hcost : (dead.length : α) * ℓ * (1 - i) ≤ T * W) :
    liveTicks (dead ++ alive) / T ≤ τ * (W / (ℓlo * (1 - i)) + (alive.length : α) / T) := by
  have h := meanLive_le dead alive hτ hT (lt_of_lt_of_le hlo hℓ) hi hage hcost
  have hi' : 0 < 1 - i := by linarith
  have hmono : W / (ℓ * (1 - i)) ≤ W / (ℓlo * (1 - i)) :=
    div_le_div_of_nonneg_left hW (mul_pos hlo hi') (mul_le_mul_of_nonneg_right hℓ hi'.le)
  have := mul_le_mul_of_nonneg_left (add_le_add_right hmono ((alive.length : α) / T)) hτ
  linarith

end Field

/-- `ln 2` lies in the rational enclosure `[0.6931471803, 0.6931471808]`. -/
theorem log_two_mem_enclosure : (0.6931471803 : ℝ) ≤ log 2 ∧ log 2 ≤ 0.6931471808 :=
  ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

/-- **The death cost from `SecondLaw`**: an erasure of the `D` dead cells' bits obeying the erase case, a recovery
    obeying the measure-feedback case at no free-energy change against a record carrying at most the fraction `i` of
    those bits, and a supplied work `T W` (units of `k_B` times kelvin, per tick at the bath temperature) that pays the
    net give `D ln 2 (1 − i) ≤ T W / T_bath`. -/
theorem deathCost_le_of_secondLaw (b : HeatBath) (Werase : ℝ) (D : ℕ) (f : FeedbackProcess) {n m : ℕ}
    (J : JointDist n m) (i T W : ℝ) (hbath : f.bath = b) (hF : f.deltaFreeEnergy = 0)
    (hI : mutualInformation J ≤ i * (D * log 2))
    (herase : SecondLaw (.erase ⟨b, Werase⟩)
      (.transformation (uniformDist (2 ^ D) (pow_pos two_pos D)) (diracDist (0 : Fin (2 ^ D)))))
    (hrec : SecondLaw (.measureFeedback f) (.feedback J))
    (hbudget : kB * Werase - f.extWork ≤ kB * T * W) :
    D * log 2 * (1 - i) ≤ T * W / b.bathTemp.val := by
  have hT := b.bathTemp.property
  have he := UMST.CostOfInformation.bitErasure_cost b Werase D herase
  have hr : f.extWork ≤ -f.deltaFreeEnergy + kB * f.bath.bathTemp.val * mutualInformation J := hrec
  rw [hF, hbath, neg_zero, zero_add] at hr
  have hkT : 0 < kB * b.bathTemp.val := mul_pos kB_pos hT
  have hr' : f.extWork ≤ kB * b.bathTemp.val * (i * (D * log 2)) :=
    le_trans hr (mul_le_mul_of_nonneg_left hI hkT.le)
  rw [le_div_iff₀ hT]
  have key : kB * b.bathTemp.val * (D * log 2 * (1 - i)) ≤ kB * T * W := by nlinarith
  have : kB * (D * log 2 * (1 - i) * b.bathTemp.val) ≤ kB * (T * W) := by nlinarith
  exact le_of_mul_le_mul_left this kB_pos

end UMST.Culture.CarryingCapacity
