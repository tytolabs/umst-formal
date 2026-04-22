/-
  UMST-Formal: Dignity.lean

  Thermodynamic–epistemic **dignity** scalar `d ∈ [0, d_max]` with `d_max = 10`, matching the
  egoff runtime convention (`closed_loop::dignity_scalar = rcc · 10`, `interpret::dignity_band`).
  Landauer floor for **honest spend** uses `LandauerEinsteinBridge.landauerBitEnergy T` (J per bit).

  Reduction vs egoff §14bis / N3 operator spec:
  - **Bounds** (`d_max`, nonnegativity) encode the UX band `[0,10]`.
  - **Honest spend** (`honest_spend`) encodes “entropy spent covers Landauer cost for claimed MI bits”.
  - **`dignity_step`** increases dignity only on honest claims (by the MI increment, capped);
    dishonest steps leave dignity fixed — deception cannot **raise** the scalar.
  - **`dignity_scalar_matches_rcc_one_minus_epistemic_gap`** is the algebraic bind to the
    `InformationCostIdentity`-style identity `rcc + epistemic = 1` (stated here as a hypothesis on
    reals; the double-slit formal module is not in this lake closure).

  No new physical axioms beyond imports from `LandauerEinsteinBridge`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic
import LandauerEinsteinBridge

set_option linter.dupNamespace false

open Classical

namespace UMST.Formal.Dignity

noncomputable def d_max : ℝ := 10

/-- SI Landauer bit-energy scale `k_B T ln 2` (J/bit) at temperature `T` (K). -/
noncomputable def landauer_joules_per_bit (T : ℝ) : ℝ :=
  landauerBitEnergy T

lemma landauer_joules_per_bit_pos {T : ℝ} (hT : 0 < T) : 0 < landauer_joules_per_bit T :=
  landauerBitEnergy_pos hT

/-- Witnessed dignity scalar in `[0, d_max]`. -/
structure Dignity where
  value   : ℝ
  nonneg  : 0 ≤ value
  bounded : value ≤ d_max

/-- Claimed epistemic MI gain (bits) and measured energy spend (J), both nonnegative. -/
structure DignityClaim where
  delta_mi_bits   : ℝ
  delta_energy_j  : ℝ
  hmi             : 0 ≤ delta_mi_bits
  he              : 0 ≤ delta_energy_j

/-- Honest spend: Landauer floor for claimed bits is covered by dissipated/measured energy. -/
def honest_spend (T : ℝ) (c : DignityClaim) : Prop :=
  landauer_joules_per_bit T * c.delta_mi_bits ≤ c.delta_energy_j

/-- Smart constructor: `some` iff `0 ≤ x ≤ d_max`. -/
noncomputable def tryDignity (x : ℝ) : Option Dignity :=
  if h0 : 0 ≤ x then
    if h1 : x ≤ d_max then
      some ⟨x, h0, h1⟩
    else
      none
  else
    none

theorem tryDignity_eq_none_of_neg {x : ℝ} (hx : x < 0) : tryDignity x = none := by
  simp [tryDignity, not_le.mpr hx]

theorem tryDignity_eq_none_of_gt {x : ℝ} (h0 : 0 ≤ x) (h1 : d_max < x) : tryDignity x = none := by
  simp [tryDignity, h0, not_le.mpr h1]

theorem tryDignity_eq_some_iff (x : ℝ) :
    (∃ d : Dignity, tryDignity x = some d ∧ d.value = x) ↔ 0 ≤ x ∧ x ≤ d_max := by
  constructor
  · rintro ⟨d, h₁, h₂⟩
    have hx0 : 0 ≤ x := by
      by_contra h'
      have hx : x < 0 := not_le.mp h'
      rw [tryDignity_eq_none_of_neg hx] at h₁
      cases h₁
    have hx1 : x ≤ d_max := by
      by_contra h'
      have hgt : d_max < x := not_le.mp h'
      rw [tryDignity_eq_none_of_gt hx0 hgt] at h₁
      cases h₁
    exact ⟨hx0, hx1⟩
  · rintro ⟨hx0, hx1⟩
    refine ⟨⟨x, hx0, hx1⟩, ?_, rfl⟩
    simp [tryDignity, hx0, hx1]

/-- One-step update: on honest spend, add MI (capped at `d_max`); otherwise unchanged. -/
noncomputable def dignity_step (T : ℝ) (_hT : 0 < T) (d : Dignity) (c : DignityClaim) : Dignity :=
  if hh : honest_spend T c then
    let v : ℝ := min d_max (d.value + c.delta_mi_bits)
    have hv0 : 0 ≤ v := by
      refine le_min_iff.mpr ⟨?_, ?_⟩
      · show (0 : ℝ) ≤ d_max
        unfold d_max
        norm_num
      · exact le_trans d.nonneg (le_add_of_nonneg_right c.hmi)
    have hv1 : v ≤ d_max := min_le_left _ _
    ⟨v, hv0, hv1⟩
  else
    d

theorem dignity_step_honest_eq {T : ℝ} (hT : 0 < T) (d : Dignity) (c : DignityClaim)
    (hh : honest_spend T c) :
    (dignity_step T hT d c).value = min d_max (d.value + c.delta_mi_bits) := by
  simp [dignity_step, hh]

theorem dignity_step_dishonest_eq {T : ℝ} (hT : 0 < T) (d : Dignity) (c : DignityClaim)
    (hh : ¬ honest_spend T c) : dignity_step T hT d c = d := by
  simp [dignity_step, hh]

/-- On honest spend, dignity does not decrease (non-erosion by honest work). -/
theorem dignity_non_eroded_by_honest_work {T : ℝ} (hT : 0 < T) (d : Dignity) (c : DignityClaim)
    (hh : honest_spend T c) : d.value ≤ (dignity_step T hT d c).value := by
  rw [dignity_step_honest_eq hT d c hh]
  exact le_min_iff.mpr ⟨d.bounded, le_add_of_nonneg_right c.hmi⟩

/-- Monotonicity in claimed MI when both steps are honest. -/
theorem dignity_monotone_under_mi_gain {T : ℝ} (hT : 0 < T) (d : Dignity) (c₁ c₂ : DignityClaim)
    (h₁ : honest_spend T c₁) (h₂ : honest_spend T c₂) (hmi : c₁.delta_mi_bits ≤ c₂.delta_mi_bits) :
    (dignity_step T hT d c₁).value ≤ (dignity_step T hT d c₂).value := by
  rw [dignity_step_honest_eq hT d c₁ h₁, dignity_step_honest_eq hT d c₂ h₂]
  refine min_le_min ?_ ?_
  · rfl
  · exact add_le_add_left hmi d.value

/-- Sub-Landauer claims do not increase dignity (fixed point under dishonest branch). -/
theorem dignity_flags_sub_landauer_claims {T : ℝ} (hT : 0 < T) (d : Dignity) (c : DignityClaim)
    (hh : ¬ honest_spend T c) : (dignity_step T hT d c).value = d.value := by
  simp [dignity_step_dishonest_eq hT d c hh]

/-- Convex combination of two dignities stays in `[0, d_max]` (two-agent averaging). -/
noncomputable def dignity_avg (t : ℝ) (d₁ d₂ : Dignity) (ht : 0 ≤ t ∧ t ≤ 1) : Dignity where
  value := t * d₁.value + (1 - t) * d₂.value
  nonneg := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    exact add_nonneg (mul_nonneg ht0 d₁.nonneg) (mul_nonneg ht1 d₂.nonneg)
  bounded := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have h1 : t * d₁.value ≤ t * d_max :=
      mul_le_mul_of_nonneg_left d₁.bounded ht0
    have h2 : (1 - t) * d₂.value ≤ (1 - t) * d_max :=
      mul_le_mul_of_nonneg_left d₂.bounded ht1
    have hsum : t * d_max + (1 - t) * d_max = d_max := by ring
    calc
      t * d₁.value + (1 - t) * d₂.value ≤ t * d_max + (1 - t) * d_max := add_le_add h1 h2
      _ = d_max := hsum

theorem dignity_avg_value (t : ℝ) (d₁ d₂ : Dignity) (ht : 0 ≤ t ∧ t ≤ 1) :
    (dignity_avg t d₁ d₂ ht).value = t * d₁.value + (1 - t) * d₂.value :=
  rfl

/-- List-sum of dignity scalars is nonnegative (stacked nonnegative epistemic credits). -/
theorem dignity_list_values_sum_nonneg (ds : List Dignity) :
    0 ≤ (List.map (fun d : Dignity => d.value) ds).sum := by
  refine List.sum_nonneg ?_
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨d, -, rfl⟩ := hy
  exact d.nonneg

/-- RCC in `[0,1]` maps to the legacy egoff dignity scale `10 · rcc`. -/
theorem dignity_of_rcc_try {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ d : Dignity, tryDignity (d_max * r) = some d ∧ d.value = d_max * r := by
  have hx0 : 0 ≤ d_max * r := mul_nonneg (show (0 : ℝ) ≤ d_max by unfold d_max; norm_num) hr0
  have hx1 : d_max * r ≤ d_max := by
    have hd0 : (0 : ℝ) ≤ d_max := by unfold d_max; norm_num
    calc
      d_max * r ≤ d_max * (1 : ℝ) := mul_le_mul_of_nonneg_left hr1 hd0
      _ = d_max := by ring
  refine ⟨{ value := d_max * r, nonneg := hx0, bounded := hx1 }, ?_⟩
  simp [tryDignity, hx0, hx1]

/-- Bind to the `rcc + epistemic = 1` bookkeeping: `10·rcc = 10·(1 - epistemic_gap)` when `rcc + e = 1`. -/
theorem dignity_scalar_matches_rcc_one_minus_epistemic_gap (rcc epistemic_gap : ℝ)
    (_hrcc : 0 ≤ rcc ∧ rcc ≤ 1) (_he : 0 ≤ epistemic_gap ∧ epistemic_gap ≤ 1)
    (hsum : rcc + epistemic_gap = 1) : d_max * rcc = d_max * (1 - epistemic_gap) := by
  have : rcc = 1 - epistemic_gap := by linarith
  simp [this]

end UMST.Formal.Dignity
