/-
  UMST-Formal: LandauerEinsteinBridge.lean

  Standalone mathematical artifact: combine the Landauer thermal scale `k_B T ln 2`
  (energy, per chosen convention for one logical bit) with special-relativistic
  mass–energy `E = m c²` to obtain
  `m_eq(T) = (k_B T ln 2) / c²`.

  **SI values.**  `kBoltzmannSI` and `speedOfLightSI` are the exact SI definitions.
  `Real.log 2` is Mathlib’s logarithm.  Coarse and tight numeric brackets at `T = 300`
  use Mathlib bounds on `log 2`.

  **Explicitly not a theorem in this file:** (i) that physical bit erasure must cost
  at least `k_B T ln 2` in any particular device model (thermodynamic Landauer
  statement); (ii) any identification of `m_eq` with measured gravitational
  effects beyond applying `E = mc²` to the defined energy scale.

  Coq counterpart: `Coq/LandauerEinsteinBridge.v` (parameters `kB_SI`, `c_SI`, `ln2` +
  positivity axioms).
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.ExponentialBounds

open Real

/-- SI 2019 exact Boltzmann constant `k_B = 1.380649 × 10⁻²³` J/K (rational real). -/
noncomputable def kBoltzmannSI : ℝ :=
  (1380649 : ℝ) / (10 : ℝ) ^ 29

/-- SI exact speed of light in vacuum `c = 299792458` m/s. -/
noncomputable def speedOfLightSI : ℝ :=
  (299792458 : ℝ)

lemma kBoltzmannSI_pos : 0 < kBoltzmannSI := by
  unfold kBoltzmannSI
  have h10 : 0 < (10 : ℝ) ^ 29 := by positivity
  exact div_pos (by norm_num) h10

lemma speedOfLightSI_pos : 0 < speedOfLightSI := by
  unfold speedOfLightSI
  norm_num

lemma speedOfLightSI_sq_pos : 0 < speedOfLightSI ^ 2 :=
  sq_pos_of_pos speedOfLightSI_pos

/-- Energy scale `k_B T ln 2` at temperature `T` (kelvin). -/
noncomputable def landauerBitEnergy (T : ℝ) : ℝ :=
  kBoltzmannSI * T * log 2

/-- Mass equivalent `(k_B T ln 2) / c²` (kg) from `E = m c²`. -/
noncomputable def massEquivalent (T : ℝ) : ℝ :=
  landauerBitEnergy T / speedOfLightSI ^ 2

lemma landauerBitEnergy_pos {T : ℝ} (hT : 0 < T) : 0 < landauerBitEnergy T := by
  unfold landauerBitEnergy
  have hlog : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  exact mul_pos (mul_pos kBoltzmannSI_pos hT) hlog

lemma massEquivalent_pos {T : ℝ} (hT : 0 < T) : 0 < massEquivalent T := by
  unfold massEquivalent
  exact div_pos (landauerBitEnergy_pos hT) speedOfLightSI_sq_pos

/-- Homogeneity in temperature: `m_eq(a·T) = a · m_eq(T)` for fixed SI constants. -/
theorem massEquivalent_linear (T₁ T₂ a : ℝ) (_ha : 0 < a) (hT : T₂ = a * T₁) :
    massEquivalent T₂ = a * massEquivalent T₁ := by
  subst hT
  unfold massEquivalent landauerBitEnergy
  rw [show kBoltzmannSI * (a * T₁) * log 2 = a * (kBoltzmannSI * T₁ * log 2) by ring]
  rw [mul_div_assoc]

/-! ### Numeric bracket at `T = 300` K

Coarse bracket from `log_two_gt_d9` / `log_two_lt_d9`.  Reference value ≈ 3.194×10⁻³⁸ kg
lies inside the tight bracket below.
-/

/-- Lower/upper rational approximants matching `log_two_gt_d9` / `log_two_lt_d9`. -/
private lemma log_two_lo_val : (6931471803 : ℝ) / 10 ^ 10 = (0.6931471803 : ℝ) := by norm_num

private lemma log_two_hi_val : (6931471808 : ℝ) / 10 ^ 10 = (0.6931471808 : ℝ) := by norm_num

private lemma log_two_lo_lt : (6931471803 : ℝ) / 10 ^ 10 < log 2 := by
  rw [log_two_lo_val]
  exact log_two_gt_d9

private lemma log_two_hi_lt : log 2 < (6931471808 : ℝ) / 10 ^ 10 := by
  rw [log_two_hi_val]
  exact log_two_lt_d9

theorem massEquivalent_three_hundred_gt_three_point_one_e_neg_thirtyEight :
    (318 : ℝ) / 10 ^ 40 < massEquivalent 300 := by
  have hpos : 0 < kBoltzmannSI * (300 : ℝ) := mul_pos kBoltzmannSI_pos (by norm_num)
  have hnum :
      kBoltzmannSI * (300 : ℝ) * ((6931471803 : ℝ) / 10 ^ 10) <
        kBoltzmannSI * (300 : ℝ) * log 2 :=
    mul_lt_mul_of_pos_left log_two_lo_lt hpos
  have hdiv :
      (kBoltzmannSI * (300 : ℝ) * ((6931471803 : ℝ) / 10 ^ 10)) / speedOfLightSI ^ 2 <
        massEquivalent 300 := by
    unfold massEquivalent landauerBitEnergy
    exact div_lt_div_of_pos_right hnum speedOfLightSI_sq_pos
  refine lt_trans ?_ hdiv
  unfold kBoltzmannSI speedOfLightSI
  norm_num

theorem massEquivalent_three_hundred_lt_three_point_two_e_neg_thirtyEight :
    massEquivalent 300 < (320 : ℝ) / 10 ^ 40 := by
  have hpos : 0 < kBoltzmannSI * (300 : ℝ) := mul_pos kBoltzmannSI_pos (by norm_num)
  have hnum :
      kBoltzmannSI * (300 : ℝ) * log 2 <
        kBoltzmannSI * (300 : ℝ) * ((6931471808 : ℝ) / 10 ^ 10) :=
    mul_lt_mul_of_pos_left log_two_hi_lt hpos
  have hdiv :
      massEquivalent 300 <
        (kBoltzmannSI * (300 : ℝ) * ((6931471808 : ℝ) / 10 ^ 10)) / speedOfLightSI ^ 2 := by
    unfold massEquivalent landauerBitEnergy
    exact div_lt_div_of_pos_right hnum speedOfLightSI_sq_pos
  refine lt_trans hdiv ?_
  unfold kBoltzmannSI speedOfLightSI
  norm_num

/-- Combined coarse interval at 300 K. -/
theorem massEquivalent_three_hundred_interval :
    (318 : ℝ) / 10 ^ 40 < massEquivalent 300 ∧
      massEquivalent 300 < (320 : ℝ) / 10 ^ 40 :=
  ⟨massEquivalent_three_hundred_gt_three_point_one_e_neg_thirtyEight,
    massEquivalent_three_hundred_lt_three_point_two_e_neg_thirtyEight⟩

/-! ### Tight bracket (`log_two_near_10`: |ln 2 − 287209/414355| ≤ 10⁻¹⁰)

Rational `r ± ε` propagated through exact SI `k_B`, `c`, and `T = 300`.
-/

private lemma log_two_ge_r_sub_eps :
    (287209 : ℝ) / 414355 - 1 / 10 ^ 10 ≤ log 2 := by
  have h := (abs_sub_le_iff.mp log_two_near_10).2
  linarith

private lemma log_two_le_r_add_eps :
    log 2 ≤ (287209 : ℝ) / 414355 + 1 / 10 ^ 10 := by
  have h := (abs_sub_le_iff.mp log_two_near_10).1
  linarith

private lemma kB_mul_three_hundred_nonneg : 0 ≤ kBoltzmannSI * (300 : ℝ) :=
  le_of_lt (mul_pos kBoltzmannSI_pos (by norm_num))

theorem massEquivalent_three_hundred_gt_tight :
    (319439481694054 : ℝ) / 10 ^ 52 < massEquivalent 300 := by
  have hnum :
      kBoltzmannSI * (300 : ℝ) * ((287209 : ℝ) / 414355 - 1 / 10 ^ 10) ≤
        kBoltzmannSI * (300 : ℝ) * log 2 :=
    mul_le_mul_of_nonneg_left log_two_ge_r_sub_eps kB_mul_three_hundred_nonneg
  have hdiv :
      (kBoltzmannSI * (300 : ℝ) * ((287209 : ℝ) / 414355 - 1 / 10 ^ 10)) / speedOfLightSI ^ 2 ≤
        massEquivalent 300 := by
    unfold massEquivalent landauerBitEnergy
    exact (div_le_div_iff_of_pos_right speedOfLightSI_sq_pos).mpr hnum
  refine lt_of_lt_of_le ?_ hdiv
  unfold kBoltzmannSI speedOfLightSI
  norm_num

theorem massEquivalent_three_hundred_lt_tight :
    massEquivalent 300 < (319439481786228 : ℝ) / 10 ^ 52 := by
  have hnum :
      kBoltzmannSI * (300 : ℝ) * log 2 ≤
        kBoltzmannSI * (300 : ℝ) * ((287209 : ℝ) / 414355 + 1 / 10 ^ 10) :=
    mul_le_mul_of_nonneg_left log_two_le_r_add_eps kB_mul_three_hundred_nonneg
  have hdiv :
      massEquivalent 300 ≤
        (kBoltzmannSI * (300 : ℝ) * ((287209 : ℝ) / 414355 + 1 / 10 ^ 10)) / speedOfLightSI ^ 2 := by
    unfold massEquivalent landauerBitEnergy
    exact (div_le_div_iff_of_pos_right speedOfLightSI_sq_pos).mpr hnum
  have hstrict :
      (kBoltzmannSI * (300 : ℝ) * ((287209 : ℝ) / 414355 + 1 / 10 ^ 10)) / speedOfLightSI ^ 2 <
        (319439481786228 : ℝ) / 10 ^ 52 := by
    unfold kBoltzmannSI speedOfLightSI
    norm_num
  exact lt_of_le_of_lt hdiv hstrict

/-- Tight machine-checked interval at 300 K from `log_two_near_10`. -/
theorem massEquivalent_three_hundred_interval_tight :
    (319439481694054 : ℝ) / 10 ^ 52 < massEquivalent 300 ∧
      massEquivalent 300 < (319439481786228 : ℝ) / 10 ^ 52 :=
  ⟨massEquivalent_three_hundred_gt_tight, massEquivalent_three_hundred_lt_tight⟩
