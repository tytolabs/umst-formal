-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Concrete/PowersCapillary.lean

  The capillary porosity of Powers' volume model (`Concrete.PowersVolume`) in closed form, and the rounded
  coefficients that runtime closures carry.

  * The capillary pores of a paste, capillary water together with chemical-shrinkage voids, fill the fraction
    `(w − (w/c)_s·α) / (w + ρ_w/ρ_c)` of the paste at water-cement ratio `w` and degree of hydration `α`
    (`capillaryPorosity_eq`), with `(w/c)_s = 0.356` (`Constants.SI.criticalWcSpace`) and `ρ_w/ρ_c = 1/3.15`.
  * The closure `(w − 0.36·α) / (w + 0.32)` rounds both coefficients to two decimals
    (`powersCapillaryWaterCoeff_value`, `powersPasteOffsetCoeff_value`); each rounded coefficient lies within
    1/200 of the derived one (`powersCapillaryWaterCoeff_err`, `powersPasteOffsetCoeff_err`).
  * The cement volume per unit water volume at unit water-cement ratio, `ρ_w/ρ_c`, rounds to 0.317 at three
    decimals (`powersCementVolumeCoeff_value`).

  The coefficients are derived from the cited water parameters and densities of `Constants.SI`; no new
  physical assumption enters.
-/

import Concrete.PowersVolume
import Mathlib.Tactic

open UMST.Constants.SI UMST.Concrete.PowersVolume

namespace UMST.Concrete.PowersCapillary

/-- Capillary pore fraction of the paste: capillary water plus chemical-shrinkage voids, at water-cement ratio `w`
    and degree of hydration `α`. -/
def capillaryPorosity (w α : ℚ) : ℚ :=
  capillaryWater (waterFraction w) α + shrinkage (waterFraction w) α

/-- **Capillary porosity in closed form**: `(w − (w/c)_s·α) / (w + 1/(ρ_c/ρ_w))`. -/
theorem capillaryPorosity_eq (w α : ℚ) (hw : 0 ≤ w) :
    capillaryPorosity w α = (w - criticalWcSpace * α) / (w + 1 / densityRatio) := by
  unfold capillaryPorosity capillaryWater shrinkage waterFraction
  rw [capillaryConsumption_value, shrinkageVolume_value, densityRatio_value, criticalWcSpace_value]
  have h1 : (0 : ℚ) < w * (63 / 20) + 1 := by positivity
  have h2 : (0 : ℚ) < w + 1 / (63 / 20) := by positivity
  field_simp
  ring

/-- `x` rounded to two decimals. -/
def round2 (x : ℚ) : ℚ := (round (100 * x) : ℚ) / 100

/-- `x` rounded to three decimals. -/
def round3 (x : ℚ) : ℚ := (round (1000 * x) : ℚ) / 1000

/-- The capillary-water coefficient of the rounded closure: `(w/c)_s` at two decimals. -/
def powersCapillaryWaterCoeff : ℚ := round2 criticalWcSpace

/-- The paste-offset coefficient of the rounded closure: `ρ_w/ρ_c` at two decimals. -/
def powersPasteOffsetCoeff : ℚ := round2 (1 / densityRatio)

/-- The cement volume per unit water volume at unit water-cement ratio: `ρ_w/ρ_c` at three decimals. -/
def powersCementVolumeCoeff : ℚ := round3 (1 / densityRatio)

theorem powersCapillaryWaterCoeff_value : powersCapillaryWaterCoeff = 36 / 100 := by
  have h : round ((100 : ℚ) * (89 / 250)) = 36 := by
    rw [round_eq, Int.floor_eq_iff]; norm_num
  unfold powersCapillaryWaterCoeff round2
  rw [criticalWcSpace_value, h]; norm_num

theorem powersPasteOffsetCoeff_value : powersPasteOffsetCoeff = 32 / 100 := by
  have h : round ((100 : ℚ) * (1 / (63 / 20))) = 32 := by
    rw [round_eq, Int.floor_eq_iff]; norm_num
  unfold powersPasteOffsetCoeff round2
  rw [densityRatio_value, h]; norm_num

theorem powersCementVolumeCoeff_value : powersCementVolumeCoeff = 317 / 1000 := by
  have h : round ((1000 : ℚ) * (1 / (63 / 20))) = 317 := by
    rw [round_eq, Int.floor_eq_iff]; norm_num
  unfold powersCementVolumeCoeff round3
  rw [densityRatio_value, h]; norm_num

/-- The rounded capillary-water coefficient lies within 1/200 of `(w/c)_s`. -/
theorem powersCapillaryWaterCoeff_err : |powersCapillaryWaterCoeff - criticalWcSpace| ≤ 1 / 200 := by
  rw [powersCapillaryWaterCoeff_value, criticalWcSpace_value, abs_le]; constructor <;> norm_num

/-- The rounded paste-offset coefficient lies within 1/200 of `ρ_w/ρ_c`. -/
theorem powersPasteOffsetCoeff_err : |powersPasteOffsetCoeff - 1 / densityRatio| ≤ 1 / 200 := by
  rw [powersPasteOffsetCoeff_value, densityRatio_value, abs_le]; constructor <;> norm_num

end UMST.Concrete.PowersCapillary
