-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Concrete/PowersVolume.lean

  Powers' volume model of a hydrating cement paste (Bentz, Irassar, Bucher and Weiss 2009, equation set 1), with
  its coefficients derived in `Constants.SI` from the cited water parameters (non-evaporable water, chemical
  shrinkage, gel water) and the density ratio. With `p` the initial volume fraction of water and `α` the degree
  of hydration, the paste holds cement, gel solids, gel water, capillary water and chemical-shrinkage voids.

  * The volumes always sum to one (`volume_balance`): the cited parameters conserve volume at every `p` and `α`.
  * At complete hydration the capillary water has the sign of `w − (w/c)*` with `(w/c)* = 0.42`
    (`capillaryWater_full_nonneg_iff`): below it sealed paste runs out of water.
  * Capillary water and shrinkage voids together have the sign of `w − (w/c)_s` with `(w/c)_s = 0.356`
    (`space_full_nonneg_iff`): below it the hydration products run out of space.

  Per unit volume of cement (`capillaryPerCement`, `spacePerCement`) both thresholds hold without division; these
  forms are stated identically in Lean, Coq, Agda and Haskell (formal_parity.json), and the paste fractions are
  them divided by the positive paste volume `w·d + 1` (`capillaryWater_full_eq`, `space_full_eq`).
-/

import Constants.SI
import Mathlib.Tactic

open UMST.Constants.SI

namespace UMST.Concrete.PowersVolume

/-- Initial volume fraction of water in a paste of water-cement ratio `w` (by mass). -/
def waterFraction (w : ℚ) : ℚ := w * densityRatio / (w * densityRatio + 1)

/-- Volume fraction of unreacted cement at initial water fraction `p` and degree of hydration `α`. -/
def cement (p α : ℚ) : ℚ := (1 - p) * (1 - α)

/-- Volume fraction of gel solids. -/
def gelSolids (p α : ℚ) : ℚ := gelSolidsVolume * (1 - p) * α

/-- Volume fraction of gel water. -/
def gelWaterV (p α : ℚ) : ℚ := gelWaterVolume * (1 - p) * α

/-- Volume fraction of capillary water. -/
def capillaryWater (p α : ℚ) : ℚ := p - capillaryConsumption * (1 - p) * α

/-- Volume fraction of chemical-shrinkage voids. -/
def shrinkage (p α : ℚ) : ℚ := shrinkageVolume * (1 - p) * α

/-- The coefficients conserve volume: gel solids, gel water and shrinkage voids replace the cement and capillary water
    consumed. -/
theorem coefficient_balance : gelSolidsVolume + gelWaterVolume + shrinkageVolume - capillaryConsumption = 1 := by
  rw [gelSolidsVolume_value, gelWaterVolume_value, shrinkageVolume_value, capillaryConsumption_value]; norm_num

/-- **Volume balance**: at every initial water fraction and degree of hydration the phases fill the paste. -/
theorem volume_balance (p α : ℚ) :
    cement p α + gelSolids p α + gelWaterV p α + capillaryWater p α + shrinkage p α = 1 := by
  have h := coefficient_balance
  unfold cement gelSolids gelWaterV capillaryWater shrinkage
  linear_combination (1 - p) * α * h

/-- Capillary water at complete hydration per unit volume of cement, for water-cement ratio `w`. -/
def capillaryPerCement (w : ℚ) : ℚ := w * densityRatio - capillaryConsumption

/-- Capillary water and shrinkage voids at complete hydration per unit volume of cement. -/
def spacePerCement (w : ℚ) : ℚ := capillaryPerCement w + shrinkageVolume

/-- **Sealed-curing threshold**, per unit volume of cement: capillary water remains exactly when `w ≥ 0.42`. -/
theorem capillaryPerCement_nonneg_iff (w : ℚ) : 0 ≤ capillaryPerCement w ↔ criticalWcSealed ≤ w := by
  unfold capillaryPerCement
  rw [capillaryConsumption_value, densityRatio_value, criticalWcSealed_value]
  constructor <;> intro h <;> linarith

/-- **Space threshold**, per unit volume of cement: the products fit exactly when `w ≥ 0.356`. -/
theorem spacePerCement_nonneg_iff (w : ℚ) : 0 ≤ spacePerCement w ↔ criticalWcSpace ≤ w := by
  unfold spacePerCement capillaryPerCement
  rw [capillaryConsumption_value, shrinkageVolume_value, densityRatio_value, criticalWcSpace_value]
  constructor <;> intro h <;> linarith

private lemma denom_pos {w : ℚ} (hw : 0 ≤ w) : 0 < w * densityRatio + 1 := by
  rw [densityRatio_value]; positivity

/-- Capillary water at complete hydration, in terms of the water-cement ratio. -/
theorem capillaryWater_full (w : ℚ) (hw : 0 ≤ w) :
    capillaryWater (waterFraction w) 1 = densityRatio * (w - criticalWcSealed) / (w * densityRatio + 1) := by
  have hd := (denom_pos hw).ne'
  unfold capillaryWater waterFraction
  rw [capillaryConsumption_value, densityRatio_value, criticalWcSealed_value] at *
  field_simp
  ring

/-- **Sealed-curing threshold**: at complete hydration capillary water remains exactly when `w ≥ (w/c)* = 0.42`. -/
theorem capillaryWater_full_nonneg_iff (w : ℚ) (hw : 0 ≤ w) :
    0 ≤ capillaryWater (waterFraction w) 1 ↔ criticalWcSealed ≤ w := by
  rw [capillaryWater_full w hw, le_div_iff₀ (denom_pos hw), zero_mul, densityRatio_value]
  constructor <;> intro h <;> linarith

/-- Capillary water and shrinkage voids at complete hydration: the space left for hydration products. -/
theorem space_full (w : ℚ) (hw : 0 ≤ w) :
    capillaryWater (waterFraction w) 1 + shrinkage (waterFraction w) 1 =
      densityRatio * (w - criticalWcSpace) / (w * densityRatio + 1) := by
  have hd := (denom_pos hw).ne'
  unfold capillaryWater shrinkage waterFraction
  rw [capillaryConsumption_value, shrinkageVolume_value, densityRatio_value, criticalWcSpace_value] at *
  field_simp
  ring

/-- The paste fraction of capillary water is the per-cement volume over the paste volume `w·d + 1`. -/
theorem capillaryWater_full_eq (w : ℚ) (hw : 0 ≤ w) :
    capillaryWater (waterFraction w) 1 = capillaryPerCement w / (w * densityRatio + 1) := by
  have hd := (denom_pos hw).ne'
  unfold capillaryWater waterFraction capillaryPerCement
  field_simp

/-- The paste fraction of space left for products is the per-cement volume over the paste volume. -/
theorem space_full_eq (w : ℚ) (hw : 0 ≤ w) :
    capillaryWater (waterFraction w) 1 + shrinkage (waterFraction w) 1 = spacePerCement w / (w * densityRatio + 1) := by
  have hd := (denom_pos hw).ne'
  unfold capillaryWater shrinkage waterFraction spacePerCement capillaryPerCement
  field_simp

/-- **Space threshold**: at complete hydration the products fit exactly when `w ≥ (w/c)_s = 0.356`. -/
theorem space_full_nonneg_iff (w : ℚ) (hw : 0 ≤ w) :
    0 ≤ capillaryWater (waterFraction w) 1 + shrinkage (waterFraction w) 1 ↔ criticalWcSpace ≤ w := by
  rw [space_full w hw, le_div_iff₀ (denom_pos hw), zero_mul, densityRatio_value]
  constructor <;> intro h <;> linarith

end UMST.Concrete.PowersVolume
