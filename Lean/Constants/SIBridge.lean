-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Constants/SIBridge.lean

  The exact constants of `Constants.SI` are the constants the second-law chain uses, and the laws that carry the
  second law are stated over them:

  * identity: `kBoltzmannSI`, `LandauerLaw.kB` and `speedOfLightSI` (real-valued, used by the Landauer and
    Landauer–Einstein modules) equal the exact SI values cast to ℝ, so the ecosystem has one Boltzmann constant
    and one speed of light;
  * molar Landauer law: erasing one mole of bits at temperature `T` costs at least `R T ln 2`, because
    `N_A · (k_B T ln 2) = R T ln 2` with `R = N_A k_B` derived in `Constants.SI`;
  * mass equivalent: the mass equivalent of the Landauer energy is `k_B T ln 2 / c²` with `c²` derived exactly.

  * the SI Landauer bound: under the second-law hypothesis in SI form (`ProcessFamily.eraseSecondLawSI`: an entropy
    drop of `ln 2` nats costs work `W` with `ln 2 ≤ W / (k_B T)`), erasing one bit at `T` costs at least `k_B T ln 2`
    joules with the exact SI `k_B`, and erasing one mole of bits costs at least `R T ln 2`;
    `LandauerLaw.SecondLaw_landauerTight` shows the natural-unit bound is attained.
-/

import Constants.SI
import LandauerEinsteinBridge
import LandauerLaw
import Process

open Real UMST.Constants.SI

namespace UMST.Constants.SIBridge

/-- The Landauer–Einstein bridge's Boltzmann constant is the exact SI value. -/
theorem kBoltzmannSI_eq : kBoltzmannSI = (boltzmann : ℝ) := by
  norm_num [kBoltzmannSI, boltzmann]

/-- The Landauer law's Boltzmann constant is the exact SI value. -/
theorem landauerLaw_kB_eq : UMST.LandauerLaw.kB = (boltzmann : ℝ) := by
  norm_num [UMST.LandauerLaw.kB, boltzmann]

/-- The bridge's speed of light is the exact SI value. -/
theorem speedOfLightSI_eq : speedOfLightSI = (speedOfLight : ℝ) := by
  norm_num [speedOfLightSI, speedOfLight]

/-- Erasing one mole of bits at temperature `T` costs `R T ln 2`: `N_A` times the Landauer bit energy. -/
theorem molarLandauer (T : ℝ) : (avogadro : ℝ) * landauerBitEnergy T = (gasConstant : ℝ) * T * log 2 := by
  rw [landauerBitEnergy, kBoltzmannSI_eq, gasConstant, Rat.cast_mul]
  ring

/-- The mass equivalent of the Landauer energy at `T` is the Landauer energy over the exact `c²`. -/
theorem massEquivalent_eq (T : ℝ) : massEquivalent T = landauerBitEnergy T / (speedOfLightSquared : ℝ) := by
  rw [massEquivalent, speedOfLightSI_eq, speedOfLightSquared, Rat.cast_mul]
  ring

/-- The molar Landauer cost is positive at every positive temperature. -/
theorem molarLandauer_pos {T : ℝ} (hT : 0 < T) : 0 < (gasConstant : ℝ) * T * log 2 := by
  rw [← molarLandauer]
  exact mul_pos (by norm_num [avogadro]) (landauerBitEnergy_pos hT)

/-- **SI Landauer bound.** Under the second law in SI form, erasing one bit (an entropy drop of `ln 2` nats) at
    temperature `T` costs at least `k_B T ln 2` joules, with `k_B` the exact SI value. -/
theorem landauerBoundSI {T W : ℝ} (hT : 0 < T) (h : UMST.ProcessFamily.eraseSecondLawSI T hT (log 2) W) :
    (boltzmann : ℝ) * T * log 2 ≤ W := by
  unfold UMST.ProcessFamily.eraseSecondLawSI at h
  rw [le_div_iff₀ (mul_pos UMST.LandauerLaw.kB_pos hT), landauerLaw_kB_eq] at h
  linarith [show (boltzmann : ℝ) * T * log 2 = log 2 * ((boltzmann : ℝ) * T) by ring]

/-- **Molar SI Landauer bound.** If each of `N_A` bit erasures obeys the second law in SI form with work `W`, the
    mole costs at least `R T ln 2` joules. -/
theorem molarLandauerBoundSI {T W : ℝ} (hT : 0 < T) (h : UMST.ProcessFamily.eraseSecondLawSI T hT (log 2) W) :
    (gasConstant : ℝ) * T * log 2 ≤ (avogadro : ℝ) * W := by
  have hb := landauerBoundSI hT h
  have hN : (0 : ℝ) ≤ (avogadro : ℝ) := by norm_num [avogadro]
  calc (gasConstant : ℝ) * T * log 2 = (avogadro : ℝ) * ((boltzmann : ℝ) * T * log 2) := by
        rw [gasConstant, Rat.cast_mul]; ring
    _ ≤ (avogadro : ℝ) * W := mul_le_mul_of_nonneg_left hb hN

end UMST.Constants.SIBridge
