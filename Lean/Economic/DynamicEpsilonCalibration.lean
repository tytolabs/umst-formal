/-
  UMST-Formal: Economic/DynamicEpsilonCalibration.lean

  Observable-to-entropy-tax mapping: user supplies `f` (e.g. monthly metric); Landauer bit-energy
  gives a compatible **energy** scale at bath temperature `T`. No live data feed in proof objects.
-/

import Economic.EconomicDomain
import LandauerEinsteinBridge

open Real

namespace UMST.Economics

/-- Map a public observable `x` to an entropy-tax scalar `ε` (same units as caller chooses for burden `ε`). -/
noncomputable def epsilonFromObservable (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x

/-- Landauer bit-energy at `T` is positive when `T > 0` (SI positivity chain in bridge). -/
theorem landauerBitEnergy_pos_of_T_pos {T : ℝ} (hT : 0 < T) : 0 < landauerBitEnergy T :=
  landauerBitEnergy_pos hT

/-- **Calibration receipt:** any nonnegative `f x` scales a lower bound on energy per nat at temperature `T`. -/
theorem epsilon_calibrated_energy_nonneg (T x : ℝ) (f : ℝ → ℝ) (hT : 0 < T) (hf : 0 ≤ f x) :
    0 ≤ landauerBitEnergy T * f x / log 2 := by
  have hbit : 0 < landauerBitEnergy T := landauerBitEnergy_pos hT
  have hlog : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  exact div_nonneg (mul_nonneg hbit.le hf) hlog.le

end UMST.Economics
