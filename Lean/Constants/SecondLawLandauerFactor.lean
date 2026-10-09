-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Constants/SecondLawLandauerFactor.lean

  The Landauer factor ln 2 fixed by the second law. An erasure of the uniform bit at a bath of temperature `T`
  that dissipates `T·r` (work per kelvin `r`, in nats, the `k_B = 1` units of `ErasureProcess.work`) obeys the
  `.erase` case of `UMST.ProcessFamily.SecondLaw` exactly when `ln 2 ≤ r`
  (`secondLaw_uniformBit_iff`); the least admitted work per kelvin is therefore `ln 2`
  (`landauerFactor_isLeast`), at every temperature. In SI units the least work is `k_B·T·ln 2`
  (`Constants.SIBridge.landauerBoundSI`), and `ln 2` is the factor the cognitive-efficiency ratio divides by.
  Zero Lean axioms; physics enters only as the `SecondLaw` hypothesis.
-/

import Process

open Real UMST.ProcessFamily UMST.LandauerLaw

namespace UMST.Constants.SecondLawLandauerFactor

/-- An erasure at a bath of temperature `T` dissipating `T·r` (work per kelvin `r`, in nats). -/
noncomputable def erasureAtFactor (T : ℝ) (hT : 0 < T) (r : ℝ) : ErasureProcess where
  bath := { bathTemp := ⟨T, hT⟩ }
  work := T * r

/-- Erasing the uniform bit with work per kelvin `r` obeys the second law exactly when `ln 2 ≤ r`. -/
theorem secondLaw_uniformBit_iff (T : ℝ) (hT : 0 < T) (r : ℝ) :
    SecondLaw (.erase (erasureAtFactor T hT r)) (.erasure uniformBinary) ↔ log 2 ≤ r := by
  show shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2)) ≤ T * r / T ↔ _
  rw [binaryErasureEntropyDrop, mul_div_cancel_left₀ r hT.ne']

/-- **The Landauer factor**: `ln 2` is the least work per kelvin the second law admits for erasing one uniform
    bit, at every bath temperature. -/
theorem landauerFactor_isLeast (T : ℝ) (hT : 0 < T) :
    IsLeast {r : ℝ | SecondLaw (.erase (erasureAtFactor T hT r)) (.erasure uniformBinary)} (log 2) :=
  ⟨(secondLaw_uniformBit_iff T hT _).2 le_rfl, fun _ hr => (secondLaw_uniformBit_iff T hT _).1 hr⟩

end UMST.Constants.SecondLawLandauerFactor
