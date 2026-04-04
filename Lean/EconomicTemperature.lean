/-
  UMST-Formal: EconomicTemperature.lean

  Macroscopic "information temperature" layer: Shannon uncertainty of an adoption marginal,
  mapped to SI joules via the same Boltzmann factor as the Landauer–Einstein bridge
  (`k_B · T` per nat of entropy).
-/

import InfoTheory
import LandauerEinsteinBridge

open Real

namespace UMST.Economics

open UMST.InfoTheory UMST.LandauerLaw

/-- Shannon entropy (nats) of the **adoption / agent** marginal `Y` of a joint market×agent model. -/
noncomputable def adoptionInformation {n m : ℕ} (J : JointDist n m) : ℝ :=
  shannonEntropy (JointDist.marginalY J)

/-- **Economic thermal energy scale:** `k_B · T · S` with `S` the adoption marginal entropy (nats).
    This is the standard identification of Shannon entropy with thermodynamic entropy at bath `T`. -/
noncomputable def Tecon_joules {n m : ℕ} (T : ℝ) (J : JointDist n m) : ℝ :=
  kBoltzmannSI * T * adoptionInformation J

theorem Tecon_joules_product {n m : ℕ} (T : ℝ) (p : ProbDist n) (q : ProbDist m) :
    Tecon_joules T (JointDist.productJoint p q) = kBoltzmannSI * T * shannonEntropy q := by
  unfold Tecon_joules adoptionInformation
  rw [JointDist.marginalY_product]

/-- Independent product ⇒ adoption information equals `S(q)` alone (no correlation load). -/
theorem adoptionInformation_product {n m : ℕ} (p : ProbDist n) (q : ProbDist m) :
    adoptionInformation (JointDist.productJoint p q) = shannonEntropy q := by
  unfold adoptionInformation
  rw [JointDist.marginalY_product]

/-- Landauer bit-energy at `T` times the **bit-equivalent** adoption entropy `S / ln 2`. -/
noncomputable def Tecon_landauerBitEquivalent {n m : ℕ} (T : ℝ) (J : JointDist n m) : ℝ :=
  landauerBitEnergy T * adoptionInformation J / log 2

/-- `Tecon_landauerBitEquivalent` collapses to `k_B T S` — same as `Tecon_joules` — since
`landauerBitEnergy T · (S / ln 2) = (k_B T ln 2) · (S / ln 2)`. -/
theorem Tecon_landauerBitEquivalent_eq_Tecon_joules {n m : ℕ} (T : ℝ) (J : JointDist n m) :
    Tecon_landauerBitEquivalent T J = Tecon_joules T J := by
  unfold Tecon_landauerBitEquivalent Tecon_joules landauerBitEnergy adoptionInformation
  have hlog : log 2 ≠ 0 := ne_of_gt (log_pos (by norm_num : (1 : ℝ) < 2))
  field_simp [hlog]
  ring

end UMST.Economics
