/-
  UMST-Formal: CoordinationCost.lean

  Scaffold for the MTP-Arc **Coordination Cost Identity** (Paper 6 / A7):
    `CoordCost(A,B; T) = k_B · T · ln 2 · I(A:B)`  with mutual information in **bits**.

  **Semantics tier: reporting lower bound (Landauer floor).**
  The scalar is a *thermodynamic floor projection* for honest performance reporting —
  not realized dissipation, wall-clock speedup, or a `gate<R>` witness.

  Rust SSOT (parity targets):
    - `umst-arcs/crates/umst-arcs/src/coordination_cost.rs`
    - `umst-ucrs/Rust/src/landauer.rs` `coordination_cost`

  **Provable in this scaffold (no new axioms, no `sorry`):**
    - Definitional alignment with `landauerBitEnergy` and `ClassicalMeasurementCost`
    - Zero MI ⇒ zero saving; linear scaling in MI; temperature homogeneity

  **Explicit non-claims (documented via `OpenObligation`, not proved here):**
    - Joint erasure of correlated registers costs less than independent erasure
    - Finite-time excess above the isothermal Landauer floor
    - Epistemic / semantic MI (L10 fiber) — separate witness type (A7-4)

  L₀ boundary: does **not** import `Gate.lean` or Kleisli composition.
  Orthogonality of `coordination_saving` to Core `gate<R>` is operational (Rust tests).
-/

import LandauerEinsteinBridge
import InfoTheory
import ClassicalMeasurementCost

open Real UMST.InfoTheory UMST.InfoTheory.JointDist UMST.LandauerLaw
open UMST.ClassicalMeasurementCost

namespace UMST.CoordinationCost

-- ================================================================
-- SECTION 1: Reporting definitions (SSOT alignment)
-- ================================================================

/-- Mutual information reported in **bits** (`I_bits = I_nats / ln 2`). -/
noncomputable def mutualInformationBits {n m : ℕ} (J : JointDist n m) : ℝ :=
  mutualInformation J / log 2

/-- Coordination saving [J] at temperature `T` [K] for `miBits` of mutual information.
    Matches `coordination_saving_joules` in umst-arcs. -/
noncomputable def coordinationSavingJoules (miBits T : ℝ) : ℝ :=
  landauerBitEnergy T * miBits

/-- Landauer cost [J] for `bits` of resolved uncertainty at temperature `T` [K].
    Definitional alias — same reporting functor as `coordinationSavingJoules`. -/
noncomputable def landauerCostJoules (bits T : ℝ) : ℝ :=
  coordinationSavingJoules bits T

/-- Labels a scalar as a **floor projection**, not measured energy. -/
structure CoordinationReport where
  mutualInfoBits : ℝ
  temperatureKelvin : ℝ
  savingJoules : ℝ
  isProjection : savingJoules = coordinationSavingJoules mutualInfoBits temperatureKelvin

/-- Construct a projection report from MI (bits) and bath temperature. -/
noncomputable def mkReport (miBits T : ℝ) : CoordinationReport where
  mutualInfoBits := miBits
  temperatureKelvin := T
  savingJoules := coordinationSavingJoules miBits T
  isProjection := rfl

-- ================================================================
-- SECTION 2: Algebraic lemmas (proved — no physics beyond definitions)
-- ================================================================

theorem coordinationSaving_eq_landauerCost (miBits T : ℝ) :
    coordinationSavingJoules miBits T = landauerCostJoules miBits T :=
  rfl

theorem coordinationSaving_zero (T : ℝ) :
    coordinationSavingJoules 0 T = 0 := by
  unfold coordinationSavingJoules landauerBitEnergy
  ring

theorem coordinationSaving_linear (a miBits T : ℝ) :
    coordinationSavingJoules (a * miBits) T = a * coordinationSavingJoules miBits T := by
  unfold coordinationSavingJoules landauerBitEnergy
  ring

theorem coordinationSaving_one_bit (T : ℝ) :
    coordinationSavingJoules 1 T = landauerBitEnergy T := by
  unfold coordinationSavingJoules
  ring

theorem coordinationSaving_temp_scaling (miBits a T : ℝ) (_ha : 0 < a) :
    coordinationSavingJoules miBits (a * T) = a * coordinationSavingJoules miBits T := by
  unfold coordinationSavingJoules landauerBitEnergy
  ring

theorem mutualInformationBits_product_zero {n m : ℕ} (p : ProbDist n) (q : ProbDist m) :
    mutualInformationBits (productJoint p q) = 0 := by
  unfold mutualInformationBits
  rw [mutualInformation_product_zero]
  simp

theorem zero_mi_zero_saving {n m : ℕ} (T : ℝ) (p : ProbDist n) (q : ProbDist m) :
    coordinationSavingJoules (mutualInformationBits (productJoint p q)) T = 0 := by
  rw [mutualInformationBits_product_zero, coordinationSaving_zero]

/-- Classical MI floor in nats agrees with bit-normalised coordination saving. -/
theorem classical_measurement_floor_agrees {n m : ℕ} (T : ℝ) (J : JointDist n m) :
    measurementEnergyLowerBound T J =
      coordinationSavingJoules (mutualInformationBits J) T := by
  unfold measurementEnergyLowerBound coordinationSavingJoules mutualInformationBits
    landauerBitEnergy
  have hk : kB = kBoltzmannSI := rfl
  have hlog : log 2 ≠ 0 := ne_of_gt log_two_pos
  rw [hk]
  field_simp
  ring

-- ================================================================
-- SECTION 3: Open obligations (indexed — no `sorry` placeholders)
-- ================================================================

/-- Proof targets deferred beyond this scaffold. Listed for audit / receipt traceability. -/
inductive OpenObligation
  | joint_erasure_sub_additive
  | finite_time_excess_bound
  | epistemic_mi_witness
  deriving DecidableEq, Repr

end UMST.CoordinationCost
