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
    - Definitional alignment with `landauerBitEnergy`, `landauerEnergyAt`, `ClassicalMeasurementCost`
    - Zero MI ⇒ zero saving; linear / additive scaling in MI; temperature homogeneity
    - Mass-equivalent bridge via `LandauerEinsteinBridge.massEquivalent`
    - `CoordinationReport` projection witnesses (joules + kg)
    - Independent-minus-joint delta identity (algebraic form of Rust parity test)
    - A7-4 n-ary `multiInformationBits` with n=2 reduction to pairwise `mutualInformationBits`

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

/-- Mass equivalent [kg] of the coordination saving at temperature `T` [K].
    Matches egoff `CoordinationReport.mass_equiv_kg` (`cost_j / c²`). -/
noncomputable def coordinationMassEquivalentKg (miBits T : ℝ) : ℝ :=
  massEquivalent T * miBits

/-- Total correlation / multi-information in **nats**:
    `I_n = Σᵢ H(Xᵢ) − H(joint)` (Shannon entropies in nats). -/
noncomputable def multiInformationNats (marginalEntropies : List ℝ) (jointEntropy : ℝ) : ℝ :=
  marginalEntropies.sum - jointEntropy

/-- A7-4 global correlation scalar in **bits** (`I_n_bits = I_n_nats / ln 2`).
    Additive reporting identity — pairwise SSOT preserved; not a replacement. -/
noncomputable def multiInformationBits (marginalEntropies : List ℝ) (jointEntropy : ℝ) : ℝ :=
  multiInformationNats marginalEntropies jointEntropy / log 2

/-- A7-4 **global** coordination floor [J] from multi-information in bits.
    Matches planned `coordination_saving_global_joules` in umst-arcs (`feature a7-4`). -/
noncomputable def coordinationSavingGlobalJoules (multiInfoBits T : ℝ) : ℝ :=
  coordinationSavingJoules multiInfoBits T

/-- Legacy alias — same functor as `coordinationSavingGlobalJoules`. -/
noncomputable def globalCoordinationSavingJoules (multiInfoBits T : ℝ) : ℝ :=
  coordinationSavingGlobalJoules multiInfoBits T

/-- Independent erasure minus joint erasure floor [J].
    Algebraic form of `coordination_cost_identity_independent_minus_joint` (Rust). -/
noncomputable def independentMinusJointDelta (independentBits jointBits T : ℝ) : ℝ :=
  coordinationSavingJoules independentBits T - coordinationSavingJoules jointBits T

/-- Labels a scalar as a **floor projection**, not measured energy. -/
structure CoordinationReport where
  mutualInfoBits : ℝ
  temperatureKelvin : ℝ
  savingJoules : ℝ
  massEquivalentKg : ℝ
  isProjection : savingJoules = coordinationSavingJoules mutualInfoBits temperatureKelvin
  massEquivMatches :
    massEquivalentKg = coordinationMassEquivalentKg mutualInfoBits temperatureKelvin

/-- Construct a projection report from MI (bits) and bath temperature. -/
noncomputable def mkReport (miBits T : ℝ) : CoordinationReport where
  mutualInfoBits := miBits
  temperatureKelvin := T
  savingJoules := coordinationSavingJoules miBits T
  massEquivalentKg := coordinationMassEquivalentKg miBits T
  isProjection := rfl
  massEquivMatches := rfl

-- ================================================================
-- SECTION 2: Channel split scaffold (A7-4 — no epistemic→thermo slip)
-- ================================================================

/-- Physical MI channel: only declared joint distributions enter cert fixtures. -/
structure PhysicalMiChannel (n m : ℕ) where
  joint : JointDist n m

/-- Epistemic MI draft — **not** a thermodynamic witness without an explicit bridge.
    Mirrors egoff `ClosedLoop.cumulative_mi_bits` policy (reporting only). -/
structure EpistemicMiDraft where
  cumulativeBits : ℝ

/-- Physical channel projects to bits via Shannon MI on the declared joint. -/
noncomputable def physicalMiBits {n m : ℕ} (ch : PhysicalMiChannel n m) : ℝ :=
  mutualInformationBits ch.joint

/-- Epistemic draft carries raw bits only — no `PhysicalMiChannel` claim. -/
noncomputable def epistemicMiBits (draft : EpistemicMiDraft) : ℝ :=
  draft.cumulativeBits

-- ================================================================
-- SECTION 2b: N-ary physical channel (A7-4 — fixture declarations only)
-- ================================================================

/-- N-ary physical channel: declared marginal + joint Shannon entropies (nats).
    Fixture-only — no silent epistemic→thermo promotion. -/
structure PhysicalMultiInfoChannel where
  marginalEntropiesNats : List ℝ
  jointEntropyNats : ℝ

/-- Epistemic n-ary draft — **not** a thermodynamic witness without explicit bridge. -/
structure EpistemicMultiInfoDraft where
  marginalBits : List ℝ
  jointBits : ℝ

/-- Project declared entropies to multi-information in bits. -/
noncomputable def physicalMultiInfoBits (ch : PhysicalMultiInfoChannel) : ℝ :=
  multiInformationBits ch.marginalEntropiesNats ch.jointEntropyNats

/-- Epistemic n-ary draft carries raw bits only — no `PhysicalMultiInfoChannel` claim. -/
noncomputable def epistemicMultiInfoBits (draft : EpistemicMultiInfoDraft) : ℝ :=
  multiInformationBits draft.marginalBits draft.jointBits

/-- Pairwise joint distribution as a 2-ary physical multi-info channel. -/
noncomputable def physicalMultiInfoChannel_pair {n m : ℕ} (J : JointDist n m) :
    PhysicalMultiInfoChannel where
  marginalEntropiesNats := [shannonEntropy (marginalX J), shannonEntropy (marginalY J)]
  jointEntropyNats := jointEntropy J

/-- Global coordination report from multi-information (bits) at temperature `T`. -/
noncomputable def mkGlobalReport (multiInfoBits T : ℝ) : CoordinationReport :=
  mkReport multiInfoBits T

-- ================================================================
-- SECTION 3: Algebraic lemmas (proved — no physics beyond definitions)
-- ================================================================

theorem landauerBitEnergy_eq_landauerEnergyAt (T : ℝ) :
    landauerBitEnergy T = landauerEnergyAt T := by
  unfold landauerBitEnergy landauerEnergyAt kBoltzmannSI kB
  rfl

theorem coordinationSaving_eq_landauerCost (miBits T : ℝ) :
    coordinationSavingJoules miBits T = landauerCostJoules miBits T :=
  rfl

theorem coordinationSaving_eq_landauerEnergyAt (miBits T : ℝ) :
    coordinationSavingJoules miBits T = miBits * landauerEnergyAt T := by
  unfold coordinationSavingJoules landauerBitEnergy landauerEnergyAt kB kBoltzmannSI
  ring

theorem coordinationSaving_zero (T : ℝ) :
    coordinationSavingJoules 0 T = 0 := by
  unfold coordinationSavingJoules landauerBitEnergy
  ring

theorem coordinationSaving_linear (a miBits T : ℝ) :
    coordinationSavingJoules (a * miBits) T = a * coordinationSavingJoules miBits T := by
  unfold coordinationSavingJoules landauerBitEnergy
  ring

theorem coordinationSaving_additive (mi₁ mi₂ T : ℝ) :
    coordinationSavingJoules (mi₁ + mi₂) T =
      coordinationSavingJoules mi₁ T + coordinationSavingJoules mi₂ T := by
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

theorem coordinationMassEquivalent_eq_div (miBits T : ℝ) :
    coordinationMassEquivalentKg miBits T =
      coordinationSavingJoules miBits T / speedOfLightSI ^ 2 := by
  unfold coordinationMassEquivalentKg massEquivalent coordinationSavingJoules landauerBitEnergy
  ring

theorem coordinationMassEquivalent_temp_scaling (miBits a T : ℝ) (ha : 0 < a) :
    coordinationMassEquivalentKg miBits (a * T) =
      a * coordinationMassEquivalentKg miBits T := by
  rw [coordinationMassEquivalent_eq_div, coordinationMassEquivalent_eq_div]
  rw [coordinationSaving_temp_scaling miBits a T ha]
  ring

theorem multiInformationNats_eq_sum_sub (marginals joint : ℝ) :
    multiInformationNats [marginals] joint = marginals - joint := by
  simp [multiInformationNats]

theorem multiInformationBits_eq_div (marginalEntropies : List ℝ) (jointEntropy : ℝ) :
    multiInformationBits marginalEntropies jointEntropy =
      multiInformationNats marginalEntropies jointEntropy / log 2 := by
  rfl

theorem multiInformationNats_pair (hX hY joint : ℝ) :
    multiInformationNats [hX, hY] joint = hX + hY - joint := by
  simp [multiInformationNats]

theorem multiInformationBits_pair (hX hY joint : ℝ) :
    multiInformationBits [hX, hY] joint = (hX + hY - joint) / log 2 := by
  unfold multiInformationBits multiInformationNats
  simp

theorem multiInformationNats_zero (marginalEntropies : List ℝ) (jointEntropy : ℝ)
    (h : marginalEntropies.sum = jointEntropy) :
    multiInformationNats marginalEntropies jointEntropy = 0 := by
  unfold multiInformationNats
  rw [h, sub_self]

theorem multiInformationBits_zero (marginalEntropies : List ℝ) (jointEntropy : ℝ)
    (h : marginalEntropies.sum = jointEntropy) :
    multiInformationBits marginalEntropies jointEntropy = 0 := by
  unfold multiInformationBits multiInformationNats
  rw [h, sub_self, zero_div]

theorem multiInformationNats_nonneg (marginalEntropies : List ℝ) (jointEntropy : ℝ)
    (h : jointEntropy ≤ marginalEntropies.sum) :
    0 ≤ multiInformationNats marginalEntropies jointEntropy := by
  unfold multiInformationNats
  exact sub_nonneg.mpr h

theorem multiInformationBits_nonneg (marginalEntropies : List ℝ) (jointEntropy : ℝ)
    (h : jointEntropy ≤ marginalEntropies.sum) :
    0 ≤ multiInformationBits marginalEntropies jointEntropy := by
  unfold multiInformationBits multiInformationNats
  exact div_nonneg (sub_nonneg.mpr h) (le_of_lt log_two_pos)

theorem multiInformationBits_pair_eq_mutualInformationBits {n m : ℕ} (J : JointDist n m) :
    multiInformationBits
        [shannonEntropy (marginalX J), shannonEntropy (marginalY J)]
        (jointEntropy J) =
      mutualInformationBits J := by
  unfold multiInformationBits mutualInformationBits mutualInformation multiInformationNats
  simp only [List.sum_cons, List.sum_nil, add_zero]

theorem physicalMultiInfoBits_pair_eq {n m : ℕ} (J : JointDist n m) :
    physicalMultiInfoBits (physicalMultiInfoChannel_pair J) = mutualInformationBits J := by
  unfold physicalMultiInfoBits physicalMultiInfoChannel_pair
  exact multiInformationBits_pair_eq_mutualInformationBits J

theorem multiInformationBits_pair_product_zero {n m : ℕ} (p : ProbDist n) (q : ProbDist m) :
    multiInformationBits
        [shannonEntropy p, shannonEntropy q]
        (jointEntropy (productJoint p q)) = 0 := by
  have hj :
      [shannonEntropy p, shannonEntropy q].sum = jointEntropy (productJoint p q) := by
    simp only [List.sum_cons, List.sum_nil, add_zero]
    rw [← jointEntropy_product p q]
  exact multiInformationBits_zero _ _ hj

theorem coordinationSavingGlobal_eq_pairwise (multiInfoBits T : ℝ) :
    coordinationSavingGlobalJoules multiInfoBits T = coordinationSavingJoules multiInfoBits T :=
  rfl

theorem globalCoordinationSaving_eq_global (multiInfoBits T : ℝ) :
    globalCoordinationSavingJoules multiInfoBits T = coordinationSavingGlobalJoules multiInfoBits T :=
  rfl

theorem globalCoordinationSaving_eq_pairwise (miBits T : ℝ) :
    globalCoordinationSavingJoules miBits T = coordinationSavingJoules miBits T :=
  rfl

theorem coordinationSavingGlobal_linear (a multiInfoBits T : ℝ) :
    coordinationSavingGlobalJoules (a * multiInfoBits) T =
      a * coordinationSavingGlobalJoules multiInfoBits T := by
  unfold coordinationSavingGlobalJoules
  exact coordinationSaving_linear a multiInfoBits T

theorem coordinationSavingGlobal_zero (T : ℝ) :
    coordinationSavingGlobalJoules 0 T = 0 := by
  unfold coordinationSavingGlobalJoules
  exact coordinationSaving_zero T

theorem coordinationSavingGlobal_physical_zero {n m : ℕ} (T : ℝ) (p : ProbDist n) (q : ProbDist m) :
    coordinationSavingGlobalJoules
        (physicalMultiInfoBits
          ⟨[shannonEntropy p, shannonEntropy q], jointEntropy (productJoint p q)⟩)
        T = 0 := by
  rw [physicalMultiInfoBits, multiInformationBits_pair_product_zero, coordinationSavingGlobal_zero]

theorem global_floor_pair_agrees {n m : ℕ} (T : ℝ) (J : JointDist n m) :
    coordinationSavingGlobalJoules (physicalMultiInfoBits (physicalMultiInfoChannel_pair J)) T =
      coordinationSavingJoules (mutualInformationBits J) T := by
  rw [physicalMultiInfoBits_pair_eq, coordinationSavingGlobal_eq_pairwise]

theorem mkGlobalReport_saving (multiInfoBits T : ℝ) :
    (mkGlobalReport multiInfoBits T).savingJoules =
      coordinationSavingGlobalJoules multiInfoBits T :=
  rfl

theorem independent_minus_joint_eq_mi_delta (independent joint T : ℝ) :
    independentMinusJointDelta independent joint T =
      coordinationSavingJoules (independent - joint) T := by
  unfold independentMinusJointDelta coordinationSavingJoules landauerBitEnergy
  ring

theorem independent_minus_joint_zero_joint (independent T : ℝ) :
    independentMinusJointDelta independent 0 T = coordinationSavingJoules independent T := by
  rw [independent_minus_joint_eq_mi_delta, sub_zero]

theorem mkReport_saving (miBits T : ℝ) :
    (mkReport miBits T).savingJoules = coordinationSavingJoules miBits T :=
  rfl

theorem mkReport_mass_equiv (miBits T : ℝ) :
    (mkReport miBits T).massEquivalentKg = coordinationMassEquivalentKg miBits T :=
  rfl

theorem mkReport_fields (miBits T : ℝ) :
    (mkReport miBits T).mutualInfoBits = miBits ∧
      (mkReport miBits T).temperatureKelvin = T :=
  ⟨rfl, rfl⟩

theorem mutualInformationBits_product_zero {n m : ℕ} (p : ProbDist n) (q : ProbDist m) :
    mutualInformationBits (productJoint p q) = 0 := by
  unfold mutualInformationBits
  rw [mutualInformation_product_zero]
  simp

theorem physicalMiBits_product_zero {n m : ℕ} (p : ProbDist n) (q : ProbDist m) :
    physicalMiBits ⟨productJoint p q⟩ = 0 := by
  unfold physicalMiBits
  exact mutualInformationBits_product_zero p q

theorem coordinationSaving_physical_zero {n m : ℕ} (T : ℝ) (p : ProbDist n) (q : ProbDist m) :
    coordinationSavingJoules (physicalMiBits ⟨productJoint p q⟩) T = 0 := by
  rw [physicalMiBits_product_zero, coordinationSaving_zero]

theorem coordinationSaving_nonneg (miBits T : ℝ) (hmi : 0 ≤ miBits) (hT : 0 ≤ T) :
    0 ≤ coordinationSavingJoules miBits T := by
  unfold coordinationSavingJoules landauerBitEnergy
  refine mul_nonneg ?_ hmi
  exact mul_nonneg (mul_nonneg (le_of_lt kBoltzmannSI_pos) hT) (le_of_lt log_two_pos)

theorem coordinationSaving_pos (miBits T : ℝ) (hmi : 0 < miBits) (hT : 0 < T) :
    0 < coordinationSavingJoules miBits T := by
  unfold coordinationSavingJoules landauerBitEnergy
  exact mul_pos (mul_pos (mul_pos kBoltzmannSI_pos hT) log_two_pos) hmi

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

theorem physical_channel_floor_agrees {n m : ℕ} (T : ℝ) (ch : PhysicalMiChannel n m) :
    measurementEnergyLowerBound T ch.joint =
      coordinationSavingJoules (physicalMiBits ch) T := by
  unfold physicalMiBits
  exact classical_measurement_floor_agrees T ch.joint

-- ================================================================
-- SECTION 4: Open obligations (indexed — no `sorry` placeholders)
-- ================================================================

/-- Proof targets deferred beyond this scaffold. Listed for audit / receipt traceability. -/
inductive OpenObligation
  | joint_erasure_sub_additive
  | finite_time_excess_bound
  | epistemic_mi_witness
  deriving DecidableEq, Repr

/-- Human-readable obligation labels for receipts / cert tooling. -/
def openObligationDescription : OpenObligation → String
  | .joint_erasure_sub_additive =>
      "joint erasure of correlated registers cheaper than independent sum"
  | .finite_time_excess_bound =>
      "finite-time excess dissipation above isothermal Landauer floor"
  | .epistemic_mi_witness =>
      "epistemic MI bridge witness (L10 fiber) — not physical MI"

end UMST.CoordinationCost
