-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Process.lean

  Unified thermodynamic **process family** (P0-8): one `Process` type and one
  `SecondLaw : Process → Prior → Prop` generalising erasure-only accounting.

  Instances:
    • `erase` — Clausius entropy form ΔS_sys ≤ W/T (natural units k_B = 1 on `ErasureProcess.work`;
      SI joules use `kB` from `LandauerLaw`).
    • `measureFeedback` — Sagawa–Ueda generalized second law for feedback control
      (T. Sagawa and M. Ueda, Phys. Rev. Lett. **100**, 080403 (2008)):
      W_ext ≤ −ΔF + k_B T I  (I = mutual information in nats).
    • `transition` — free-energy descent via `UMST.Core.CoreAdmissible` on `RealThermodynamicState`.

  Witnesses: Landauer-tight erasure; Szilard engine at I = ln 2.

  Zero Lean `axiom` / `sorry`. Erase branch delegates to `LandauerLaw.eraseSecondLaw`.
-/

import LandauerLaw
import InfoTheory
import Core.Gate
import Real.State

open Real Finset UMST.Core UMST.Real
open UMST.LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist

namespace UMST.ProcessFamily

-- ================================================================
-- SECTION 1: Process constructors
-- ================================================================

/-- Measurement-and-feedback process: external work on the device, free-energy change
    of the system, and an isothermal bath (Kelvin). -/
structure FeedbackProcess where
  bath : HeatBath
  extWork : ℝ
  deltaFreeEnergy : ℝ

/-- Unified physical process family. -/
inductive Process where
  | erase (proc : ErasureProcess)
  | measureFeedback (proc : FeedbackProcess)
  | transition

-- ================================================================
-- SECTION 2: Prior witnesses (matched to process kind)
-- ================================================================

/-- Prior / boundary data for a `SecondLaw` membership test. -/
inductive Prior where
  | erasure (p : ProbDist 2)
  | feedback {n m : ℕ} (J : JointDist n m)
  | thermodynamic (old new : RealThermodynamicState)
  /-- A transformation of an `n`-state distribution `prior` into `post` (a chemical assemblage, a register, a memory). -/
  | transformation {n : ℕ} (prior post : ProbDist n)

-- ================================================================
-- SECTION 3: Second law — one predicate, three instances
-- ================================================================

/-- **Second law** (process-family admissibility).

    Wrong `Prior` kind for a constructor yields `False` (typed refusal, not a silent skip). -/
def SecondLaw : Process → Prior → Prop
  | .erase proc, .erasure prior =>
    eraseSecondLaw proc prior
  | .measureFeedback proc, .feedback J =>
    proc.extWork ≤ -proc.deltaFreeEnergy + kB * proc.bath.bathTemp.val * mutualInformation J
  | .transition, .thermodynamic old new =>
    CoreAdmissible ℝ RealThermodynamicState old new
  | .erase proc, .transformation prior post =>
    shannonEntropy prior - shannonEntropy post ≤ proc.work / proc.bath.bathTemp.val
  | _, _ => False

/-- SI Clausius form for erasure when `workJoules` is dissipated work in joules:
    ΔS_sys ≤ W / (k_B T). -/
def eraseSecondLawSI (T : ℝ) (_hT : 0 < T) (entropyDrop workJoules : ℝ) : Prop :=
  entropyDrop ≤ workJoules / (kB * T)

/-- **Units bridge**: the erase instance states work in units of k_B times kelvin; in joules that work is k_B·W, and
    the instance is exactly the SI Clausius form at that work. One law, two unit systems. -/
theorem SecondLaw_transformation_iff_SI (b : HeatBath) (W : ℝ) {n : ℕ} (p q : ProbDist n) :
    SecondLaw (.erase ⟨b, W⟩) (.transformation p q) ↔
      eraseSecondLawSI b.bathTemp.val b.bathTemp.property (shannonEntropy p - shannonEntropy q) (kB * W) := by
  show _ ≤ W / b.bathTemp.val ↔ _ ≤ kB * W / (kB * b.bathTemp.val)
  rw [mul_div_mul_left W _ (ne_of_gt kB_pos)]

-- ================================================================
-- SECTION 4: Witness — Landauer-tight erasure
-- ================================================================

theorem SecondLaw_landauerTight_erase (T : ℝ) (hT : 0 < T) :
    SecondLaw (.erase (landauerTightErasure T hT)) (.erasure uniformBinary) :=
  SecondLaw_landauerTight T hT

-- ================================================================
-- SECTION 5: Witness — Szilard engine (I = ln 2)
-- ================================================================

/-- Deterministic Szilard copy joint on `Fin 2 × Fin 2` (one bit of correlation). -/
noncomputable def szilardJoint : JointDist 2 2 where
  mass := fun p => if p.1 = p.2 then (1 : ℝ) / 2 else 0
  nonneg := fun p => by
    classical
    by_cases h : p.1 = p.2 <;> simp [h]
  sumOne := by
    classical
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, Finset.sum_ite_eq', Finset.mem_univ, if_true, if_false]
    norm_num

theorem szilardJoint_marginalX :
    marginalX szilardJoint = uniformBinary := by
  apply ProbDist.ext_mass
  funext i
  simp only [marginalX, szilardJoint, ProbDist.mass, uniformBinary, uniformDist]
  fin_cases i <;> simp [Fin.sum_univ_two]

theorem szilardJoint_marginalY :
    marginalY szilardJoint = uniformBinary := by
  apply ProbDist.ext_mass
  funext j
  simp only [marginalY, szilardJoint, ProbDist.mass, uniformBinary, uniformDist]
  fin_cases j <;> simp [Fin.sum_univ_two]

theorem szilardJoint_entropy :
    jointEntropy szilardJoint = log 2 := by
  classical
  unfold jointEntropy szilardJoint
  have hlog : log ((1 : ℝ) / 2) = -log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  have hsum :
      ∑ p : Fin 2 × Fin 2,
          (if p.1 = p.2 then (1 : ℝ) / 2 else 0) * log (if p.1 = p.2 then (1 : ℝ) / 2 else 0) =
        -log 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, hlog]
    have : (1 : ℝ) / 2 * (-log 2) + (1 : ℝ) / 2 * (-log 2) = -log 2 := by ring
    simpa using this
  rw [hsum, neg_neg]

theorem szilardJoint_mutualInformation :
    mutualInformation szilardJoint = log 2 := by
  unfold mutualInformation
  rw [szilardJoint_marginalX, szilardJoint_marginalY, uniformBinaryEntropy, szilardJoint_entropy]
  ring

/-- Szilard-limited feedback work at bath temperature `T`: W_ext = k_B T ln 2, ΔF = 0. -/
noncomputable def szilardEngine (T : ℝ) (hT : 0 < T) : FeedbackProcess where
  bath := { bathTemp := ⟨T, hT⟩ }
  extWork := kB * T * log 2
  deltaFreeEnergy := 0

theorem SecondLaw_szilardEngine (T : ℝ) (hT : 0 < T) :
    SecondLaw (.measureFeedback (szilardEngine T hT)) (.feedback szilardJoint) := by
  dsimp [SecondLaw]
  rw [szilardJoint_mutualInformation]
  simp only [szilardEngine, FeedbackProcess.deltaFreeEnergy, neg_zero, zero_add]
  exact le_rfl

-- ================================================================
-- SECTION 6: Transition instance (Core hook)
-- ================================================================

/-- A prior of the wrong kind is refused: an erasure is not judged against a measurement's information. -/
theorem SecondLaw_erase_feedback (proc : ErasureProcess) {n m : ℕ} (J : JointDist n m) :
    ¬ SecondLaw (.erase proc) (.feedback J) := id

theorem SecondLaw_transition_refl (s : RealThermodynamicState) :
    SecondLaw .transition (.thermodynamic s s) := by
  dsimp [SecondLaw]
  exact ⟨by simp [abs_zero], le_rfl⟩

theorem secondLaw_process_family_satisfiable :
    ∃ p pr, SecondLaw p pr :=
  ⟨.erase (landauerTightErasure 300 (by norm_num)), .erasure uniformBinary,
    SecondLaw_landauerTight_erase 300 (by norm_num)⟩

-- ================================================================
-- SECTION: Transformations of n-state distributions (Clausius form)
-- ================================================================

/-- Binary erasure is the transformation whose target is the Dirac state. -/
theorem SecondLaw_erasure_iff_transformation (proc : ErasureProcess) (p : ProbDist 2) :
    SecondLaw (.erase proc) (.erasure p) ↔ SecondLaw (.erase proc) (.transformation p (diracDist (0 : Fin 2))) :=
  Iff.rfl

/-- Leaving a distribution unchanged costs nothing: the identity transformation at zero work obeys the law. -/
theorem SecondLaw_transformation_id (b : HeatBath) {n : ℕ} (p : ProbDist n) :
    SecondLaw (.erase ⟨b, 0⟩) (.transformation p p) := by
  show shannonEntropy p - shannonEntropy p ≤ 0 / b.bathTemp.val
  simp

/-- **Composition.** At one bath temperature, transformations `p → q` at work `W₁` and `q → r` at work `W₂` that
    obey the second law compose into `p → r` at work `W₁ + W₂`, which obeys it too: entropy drops telescope and
    costs add. -/
theorem SecondLaw_transformation_comp (b : HeatBath) {n : ℕ} (p q r : ProbDist n) (W₁ W₂ : ℝ)
    (h₁ : SecondLaw (.erase ⟨b, W₁⟩) (.transformation p q))
    (h₂ : SecondLaw (.erase ⟨b, W₂⟩) (.transformation q r)) :
    SecondLaw (.erase ⟨b, W₁ + W₂⟩) (.transformation p r) := by
  change shannonEntropy p - shannonEntropy q ≤ W₁ / b.bathTemp.val at h₁
  change shannonEntropy q - shannonEntropy r ≤ W₂ / b.bathTemp.val at h₂
  show shannonEntropy p - shannonEntropy r ≤ (W₁ + W₂) / b.bathTemp.val
  rw [add_div]; linarith

/-- Independent erasures: the entropy both remove is at most the entropy both dissipate. -/
theorem SecondLaw_erasure_additive (e₁ e₂ : ErasureProcess) (p q : ProbDist 2)
    (h₁ : SecondLaw (.erase e₁) (.erasure p)) (h₂ : SecondLaw (.erase e₂) (.erasure q)) :
    (shannonEntropy p - shannonEntropy (diracDist (0 : Fin 2))) +
        (shannonEntropy q - shannonEntropy (diracDist (0 : Fin 2))) ≤
      e₁.work / e₁.bath.bathTemp.val + e₂.work / e₂.bath.bathTemp.val :=
  add_le_add h₁ h₂

end UMST.ProcessFamily
