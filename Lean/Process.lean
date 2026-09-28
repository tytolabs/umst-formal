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
  | _, _ => False

/-- SI Clausius form for erasure when `workJoules` is dissipated work in joules:
    ΔS_sys ≤ W / (k_B T). -/
def eraseSecondLawSI (T : ℝ) (_hT : 0 < T) (entropyDrop workJoules : ℝ) : Prop :=
  entropyDrop ≤ workJoules / (kB * T)

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

theorem SecondLaw_transition_refl (s : RealThermodynamicState) :
    SecondLaw .transition (.thermodynamic s s) := by
  dsimp [SecondLaw]
  exact ⟨by simp [abs_zero], le_rfl⟩

theorem secondLaw_process_family_satisfiable :
    ∃ p pr, SecondLaw p pr :=
  ⟨.erase (landauerTightErasure 300 (by norm_num)), .erasure uniformBinary,
    SecondLaw_landauerTight_erase 300 (by norm_num)⟩

theorem physicalSecondLaw_erase_instance (proc : ErasureProcess) (prior : ProbDist 2) :
    SecondLaw (.erase proc) (.erasure prior) = physicalSecondLaw proc prior := rfl

-- ================================================================
-- SECTION 7: Erasure sequential composition (P0-9)
-- ================================================================

/-- Erasure-step admissibility `prior → post` (generalises `SecondLaw` on `.erase`). -/
def eraseStepSecondLaw (proc : ErasureProcess) (prior post : ProbDist 2) : Prop :=
  eraseSecondLawStep proc prior post

theorem eraseStepSecondLaw_dirac (proc : ErasureProcess) (prior : ProbDist 2) :
    eraseStepSecondLaw proc prior (diracDist (0 : Fin 2)) = eraseSecondLaw proc prior := rfl

/-- Chained erase processes: admissible `p → p'` then `p' → p''` ⇒ composite `p → p''`. -/
theorem SecondLaw_erase_sequential_compose (proc1 proc2 : ErasureProcess)
    (prior prior' prior'' : ProbDist 2)
    (hT : proc1.bath.bathTemp.val = proc2.bath.bathTemp.val)
    (h1 : eraseStepSecondLaw proc1 prior prior')
    (h2 : eraseStepSecondLaw proc2 prior' prior'') :
    eraseStepSecondLaw ⟨proc1.bath, proc1.work + proc2.work⟩ prior prior'' :=
  secondLaw_sequential_compose proc1 proc2 prior prior' prior'' hT h1 h2

/-- When the first step is a Dirac erasure, `SecondLaw (.erase proc1) (.erasure prior)` is the
    same membership test as `eraseStepSecondLaw proc1 prior (diracDist 0)`. -/
theorem SecondLaw_erase_diracStep (proc : ErasureProcess) (prior : ProbDist 2) :
    SecondLaw (.erase proc) (.erasure prior) ↔
      eraseStepSecondLaw proc prior (diracDist (0 : Fin 2)) := by
  dsimp [SecondLaw, eraseStepSecondLaw]
  rfl

end UMST.ProcessFamily
