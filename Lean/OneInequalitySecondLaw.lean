-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  FORMAL-ONE-INEQUALITY (W-29): single free-energy inequality

    ΔF ≤ W_in + k_B · T · I

  Each `ProcessFamily.Process` constructor fixes which terms vanish; one chaining lemma
  composes arbitrary (including mixed) step sequences at a common bath temperature
  (Szilard measure-then-erase cycle as witness).

  Bridges to `UMST.ProcessFamily.SecondLaw` in `umst-formal` — zero new Lean axioms.
  `physics_green` stays false (typed scaffold, not measured physics).
-/

import Process

open Real Finset UMST.LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist
open UMST.ProcessFamily UMST.Core UMST.Real

/-- Disambiguate from `LandauerLaw.SecondLaw` (erasure-only abbrev). -/
local notation "SecondLawₚ" => UMST.ProcessFamily.SecondLaw

namespace UMST.OneInequalitySecondLaw

/-- One thermodynamic step in the unified inequality (SI joules; `infoI` in nats). -/
structure Step where
  bath : HeatBath
  deltaF : ℝ
  wIn : ℝ
  infoI : ℝ

/-- **Second law (one inequality).** -/
def oneInequality (s : Step) : Prop :=
  s.deltaF ≤ s.wIn + kB * s.bath.bathTemp.val * s.infoI

@[simp] theorem oneInequality_def (s : Step) :
    oneInequality s ↔ s.deltaF ≤ s.wIn + kB * s.bath.bathTemp.val * s.infoI := Iff.rfl

/-- Sequential composition: additive ΔF, work, and information at fixed bath. -/
def Step.chain (s₁ s₂ : Step) (_hT : s₁.bath.bathTemp.val = s₂.bath.bathTemp.val) : Step :=
  { bath := s₁.bath
    deltaF := s₁.deltaF + s₂.deltaF
    wIn := s₁.wIn + s₂.wIn
    infoI := s₁.infoI + s₂.infoI }

/-- **Chaining lemma** (all cases and mixed chains): admissible steps compose. -/
theorem oneInequality_chain (s₁ s₂ : Step) (hT : s₁.bath.bathTemp.val = s₂.bath.bathTemp.val)
    (h₁ : oneInequality s₁) (h₂ : oneInequality s₂) :
    oneInequality (s₁.chain s₂ hT) := by
  dsimp [oneInequality, Step.chain]
  have h₂' : s₂.deltaF ≤ s₂.wIn + kB * s₁.bath.bathTemp.val * s₂.infoI := by simpa [hT] using h₂
  have hsum :
      s₁.wIn + kB * s₁.bath.bathTemp.val * s₁.infoI +
          (s₂.wIn + kB * s₁.bath.bathTemp.val * s₂.infoI) =
        s₁.wIn + s₂.wIn + kB * s₁.bath.bathTemp.val * (s₁.infoI + s₂.infoI) := by ring
  rw [← hsum]
  exact add_le_add h₁ h₂'

-- ================================================================
-- Constructor accounts (vanishing terms)
-- ================================================================

/-- Entropy-grade erase account (`LandauerLaw` convention: `work / T` is nats). -/
noncomputable def eraseStepEntropy (proc : ErasureProcess) (prior post : ProbDist 2) : Step where
  bath := proc.bath
  deltaF := proc.bath.bathTemp.val * (shannonEntropy prior - shannonEntropy post)
  wIn := proc.work
  infoI := 0

/-- **Erase (SI joules):** I = 0; ΔF = k_B T (S_prior − S_post), W_in = k_B · work. -/
noncomputable def eraseStep (proc : ErasureProcess) (prior post : ProbDist 2) : Step :=
  let s := eraseStepEntropy proc prior post
  { s with deltaF := kB * s.deltaF, wIn := kB * s.wIn }

@[simp] theorem eraseStep_infoI_zero (proc : ErasureProcess) (prior post : ProbDist 2) :
    (eraseStep proc prior post).infoI = 0 := rfl

theorem eraseStepEntropy_oneInequality_iff (proc : ErasureProcess) (prior post : ProbDist 2) :
    eraseSecondLawStep proc prior post ↔ oneInequality (eraseStepEntropy proc prior post) := by
  dsimp [oneInequality, eraseStepEntropy, eraseSecondLawStep]
  have hT : 0 < proc.bath.bathTemp.val := proc.bath.bathTemp.property
  constructor
  · intro h
    rw [mul_zero, add_zero, mul_comm]
    exact (le_div_iff₀ hT).1 h
  · intro h
    rw [mul_zero, add_zero, mul_comm] at h
    exact (le_div_iff₀ hT).2 h

lemma oneInequality_erase_joules (proc : ErasureProcess) (prior post : ProbDist 2) :
    oneInequality (eraseStepEntropy proc prior post) ↔ oneInequality (eraseStep proc prior post) := by
  dsimp [oneInequality, eraseStep, eraseStepEntropy]
  simp only [mul_zero, add_zero]
  constructor
  · intro h; nlinarith [h, kB_pos]
  · intro h; nlinarith [h, kB_pos]

theorem eraseStep_oneInequality_iff (proc : ErasureProcess) (prior post : ProbDist 2) :
    eraseSecondLawStep proc prior post ↔ oneInequality (eraseStep proc prior post) :=
  (eraseStepEntropy_oneInequality_iff proc prior post).trans (oneInequality_erase_joules proc prior post)

theorem eraseSecondLaw_oneInequality_iff (proc : ErasureProcess) (prior : ProbDist 2) :
    eraseSecondLaw proc prior ↔
      oneInequality (eraseStep proc prior (diracDist (0 : Fin 2))) := by
  rw [eraseSecondLaw_eq_step]
  exact eraseStep_oneInequality_iff proc prior (diracDist (0 : Fin 2))

/-- **Measure / feedback:** W_in = −W_ext (Sagawa external work); I = mutual information (nats). -/
noncomputable def feedbackStep (proc : FeedbackProcess) (infoI : ℝ) : Step where
  bath := proc.bath
  deltaF := proc.deltaFreeEnergy
  wIn := -proc.extWork
  infoI := infoI

@[simp] theorem feedbackStep_wIn_neg_extWork (proc : FeedbackProcess) (infoI : ℝ) :
    (feedbackStep proc infoI).wIn = -proc.extWork := rfl

theorem feedbackStep_oneInequality_iff (proc : FeedbackProcess) (J : JointDist n m) :
    (proc.extWork ≤ -proc.deltaFreeEnergy + kB * proc.bath.bathTemp.val * mutualInformation J) ↔
      oneInequality (feedbackStep proc (mutualInformation J)) := by
  dsimp [oneInequality, feedbackStep]
  constructor <;> intro h <;> linarith

theorem SecondLaw_measureFeedback_oneInequality_iff (proc : FeedbackProcess)
    (J : JointDist n m) :
    SecondLawₚ (.measureFeedback proc) (.feedback J) ↔
      oneInequality (feedbackStep proc (mutualInformation J)) :=
  feedbackStep_oneInequality_iff proc J

/-- **Passive transition:** W_in = 0, I = 0 ⇒ ΔF ≤ 0. -/
noncomputable def transitionStep (old new : RealThermodynamicState) : Step where
  bath := { bathTemp := ⟨1, by norm_num⟩ }
  deltaF := new.freeEnergy - old.freeEnergy
  wIn := 0
  infoI := 0

@[simp] theorem transitionStep_vanishing (old new : RealThermodynamicState) :
    (transitionStep old new).wIn = 0 ∧ (transitionStep old new).infoI = 0 := ⟨rfl, rfl⟩

theorem transitionStep_oneInequality_iff (old new : RealThermodynamicState) :
    (new.freeEnergy ≤ old.freeEnergy) ↔ oneInequality (transitionStep old new) := by
  dsimp [oneInequality, transitionStep]
  constructor <;> intro h <;> simpa [mul_zero, add_zero, zero_add] using h

theorem SecondLaw_transition_oneInequality_iff (old new : RealThermodynamicState) :
    SecondLawₚ .transition (.thermodynamic old new) ↔
      oneInequality (transitionStep old new) ∧
        CoreMassCond ℝ RealThermodynamicState old new := by
  constructor
  · intro h
    rcases h with ⟨hm, hd⟩
    exact ⟨(transitionStep_oneInequality_iff old new).1 hd, hm⟩
  · intro ⟨hF, hm⟩
    exact ⟨hm, (transitionStep_oneInequality_iff old new).2 hF⟩

/-- Package any `Process` + `Prior` as a `Step` when kinds match. -/
noncomputable def stepOf : Process → Prior → Option Step
  | .erase proc, .erasure prior =>
    some (eraseStep proc prior (diracDist (0 : Fin 2)))
  | .measureFeedback proc, .feedback J =>
    some (feedbackStep proc (mutualInformation J))
  | .transition, .thermodynamic old new =>
    some (transitionStep old new)
  | _, _ => none

theorem eraseSecondLaw_iff_oneInequality (proc : ErasureProcess) (prior : ProbDist 2) :
    SecondLawₚ (.erase proc) (.erasure prior) ↔
      oneInequality (eraseStep proc prior (diracDist (0 : Fin 2))) :=
  eraseSecondLaw_oneInequality_iff proc prior

/-- Any admissible `ProcessFamily` step packages as a `Step` satisfying the one inequality. -/
theorem secondLaw_implies_oneInequality (p : Process) (pr : Prior) (h : SecondLawₚ p pr) :
    ∃ s, stepOf p pr = some s ∧ oneInequality s := by
  match p, pr with
  | .erase proc, .erasure prior =>
    exact ⟨_, rfl, (eraseSecondLaw_oneInequality_iff proc prior).1 h⟩
  | .measureFeedback proc, .feedback J =>
    exact ⟨_, rfl, (SecondLaw_measureFeedback_oneInequality_iff proc J).1 h⟩
  | .transition, .thermodynamic old new =>
    rcases h with ⟨_, hd⟩
    exact ⟨_, rfl, (transitionStep_oneInequality_iff old new).1 hd⟩
  | .erase _, .feedback _ => cases h
  | .erase _, .thermodynamic _ _ => cases h
  | .measureFeedback _, .erasure _ => cases h
  | .measureFeedback _, .thermodynamic _ _ => cases h
  | .transition, .erasure _ => cases h
  | .transition, .feedback _ => cases h

-- ================================================================
-- Szilard mixed chain (measure then erase)
-- ================================================================

theorem szilardMixedChain_oneInequality (T : ℝ) (hT : 0 < T) :
    oneInequality
      ((feedbackStep (szilardEngine T hT) (log 2)).chain
        (eraseStep (landauerTightErasure T hT) uniformBinary (diracDist (0 : Fin 2)))
        (by rfl)) := by
  have hM : oneInequality (feedbackStep (szilardEngine T hT) (log 2)) := by
    rw [← szilardJoint_mutualInformation]
    exact (SecondLaw_measureFeedback_oneInequality_iff (szilardEngine T hT) szilardJoint).1
      (SecondLaw_szilardEngine T hT)
  have hE : oneInequality
      (eraseStep (landauerTightErasure T hT) uniformBinary (diracDist (0 : Fin 2))) :=
    (eraseSecondLaw_oneInequality_iff (landauerTightErasure T hT) uniformBinary).1
      (SecondLaw_landauerTight_erase T hT)
  exact oneInequality_chain (feedbackStep (szilardEngine T hT) (log 2))
    (eraseStep (landauerTightErasure T hT) uniformBinary (diracDist (0 : Fin 2))) rfl hM hE

def formalOneInequalityCellId : String := "FORMAL-ONE-INEQUALITY"

def formalOneInequalityPhysicsGreen : Bool := false

theorem formalOneInequalityPhysicsGreen_false :
    formalOneInequalityPhysicsGreen = false := rfl

end UMST.OneInequalitySecondLaw
