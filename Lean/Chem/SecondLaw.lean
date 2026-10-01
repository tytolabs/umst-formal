-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/SecondLaw.lean

  Meso acting chemistry: a chemical assemblage update obeys the second law when its erasure is an instance of the
  one predicate `UMST.ProcessFamily.SecondLaw` on the transformation of its state distribution.

  Fiber: meso/acting → `umst-formal` only.  No quantum geometry theorems.
  CALPHAD / QTAIM / SpeciesId are presentations — not new physics axioms here.
-/

import LandauerLaw
import Process

open Real Finset UMST.LandauerLaw

namespace UMST.Chem.SecondLaw

-- ================================================================
-- SECTION 1: Chemical assemblage carriers (acting meso layer)
-- ================================================================

/-- A thermochemical transition on an assemblage: prior/post state distributions,
    dissipated work [entropy units, k_B = 1], and structural defect scalar. -/
structure ThermochemicalTransition (n : ℕ) where
  bath : HeatBath
  prior : ProbDist n
  post : ProbDist n
  dissipatedWork : ℝ
  structuralDefect : ℝ

/-- Structural coherence of an assemblage transition (no contradictory composition). -/
def structurallyCoherent {n : ℕ} (t : ThermochemicalTransition n) : Prop :=
  t.structuralDefect = 0

/-- Shannon entropy drop on the assemblage state distribution (nats). -/
noncomputable def assemblageEntropyDrop {n : ℕ} (t : ThermochemicalTransition n) : ℝ :=
  shannonEntropy t.prior - shannonEntropy t.post

-- ================================================================
-- SECTION 2: Named second-law invariant (Prop — not a Lean axiom)
-- ================================================================

/-- The erasure that pays for a transition: its bath and the work it dissipates. -/
def ThermochemicalTransition.erasure {n : ℕ} (t : ThermochemicalTransition n) : ErasureProcess :=
  ⟨t.bath, t.dissipatedWork⟩

/-- **Chemical second law**: a structurally coherent assemblage update whose erasure is an instance of the one
    second law, `UMST.ProcessFamily.SecondLaw (.erase _) (.transformation prior post)`. -/
def chemSecondLaw {n : ℕ} (t : ThermochemicalTransition n) : Prop :=
  structurallyCoherent t ∧
  UMST.ProcessFamily.SecondLaw (.erase t.erasure) (.transformation t.prior t.post)

/-- Its entropy part is the Clausius bound on the assemblage: ΔS ≤ W / T. -/
theorem chemSecondLaw_iff {n : ℕ} (t : ThermochemicalTransition n) :
    chemSecondLaw t ↔
      structurallyCoherent t ∧ assemblageEntropyDrop t ≤ t.dissipatedWork / t.bath.bathTemp.val :=
  Iff.rfl

/-- Two coherent updates at one bath, the second starting where the first ends, compose: the whole update obeys
    the second law at the summed work. -/
theorem chemSecondLaw_comp {n : ℕ} (t₁ t₂ : ThermochemicalTransition n) (hb : t₁.bath = t₂.bath)
    (hp : t₁.post = t₂.prior) (h₁ : chemSecondLaw t₁) (h₂ : chemSecondLaw t₂) :
    UMST.ProcessFamily.SecondLaw (.erase ⟨t₁.bath, t₁.dissipatedWork + t₂.dissipatedWork⟩)
      (.transformation t₁.prior t₂.post) := by
  have h₂' : UMST.ProcessFamily.SecondLaw (.erase ⟨t₁.bath, t₂.dissipatedWork⟩) (.transformation t₁.post t₂.post) := by
    rw [hb, hp]; exact h₂.2
  exact UMST.ProcessFamily.SecondLaw_transformation_comp t₁.bath t₁.prior t₁.post t₂.post _ _ h₁.2 h₂'

-- ================================================================
-- SECTION 3: Landauer refinement floor (dissipative refining)
-- ================================================================

/-- Landauer work floor for an entropy drop expressed at bath temperature `T`. -/
noncomputable def refinementWorkFloor (entropyDrop T : ℝ) : ℝ :=
  T * entropyDrop

/-- Dissipated work meets the Landauer-style floor for the declared entropy drop. -/
def refinementWorkAccounted {n : ℕ} (t : ThermochemicalTransition n) : Prop :=
  refinementWorkFloor (assemblageEntropyDrop t) t.bath.bathTemp.val ≤ t.dissipatedWork

-- ================================================================
-- SECTION 4: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

/-- Physical realization of a binary assemblage erasure (uniform → Dirac). -/
structure PhysicalChemBridge where
  proc : ErasureProcess
  transition : ThermochemicalTransition 2
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  priorEq : transition.prior = uniformBinary
  postEq : transition.post = diracDist (0 : Fin 2)
  coherent : structurallyCoherent transition

/-- `physicalSecondLaw` discharges the entropy-accounting conjunct of `chemSecondLaw`. -/
theorem chem_entropy_bound_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    assemblageEntropyDrop b.transition ≤
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val := by
  have hdrop :
      assemblageEntropyDrop b.transition =
        shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2)) := by
    unfold assemblageEntropyDrop
    rw [b.priorEq, b.postEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    have hbval :
        b.transition.bath.bathTemp.val = b.proc.bath.bathTemp.val := by
      exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
    rw [b.workEq, hbval]
  rw [hdrop, hwork]
  exact hSL

/-- Landauer bound on dissipated work for a physically bridged assemblage erasure. -/
theorem refinementLandauerBound (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    b.transition.dissipatedWork ≥
      b.transition.bath.bathTemp.val * log 2 := by
  have hbath :
      b.transition.bath.bathTemp.val = b.proc.bath.bathTemp.val := by
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  have h := landauerBound b.proc hSL
  rw [b.workEq.symm] at h
  rw [hbath.symm] at h
  exact h

/-- Physically bridged coherent transition satisfies `chemSecondLaw`. -/
theorem chemSecondLaw_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    chemSecondLaw b.transition :=
  ⟨b.coherent, chem_entropy_bound_from_physical b hSL⟩

-- ================================================================
-- SECTION 5: Canonical fixtures (0 sorry — catalog witnesses)
-- ================================================================

/-- Coherent P0 transition with zero entropy drop and zero dissipated work. -/
noncomputable def coherentP0Transition : ThermochemicalTransition 2 where
  bath := { bathTemp := ⟨300, by norm_num⟩ }
  prior := uniformBinary
  post := uniformBinary
  dissipatedWork := 0
  structuralDefect := 0

theorem coherentP0_zero_entropy_drop :
    assemblageEntropyDrop coherentP0Transition = 0 := by
  unfold assemblageEntropyDrop coherentP0Transition
  ring

theorem coherentP0_structurallyCoherent :
    structurallyCoherent coherentP0Transition := rfl

theorem coherentP0_chemSecondLaw : chemSecondLaw coherentP0Transition := by
  refine (chemSecondLaw_iff _).2 ⟨rfl, ?_⟩
  unfold assemblageEntropyDrop coherentP0Transition
  simp [coherentP0_zero_entropy_drop]

end UMST.Chem.SecondLaw
