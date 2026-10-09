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

/-- **Refinement work is the erase case of the second law.** At a positive bath temperature the Landauer floor
    `T · ΔS ≤ W` holds exactly when the update's erasure obeys `UMST.ProcessFamily.SecondLaw` on the transformation
    of its state distribution, the Clausius bound `ΔS ≤ W / T`. -/
theorem refinementWorkAccounted_iff {n : ℕ} (t : ThermochemicalTransition n) :
    refinementWorkAccounted t ↔
      UMST.ProcessFamily.SecondLaw (.erase t.erasure) (.transformation t.prior t.post) := by
  show _ ↔ assemblageEntropyDrop t ≤ t.dissipatedWork / t.bath.bathTemp.val
  unfold refinementWorkAccounted refinementWorkFloor
  rw [le_div_iff₀ t.bath.bathTemp.property, mul_comm]

/-- **The refinement floor is the chemical second law**: a coherent update obeys it exactly when its dissipated work
    meets the Landauer floor of its entropy drop. -/
theorem chemSecondLaw_iff_accounted {n : ℕ} (t : ThermochemicalTransition n) :
    chemSecondLaw t ↔ structurallyCoherent t ∧ refinementWorkAccounted t :=
  and_congr_right fun _ => (refinementWorkAccounted_iff t).symm

-- ================================================================
-- SECTION 4: Bridge from the erase case on the bit (derived — zero new axioms)
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

/-- The erase case of `UMST.ProcessFamily.SecondLaw` on the uniform bit discharges the erase case on the bridged
    update's transformation: the entropy-accounting conjunct of `chemSecondLaw`. -/
theorem chem_entropy_bound_from_physical (b : PhysicalChemBridge)
    (hSL : UMST.ProcessFamily.SecondLaw (.erase b.proc) (.erasure uniformBinary)) :
    UMST.ProcessFamily.SecondLaw (.erase b.transition.erasure)
      (.transformation b.transition.prior b.transition.post) := by
  show assemblageEntropyDrop b.transition ≤ b.transition.dissipatedWork / b.transition.bath.bathTemp.val
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

/-- Landauer bound on dissipated work for a physically bridged assemblage erasure whose erasure obeys the erase
    case of `UMST.ProcessFamily.SecondLaw` on the uniform bit. -/
theorem refinementLandauerBound (b : PhysicalChemBridge)
    (hSL : UMST.ProcessFamily.SecondLaw (.erase b.proc) (.erasure uniformBinary)) :
    b.transition.dissipatedWork ≥
      b.transition.bath.bathTemp.val * log 2 := by
  have hbath :
      b.transition.bath.bathTemp.val = b.proc.bath.bathTemp.val := by
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  have h := landauerBound b.proc hSL
  rw [b.workEq.symm] at h
  rw [hbath.symm] at h
  exact h

/-- A physically bridged coherent transition whose erasure obeys the erase case on the uniform bit satisfies
    `chemSecondLaw`. -/
theorem chemSecondLaw_from_physical (b : PhysicalChemBridge)
    (hSL : UMST.ProcessFamily.SecondLaw (.erase b.proc) (.erasure uniformBinary)) :
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
