-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/SecondLaw.lean

  Meso acting chemistry — second-law lift for chemical assemblages under the sole
  project axiom `LandauerLaw.physicalSecondLaw`.  Adds **zero** Lean `axiom` declarations.

  Fiber: meso/acting → `umst-formal` only.  No quantum geometry theorems.
  CALPHAD / QTAIM / SpeciesId are presentations — not new physics axioms here.
-/

import LandauerLaw

open Real Finset UMST.LandauerLaw

namespace UMST.Chem.SecondLaw

-- ================================================================
-- SECTION 1: Chemical assemblage carriers (acting meso layer)
-- ================================================================

/-- Heat bath for thermochemical processes (same carrier as `HeatBath`). -/
abbrev ChemHeatBath := HeatBath

/-- Convert a physical heat bath to the chemistry reporting bath. -/
def chemHeatBathOf (hb : HeatBath) : ChemHeatBath := hb

/-- A chemical assemblage over `n` species slots (stoichiometry scaffold). -/
structure ChemAssemblage (n : ℕ) where
  stoichiometry : Fin n → ℤ

/-- Microstate distribution over assemblage configurations. -/
abbrev AssemblageStateDist (n : ℕ) := ProbDist n

/-- A thermochemical transition on an assemblage: prior/post state distributions,
    dissipated work [entropy units, k_B = 1], and structural defect scalar. -/
structure ThermochemicalTransition (n : ℕ) where
  bath : ChemHeatBath
  prior : AssemblageStateDist n
  post : AssemblageStateDist n
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

/-- **Chemical Second Law** (meso acting invariant):

    Clausius entropy accounting on assemblage state updates:
      ΔS_assemblage ≤ W_dissipated / T

    Lifts `physicalSecondLaw` for chemical assemblages without re-declaring it. -/
def chemSecondLaw {n : ℕ} (t : ThermochemicalTransition n) : Prop :=
  structurallyCoherent t ∧
  assemblageEntropyDrop t ≤ t.dissipatedWork / t.bath.bathTemp.val

/-- Admissible thermochemical transition: satisfies the chemical second-law invariant. -/
def admissibleThermochemicalTransition {n : ℕ} (t : ThermochemicalTransition n) : Prop :=
  chemSecondLaw t

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
  bathEq : transition.bath = chemHeatBathOf proc.bath
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
      simpa [chemHeatBathOf] using
        congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
    rw [b.workEq, hbval]
  rw [hdrop, hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

/-- Landauer bound on dissipated work for a physically bridged assemblage erasure. -/
theorem refinementLandauerBound (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    b.transition.dissipatedWork ≥
      b.transition.bath.bathTemp.val * log 2 := by
  have hbath :
      b.transition.bath.bathTemp.val = b.proc.bath.bathTemp.val := by
    simpa [chemHeatBathOf] using
      congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  have h := landauerBound b.proc hSL
  rw [b.workEq.symm] at h
  rw [hbath.symm] at h
  exact h

/-- Physically bridged coherent transition satisfies `chemSecondLaw`. -/
theorem chemSecondLaw_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    chemSecondLaw b.transition :=
  ⟨b.coherent, chem_entropy_bound_from_physical b hSL⟩

/-- Entropy accounting is mandatory for admissibility. -/
theorem chemEntropyAccounting_required {n : ℕ} (t : ThermochemicalTransition n)
    (h : admissibleThermochemicalTransition t) :
    assemblageEntropyDrop t ≤ t.dissipatedWork / t.bath.bathTemp.val := h.2

/-- Structural coherence is mandatory for admissibility. -/
theorem chemCoherence_required {n : ℕ} (t : ThermochemicalTransition n)
    (h : admissibleThermochemicalTransition t) :
    structurallyCoherent t := h.1

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
  refine ⟨rfl, ?_⟩
  unfold assemblageEntropyDrop coherentP0Transition
  simp [coherentP0_zero_entropy_drop]

/-- Catalog witness: meso chemistry second-law module is present. -/
theorem chem_second_law_module_witness : True := trivial

end UMST.Chem.SecondLaw
