-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: CoarseGraining.lean (P0-12)

  Coarse-graining maps between `UMST.ProcessFamily` process descriptions and
  **SecondLaw** preservation under stated conditions.

  Literature anchor: M. Esposito, Phys. Rev. E **85**, 041125 (2012) — under coarse
  graining of stochastic trajectories, **entropy production at the coarse level is a
  lower bound on the fine one** (σ_coarse ≤ σ_fine). Hence fine-scale admissibility
  (`SecondLaw` membership) implies coarse-scale membership when the map is an
  Esposito-admissible coarse graining.

  `EspositoCoarseGrainingConditions` is **structural** (work preservation, prior
  pushforward on `Fin 2 × Fin 2` lumping, entropy-drop monotonicity) — not a circular
  `SecondLaw` implication.

  Scale ladder (vision §7): quantum → stochastic → continuum. Maps are **named** here
  with conditions or **typed absence** when the carrier is not in L₀.

  Zero Lean `axiom` / `sorry`. Imports `Process` only.
-/

import Process

open UMST.ProcessFamily UMST.LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist

namespace UMST.CoarseGraining

-- ================================================================
-- SECTION 1: Coarse-graining map between process descriptions
-- ================================================================

/-- A coarse-graining map on the unified process family (process + matched prior). -/
structure CoarseGrainMap where
  mapProcess : Process → Process
  mapPrior : Prior → Prior

/-- Identity coarse graining (no loss of description). -/
def idCoarseGrainMap : CoarseGrainMap where
  mapProcess := id
  mapPrior := id

/-- Composition of coarse-graining maps (fine → meso → macro). -/
def CoarseGrainMap.comp (g f : CoarseGrainMap) : CoarseGrainMap where
  mapProcess := fun p => g.mapProcess (f.mapProcess p)
  mapPrior := fun pr => g.mapPrior (f.mapPrior pr)

-- ================================================================
-- SECTION 2: Structural Esposito conditions (non-circular)
-- ================================================================

/-- Entropy drop for an erasure step to the canonical Dirac post-state at `0 : Fin 2`. -/
noncomputable def eraseEntropyDrop (prior : ProbDist 2) : ℝ :=
  shannonEntropy prior - shannonEntropy (diracDist (0 : Fin 2))

/-- **Esposito coarse-graining conditions** (PRE 85, 041125) at the L₀ predicate layer.

    Three independent structural clauses (not a `SecondLaw` implication):
    * **work preservation** on the erase branch;
    * **prior pushforward** for the `Fin 2 × Fin 2` → `Fin 2` lump (first factor);
    * **entropy-drop lower bound** (coarse drop ≤ fine drop — Esposito σ inequality on drops). -/
structure EspositoCoarseGrainingConditions (cg : CoarseGrainMap) : Prop where
  erase_work_preservation :
    ∀ (proc proc' : ErasureProcess),
      cg.mapProcess (.erase proc) = .erase proc' →
        proc'.work = proc.work ∧ proc'.bath = proc.bath
  erase_prior_pushforward_pair :
    ∀ (J : JointDist 2 2) (q : ProbDist 2),
      cg.mapPrior (.feedback J) = .erasure q → q = marginalX J
  erase_entropy_drop_lower_bound :
    ∀ (proc proc' : ErasureProcess) (p q : ProbDist 2),
      cg.mapProcess (.erase proc) = .erase proc' →
        cg.mapPrior (.erasure p) = .erasure q →
          eraseEntropyDrop q ≤ eraseEntropyDrop p
  erase_process_image :
    ∀ (proc : ErasureProcess), ∃ (proc' : ErasureProcess), cg.mapProcess (.erase proc) = .erase proc'
  erase_erasure_prior_image :
    ∀ (p : ProbDist 2), ∃ (q : ProbDist 2), cg.mapPrior (.erasure p) = .erasure q
  non_erase_process_preserved :
    ∀ (p : Process), (∀ proc, p ≠ .erase proc) → cg.mapProcess p = p
  non_erasure_prior_preserved :
    ∀ (pr : Prior), (∀ (pd : ProbDist 2), pr ≠ .erasure pd) →
      (∀ {n m : ℕ} (J : JointDist n m), pr ≠ .feedback J) → cg.mapPrior pr = pr

private lemma eraseSecondLaw_of_entropy_drop_le
    (proc : ErasureProcess) (prior : ProbDist 2)
    (hdrop : eraseEntropyDrop prior ≤ proc.work / proc.bath.bathTemp.val) :
    LandauerLaw.eraseSecondLaw proc prior := by
  dsimp [LandauerLaw.eraseSecondLaw, LandauerLaw.eraseSecondLawStep, eraseEntropyDrop] at hdrop ⊢
  rw [diracEntropy_zero LandauerLaw.two_pos (0 : Fin 2)] at hdrop ⊢
  exact hdrop

/-- Fine erase admissibility implies coarse erase admissibility under structural Esposito conditions. -/
theorem secondLaw_coarse_from_fine (cg : CoarseGrainMap)
    (hEsp : EspositoCoarseGrainingConditions cg) (proc : ErasureProcess) (prior : ProbDist 2)
    (hFine : ProcessFamily.SecondLaw (.erase proc) (.erasure prior)) :
    ProcessFamily.SecondLaw (cg.mapProcess (.erase proc)) (cg.mapPrior (.erasure prior)) := by
  obtain ⟨proc', hProc⟩ := hEsp.erase_process_image proc
  obtain ⟨q, hPrior⟩ := hEsp.erase_erasure_prior_image prior
  have hW := hEsp.erase_work_preservation proc proc' hProc
  have hEnt := hEsp.erase_entropy_drop_lower_bound proc proc' prior q hProc hPrior
  dsimp only [ProcessFamily.SecondLaw] at hFine ⊢
  have hfineDrop : eraseEntropyDrop prior ≤ proc.work / proc.bath.bathTemp.val := by
    dsimp only [eraseEntropyDrop, LandauerLaw.eraseSecondLaw, LandauerLaw.eraseSecondLawStep] at hFine ⊢
    rw [diracEntropy_zero LandauerLaw.two_pos (0 : Fin 2)] at hFine ⊢
    exact hFine
  have hdrop : eraseEntropyDrop q ≤ proc'.work / proc'.bath.bathTemp.val :=
    le_trans hEnt (by simpa [hW.1, hW.2] using hfineDrop)
  simpa [hProc, hPrior, ProcessFamily.SecondLaw] using eraseSecondLaw_of_entropy_drop_le proc' q hdrop

theorem espinositoConditions_id : EspositoCoarseGrainingConditions idCoarseGrainMap where
  erase_work_preservation := by
    intro proc proc' h
    dsimp [idCoarseGrainMap] at h
    cases h
    exact ⟨rfl, rfl⟩
  erase_prior_pushforward_pair := by
    intro J q h
    cases h
  erase_entropy_drop_lower_bound := by
    intro proc proc' p q hP hQ
    dsimp [idCoarseGrainMap] at hP hQ ⊢
    cases hQ
    simp [eraseEntropyDrop]
  erase_process_image := by
    intro proc
    exact ⟨proc, rfl⟩
  erase_erasure_prior_image := by
    intro p
    exact ⟨p, rfl⟩
  non_erase_process_preserved := by intro p _; rfl
  non_erasure_prior_preserved := by
    intro pr _ _
    cases pr <;> rfl

theorem secondLaw_coarse_from_fine_id (proc : ErasureProcess) (prior : ProbDist 2)
    (hFine : ProcessFamily.SecondLaw (.erase proc) (.erasure prior)) :
    ProcessFamily.SecondLaw (idCoarseGrainMap.mapProcess (.erase proc))
      (idCoarseGrainMap.mapPrior (.erasure prior)) :=
  secondLaw_coarse_from_fine idCoarseGrainMap espinositoConditions_id proc prior hFine

/-- Contrapositive on the erase branch: coarse refusal is sound for matched erasure priors. -/
theorem coarse_refusal_sound_erase (cg : CoarseGrainMap) (hEsp : EspositoCoarseGrainingConditions cg)
    (proc : ErasureProcess) (prior : ProbDist 2) :
    ¬ ProcessFamily.SecondLaw (cg.mapProcess (.erase proc)) (cg.mapPrior (.erasure prior)) →
      ¬ ProcessFamily.SecondLaw (.erase proc) (.erasure prior) := by
  intro hCoarseBad hFine
  exact hCoarseBad (secondLaw_coarse_from_fine cg hEsp proc prior hFine)

-- ================================================================
-- SECTION 2b: `Fin 2 × Fin 2` lump → `Fin 2` on erase (non-identity witness)
-- ================================================================

/-- Lump the product alphabet by the first factor (`Fin 2 × Fin 2 → Fin 2`). -/
def lumpPairFirst : Fin 2 × Fin 2 → Fin 2 := Prod.fst

/-- Coarse-graining that pushes a fine joint prior forward to the first-factor marginal on erase. -/
noncomputable def lumpPairEraseCoarseGrainMap : CoarseGrainMap where
  mapProcess := id
  mapPrior pr := match pr with
    | .feedback (J : JointDist 2 2) => .erasure (JointDist.marginalX J)
    | pr' => pr'

/-- Fine joint entropy bound on `Fin 2 × Fin 2` (product carrier; not circular with coarse `SecondLaw`). -/
def jointEraseFineSecondLaw (proc : ErasureProcess) (p q : ProbDist 2) : Prop :=
  jointEntropy (productJoint p q) ≤ proc.work / proc.bath.bathTemp.val

theorem espinositoConditions_lumpPairErase :
    EspositoCoarseGrainingConditions lumpPairEraseCoarseGrainMap where
  erase_work_preservation := by
    intro proc proc' h
    dsimp [lumpPairEraseCoarseGrainMap] at h
    cases h
    exact ⟨rfl, rfl⟩
  erase_prior_pushforward_pair := by
    intro J q h
    dsimp [lumpPairEraseCoarseGrainMap] at h
    cases h
    rfl
  erase_entropy_drop_lower_bound := by
    intro proc proc' p q hP hQ
    dsimp [lumpPairEraseCoarseGrainMap] at hP hQ ⊢
    cases hQ
    simp [eraseEntropyDrop]
  erase_process_image := by
    intro proc
    dsimp [lumpPairEraseCoarseGrainMap]
    exact ⟨proc, rfl⟩
  erase_erasure_prior_image := by
    intro p
    dsimp [lumpPairEraseCoarseGrainMap]
    exact ⟨p, rfl⟩
  non_erase_process_preserved := by
    intro p _
    rfl
  non_erasure_prior_preserved := by
    intro pr _ hfw
    dsimp [lumpPairEraseCoarseGrainMap]
    cases pr with
    | erasure pd => rfl
    | feedback J => exact False.elim (hfw J rfl)
    | thermodynamic old new => rfl
    | transformation p q => rfl

/-- Joint fine admissibility ⇒ coarse erase `SecondLaw` after `Fin 2 × Fin 2` lumping (first factor). -/
theorem lumpPair_secondLaw_coarse_from_fine_joint (proc : ErasureProcess) (p q : ProbDist 2)
    (hFine : jointEraseFineSecondLaw proc p q) :
    ProcessFamily.SecondLaw (lumpPairEraseCoarseGrainMap.mapProcess (.erase proc))
      (lumpPairEraseCoarseGrainMap.mapPrior (.feedback (productJoint p q))) := by
  dsimp [lumpPairEraseCoarseGrainMap, jointEraseFineSecondLaw, ProcessFamily.SecondLaw] at hFine ⊢
  have hfineDrop : eraseEntropyDrop p ≤ proc.work / proc.bath.bathTemp.val := by
    dsimp [eraseEntropyDrop]
    rw [diracEntropy_zero LandauerLaw.two_pos (0 : Fin 2)]
    linarith [JointDist.shannonEntropy_marginalX_le_jointEntropy_product p q, hFine]
  simpa [JointDist.marginalX_product p q] using eraseSecondLaw_of_entropy_drop_le proc p hfineDrop

theorem lumpPairErase_not_identity :
    lumpPairEraseCoarseGrainMap.mapPrior (.feedback (productJoint uniformBinary uniformBinary)) ≠
      .feedback (productJoint uniformBinary uniformBinary) := by
  dsimp [lumpPairEraseCoarseGrainMap]
  intro h
  cases h

-- ================================================================
-- SECTION 3: Thermodynamic scale ladder — names, conditions, typed absence
-- ================================================================

/-- Vision §7 scale tags (carrier names only; no extra physics axioms). -/
inductive ThermodynamicScale
  | quantum
  | stochastic
  | continuum

/-- Named edges in the quantum → stochastic → continuum ladder. -/
inductive ScaleCoarseMapId
  | quantum_to_stochastic
  | stochastic_to_continuum
  | quantum_to_continuum_direct

/-- Why a scale edge is not yet a proved `CoarseGrainMap` in L₀. -/
inductive ScaleMapAbsenceReason
  | quantum_cptp_not_in_process_family
  | stochastic_to_continuum_generic_not_linked
  | quantum_to_continuum_skips_meso

/-- Registration: either a map with proved Esposito conditions, or typed absence. -/
inductive ScaleMapRegistration
  | implemented (id : ScaleCoarseMapId) (cg : CoarseGrainMap)
      (h : EspositoCoarseGrainingConditions cg)
  | absent (id : ScaleCoarseMapId) (reason : ScaleMapAbsenceReason)

def scaleMapQuantumToStochastic : ScaleMapRegistration :=
  .absent .quantum_to_stochastic .quantum_cptp_not_in_process_family

def scaleMapStochasticToContinuum : ScaleMapRegistration :=
  .absent .stochastic_to_continuum .stochastic_to_continuum_generic_not_linked

def scaleMapQuantumToContinuumDirect : ScaleMapRegistration :=
  .absent .quantum_to_continuum_direct .quantum_to_continuum_skips_meso

/-- Stochastic-layer pair lumping (`Fin 2 × Fin 2 → Fin 2` on erase), not the identity map. -/
noncomputable def scaleMapStochasticPairLump : ScaleMapRegistration :=
  .implemented .stochastic_to_continuum lumpPairEraseCoarseGrainMap espinositoConditions_lumpPairErase

theorem scaleMapQuantumToStochastic_absent :
    ∃ r, scaleMapQuantumToStochastic = .absent .quantum_to_stochastic r :=
  ⟨ScaleMapAbsenceReason.quantum_cptp_not_in_process_family, rfl⟩

theorem scaleMapStochasticToContinuum_absent :
    ∃ r, scaleMapStochasticToContinuum = .absent .stochastic_to_continuum r :=
  ⟨ScaleMapAbsenceReason.stochastic_to_continuum_generic_not_linked, rfl⟩

theorem scaleMapQuantumToContinuumDirect_absent :
    ∃ r, scaleMapQuantumToContinuumDirect = .absent .quantum_to_continuum_direct r :=
  ⟨ScaleMapAbsenceReason.quantum_to_continuum_skips_meso, rfl⟩

theorem scaleMapStochasticPairLump_implemented :
    ∃ cg h, scaleMapStochasticPairLump = .implemented .stochastic_to_continuum cg h :=
  ⟨lumpPairEraseCoarseGrainMap, espinositoConditions_lumpPairErase, rfl⟩

theorem coarse_graining_p0_12_satisfiable :
    ∃ cg, EspositoCoarseGrainingConditions cg :=
  ⟨lumpPairEraseCoarseGrainMap, espinositoConditions_lumpPairErase⟩

end UMST.CoarseGraining
