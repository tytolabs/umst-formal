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

  Scale ladder (vision §7): quantum → stochastic → continuum. Maps are **named** here
  with conditions or **typed absence** when the carrier is not in L₀.

  Zero Lean `axiom` / `sorry`. Imports `Process` only.
-/

import Process

open UMST.ProcessFamily UMST.LandauerLaw

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
-- SECTION 2: Esposito conditions — SecondLaw(fine) → SecondLaw(coarse)
-- ================================================================

/-- **Esposito coarse-graining conditions** (PRE 85, 041125).

    Entropy production at the coarse description is a lower bound on the fine one;
    at the predicate level this is: fine `SecondLaw` ⇒ coarse `SecondLaw` for the
    paired images under `cg`. Timescale separation and Markovian projection are
    **not** encoded in L₀ — they appear only as external hypotheses bundled here. -/
def EspositoCoarseGrainingConditions (cg : CoarseGrainMap) : Prop :=
  ∀ (p : Process) (pr : Prior), SecondLaw p pr → SecondLaw (cg.mapProcess p) (cg.mapPrior pr)

/-- Fine admissibility implies coarse admissibility under Esposito conditions. -/
theorem secondLaw_coarse_from_fine (cg : CoarseGrainMap) (hEsp : EspositoCoarseGrainingConditions cg)
    (p : Process) (pr : Prior) (hFine : SecondLaw p pr) :
    SecondLaw (cg.mapProcess p) (cg.mapPrior pr) :=
  hEsp p pr hFine

theorem espinositoConditions_id : EspositoCoarseGrainingConditions idCoarseGrainMap :=
  fun _ _ h => h

theorem secondLaw_coarse_from_fine_id (p : Process) (pr : Prior) (hFine : SecondLaw p pr) :
    SecondLaw (idCoarseGrainMap.mapProcess p) (idCoarseGrainMap.mapPrior pr) :=
  secondLaw_coarse_from_fine idCoarseGrainMap espinositoConditions_id p pr hFine

theorem espinositoConditions_comp (f g : CoarseGrainMap)
    (hf : EspositoCoarseGrainingConditions f) (hg : EspositoCoarseGrainingConditions g) :
    EspositoCoarseGrainingConditions (g.comp f) := by
  intro p pr hFine
  exact hg (f.mapProcess p) (f.mapPrior pr) (hf p pr hFine)

theorem secondLaw_coarse_from_fine_comp (f g : CoarseGrainMap)
    (hf : EspositoCoarseGrainingConditions f) (hg : EspositoCoarseGrainingConditions g)
    (p : Process) (pr : Prior) (hFine : SecondLaw p pr) :
    SecondLaw ((g.comp f).mapProcess p) ((g.comp f).mapPrior pr) :=
  secondLaw_coarse_from_fine (g.comp f) (espinositoConditions_comp f g hf hg) p pr hFine

/-- Contrapositive: a coarse-scale **refusal** is sound — violation at coarse would
    contradict fine admissibility under Esposito conditions. -/
theorem coarse_refusal_sound (cg : CoarseGrainMap) (hEsp : EspositoCoarseGrainingConditions cg)
    (p : Process) (pr : Prior) :
    ¬ SecondLaw (cg.mapProcess p) (cg.mapPrior pr) → ¬ SecondLaw p pr := by
  intro hCoarseBad hFine
  exact hCoarseBad (hEsp p pr hFine)

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

/-- Stochastic-layer identity (double-slit / UCRS carriers live outside this module). -/
def scaleMapStochasticIdentity : ScaleMapRegistration :=
  .implemented .stochastic_to_continuum idCoarseGrainMap espinositoConditions_id

theorem scaleMapQuantumToStochastic_absent :
    ∃ r, scaleMapQuantumToStochastic = .absent .quantum_to_stochastic r :=
  ⟨ScaleMapAbsenceReason.quantum_cptp_not_in_process_family, rfl⟩

theorem scaleMapStochasticToContinuum_absent :
    ∃ r, scaleMapStochasticToContinuum = .absent .stochastic_to_continuum r :=
  ⟨ScaleMapAbsenceReason.stochastic_to_continuum_generic_not_linked, rfl⟩

theorem scaleMapQuantumToContinuumDirect_absent :
    ∃ r, scaleMapQuantumToContinuumDirect = .absent .quantum_to_continuum_direct r :=
  ⟨ScaleMapAbsenceReason.quantum_to_continuum_skips_meso, rfl⟩

theorem scaleMapStochasticIdentity_implemented :
    ∃ cg h, scaleMapStochasticIdentity = .implemented .stochastic_to_continuum cg h :=
  ⟨idCoarseGrainMap, espinositoConditions_id, rfl⟩

/-- Cross-scale composition is monotone when each edge satisfies Esposito conditions. -/
theorem scale_ladder_compose_second_law (f g : CoarseGrainMap)
    (hf : EspositoCoarseGrainingConditions f) (hg : EspositoCoarseGrainingConditions g)
    (p : Process) (pr : Prior) (hFine : SecondLaw p pr) :
    SecondLaw ((g.comp f).mapProcess p) ((g.comp f).mapPrior pr) :=
  secondLaw_coarse_from_fine_comp f g hf hg p pr hFine

theorem coarse_graining_p0_12_satisfiable :
    ∃ cg, EspositoCoarseGrainingConditions cg :=
  ⟨idCoarseGrainMap, espinositoConditions_id⟩

end UMST.CoarseGraining
