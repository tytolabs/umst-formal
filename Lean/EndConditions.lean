/-
  UMST-Formal: EndConditions.lean
  Lean 4 — Terminal thermodynamic state conditions and invariants
  
  This module constructs:
  1. accumulatedMassBound: generalization of mass accumulation over N steps
  2. clausiusDuhemGlobal: total dissipation bound over N steps
  3. equilibriumExists: formal proof of a stopping condition (hydration = 1)
-/

import Gate
import GraphProperties

namespace UMST

open Rat

-- ================================================================
-- SECTION 1: Accumulated Mass Bound
-- ================================================================

/-- Over an N-step admissible path, the total mass variation is bounded
    by N * δMass. This is an explicit projection of AdmissibleN's
    correctness. -/
theorem accumulatedMassBound {n : ℕ} {s_start s_end : ThermodynamicState}
    (H : AdmissibleN n s_start s_end) :
    |s_end.density - s_start.density| ≤ (n : ℚ) * δMass :=
  H.massDensity

-- ================================================================
-- SECTION 2: Global Clausius-Duhem Dissipation
-- ================================================================

/-- The total Helmholtz free energy always drops or is constant over
    an N-step path, guaranteeing monotonic global dissipation. -/
theorem clausiusDuhemGlobal {n : ℕ} {s_start s_end : ThermodynamicState}
    (H : AdmissibleN n s_start s_end) :
    s_end.freeEnergy ≤ s_start.freeEnergy :=
  H.clausiusDuhem

-- ================================================================
-- SECTION 3: Terminal Equilibrium State
-- ================================================================

/-- A state is in strict equilibrium if no strict transition can occur;
    any admissible transition from it preserves the hydration state exactly. -/
def IsEquilibrium (s : ThermodynamicState) : Prop :=
  ∀ s', Admissible s s' → s'.hydration = s.hydration

/-- In models that physically bound hydration (e.g. α ≤ 1), a fully
    hydrated state acts as a formal terminal equilibrium. -/
theorem equilibriumExists (bound : ∀ s : ThermodynamicState, s.hydration ≤ 1) :
    ∃ s : ThermodynamicState, s.hydration = 1 ∧ IsEquilibrium s := by
  let s_eq : ThermodynamicState := ⟨0, 0, 1, 0⟩
  use s_eq
  constructor
  · rfl
  · intro s' h_adm
    have h_mono := h_adm.hydrationMono
    have h_bound := bound s'
    exact le_antisymm h_bound h_mono

end UMST
