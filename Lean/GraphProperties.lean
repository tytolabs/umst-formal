/-
  UMST-Formal: GraphProperties.lean
  Lean 4 — Graph-theoretic properties of the admissibility relation.

  The admissibility relation defines a directed graph on ThermodynamicState:
  - Vertices: ThermodynamicState
  - Edge (s, s') when: Admissible s s'

  Key properties proved here:
  1. MassCond is NOT transitive (formal counterexample — this is why
     admissibleTrans was an axiom and why it has been removed).
  2. The three order conditions (Clausius-Duhem, hydration, strength)
     ARE transitive (by transitivity of ≤).
  3. Strict hydration increase is acyclic (irreversibility of reaction).
  4. The accumulated bound (AdmissibleN n) correctly generalises Admissible.

  This file provides the foundational graph-theoretic justification for the
  graded admissibility model in Gate.lean §10.
-/

import Gate

namespace UMST

-- ================================================================
-- SECTION 1: Mass Non-Transitivity (Formal Counterexample)
-- ================================================================
-- The mass condition |ρ' - ρ| ≤ δMass is NOT transitive.
-- Counterexample: three states with ρ = 0, 99, 198.
--   Step 1: |99 - 0| = 99 ≤ 100 ✓
--   Step 2: |198 - 99| = 99 ≤ 100 ✓
--   Composed: |198 - 0| = 198 > 100 ✗
-- This proves admissibleTrans (the old axiom) was REFUTABLE.

/-- The mass condition is not transitive at tolerance δMass = 100. -/
theorem mass_not_transitive :
    ∃ s₁ s₂ s₃ : ThermodynamicState,
      MassCond s₁ s₂ ∧ MassCond s₂ s₃ ∧ ¬ MassCond s₁ s₃ := by
  refine ⟨⟨0, 0, 0, 0⟩, ⟨99, 0, (1/2), 0⟩, ⟨198, 0, 1, 0⟩, ?_, ?_, ?_⟩
  · -- |99 - 0| = 99 ≤ 100
    simp only [MassCond, ThermodynamicState.density, δMass]
    norm_num
  · -- |198 - 99| = 99 ≤ 100
    simp only [MassCond, ThermodynamicState.density, δMass]
    norm_num
  · -- |198 - 0| = 198 > 100
    simp only [MassCond, ThermodynamicState.density, δMass]
    norm_num

/-- The full Admissible predicate is also not transitive (same counterexample).
    This is the formal refutation of the former admissibleTrans axiom. -/
theorem admissibleTrans_refuted :
    ∃ s₁ s₂ s₃ : ThermodynamicState,
      Admissible s₁ s₂ ∧ Admissible s₂ s₃ ∧ ¬ Admissible s₁ s₃ := by
  -- Construct three states where density increases by 99 each step,
  -- hydration is non-decreasing, free energy is non-increasing, strength non-decreasing.
  -- psiAntitone and fcMonotone are required for Admissible but here we use
  -- states where freeEnergy is already non-increasing and strength non-decreasing.
  refine ⟨⟨0, 0, 0, 0⟩, ⟨99, -225, 1/2, 50⟩, ⟨198, -450, 1, 100⟩, ?_, ?_, ?_⟩
  · -- Admissible s₁ s₂
    constructor
    · simp [MassCond, ThermodynamicState.density, δMass]; try norm_num
    · simp [DissipCond, ThermodynamicState.freeEnergy]; try norm_num
    · simp [HydratCond, ThermodynamicState.hydration]; try norm_num
    · simp [StrengthCond, ThermodynamicState.strength]; try norm_num
  · -- Admissible s₂ s₃
    constructor
    · simp [MassCond, ThermodynamicState.density, δMass]; try norm_num
    · simp [DissipCond, ThermodynamicState.freeEnergy]; try norm_num
    · simp [HydratCond, ThermodynamicState.hydration]; try norm_num
    · simp [StrengthCond, ThermodynamicState.strength]; try norm_num
  · -- ¬ Admissible s₁ s₃ (mass condition fails)
    intro h
    have := h.massDensity
    simp [MassCond, ThermodynamicState.density, δMass] at this
    norm_num at this

-- ================================================================
-- SECTION 2: Order Conditions ARE Transitive
-- ================================================================
-- Unlike the mass condition, the three order-theoretic invariants
-- (Clausius-Duhem, hydration, strength) are transitive because they
-- reduce to transitivity of ≤ on ℚ.

/-- Clausius-Duhem (dissipation) condition is transitive. -/
theorem dissipCond_transitive {s₁ s₂ s₃ : ThermodynamicState}
    (h₁₂ : DissipCond s₁ s₂) (h₂₃ : DissipCond s₂ s₃) :
    DissipCond s₁ s₃ :=
  le_trans h₂₃ h₁₂

/-- Hydration irreversibility condition is transitive. -/
theorem hydratCond_transitive {s₁ s₂ s₃ : ThermodynamicState}
    (h₁₂ : HydratCond s₁ s₂) (h₂₃ : HydratCond s₂ s₃) :
    HydratCond s₁ s₃ :=
  le_trans h₁₂ h₂₃

/-- Strength monotonicity condition is transitive. -/
theorem strengthCond_transitive {s₁ s₂ s₃ : ThermodynamicState}
    (h₁₂ : StrengthCond s₁ s₂) (h₂₃ : StrengthCond s₂ s₃) :
    StrengthCond s₁ s₃ :=
  le_trans h₁₂ h₂₃

-- ================================================================
-- SECTION 3: Hydration Acyclicity (DAG Property)
-- ================================================================
-- Strict hydration increase implies no return path.
-- This formalises the physical irreversibility of the hydration reaction.

/-- If hydration strictly increases in a transition, the reverse transition
    is impossible (it would require hydration to decrease). -/
theorem hydration_acyclic {s s' : ThermodynamicState}
    (_hfwd : Admissible s s') (hstrict : s.hydration < s'.hydration) :
    ¬ Admissible s' s := by
  intro hrev
  have hback := hrev.hydrationMono  -- s'.hydration ≤ s.hydration
  linarith

/-- A strictly-hydrating path cannot return to its start. -/
theorem hydration_dag_path {s₀ s₁ : ThermodynamicState}
    (h₀₁ : Admissible s₀ s₁) (h₁₀ : Admissible s₁ s₀)
    (hstrict : s₀.hydration < s₁.hydration) : False := by
  exact hydration_acyclic h₀₁ hstrict h₁₀

-- ================================================================
-- SECTION 4: Admissibility is Reflexive but not Symmetric
-- ================================================================

/-- The admissibility relation is NOT symmetric in general.
    Hydration irreversibility prevents reversal of forward-hydrating transitions. -/
theorem admissible_not_symmetric :
    ∃ s s' : ThermodynamicState, Admissible s s' ∧ ¬ Admissible s' s := by
  refine ⟨⟨2300, 0, 0, 0⟩, ⟨2300, -225, 1/2, 50⟩, ?_, ?_⟩
  · -- Admissible s s' (forward hydration)
    constructor
    · simp [MassCond, ThermodynamicState.density, δMass]; try norm_num
    · simp [DissipCond, ThermodynamicState.freeEnergy]; try norm_num
    · simp [HydratCond, ThermodynamicState.hydration]; try norm_num
    · simp [StrengthCond, ThermodynamicState.strength]; try norm_num
  · -- ¬ Admissible s' s (hydration would decrease)
    intro h
    have := h.hydrationMono
    simp [HydratCond, ThermodynamicState.hydration] at this
    norm_num at this

-- ================================================================
-- SECTION 5: Graded Composition Correctness
-- ================================================================

/-- Sanity check: two 1-step admissible transitions compose to a 2-step. -/
theorem graded_compose_sanity
    {s s' s'' : ThermodynamicState}
    (h₁ : Admissible s s') (h₂ : Admissible s' s'') :
    AdmissibleN 2 s s'' := by
  have h₁' := (admissible_iff_admissibleN1 s s').mp h₁
  have h₂' := (admissible_iff_admissibleN1 s' s'').mp h₂
  have := admissibleN_compose h₁' h₂'
  simpa using this

/-- The accumulated mass bound for two steps is at most 2 * δMass. -/
theorem two_step_mass_bound
    {s s' s'' : ThermodynamicState}
    (h₁ : Admissible s s') (h₂ : Admissible s' s'') :
    |s''.density - s.density| ≤ 2 * δMass := by
  have := (graded_compose_sanity h₁ h₂).massDensity
  simpa using this

end UMST
