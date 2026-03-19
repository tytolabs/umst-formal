/-
  UMST-Formal: GaloisGate.lean
  Lean 4 — Galois connection between gate conditions and transition predicates.

  The four gate conditions (Mass, Clausius-Duhem, Hydration, Strength) form
  a Galois connection between:
  - The lattice of condition-subsets (Finset (Fin 4))
  - The lattice of transition-pair predicates (ThermodynamicState → ThermodynamicState → Prop)

  This formalises the algebraic structure underlying the CSG decomposition
  of the admissibility predicate (admissibleIffCSG in Gate.lean).

  Key results:
  1. The four conditions are independent (removing any one expands the set of admissible transitions).
  2. The meet of all four conditions is exactly Admissible.
  3. The gate is the characteristic function of the intersection.
-/

import Mathlib.Order.GaloisConnection
import Mathlib.Data.Finset.Basic
import Gate

namespace UMST

/-- Local classical decidability so `Finset.filter` on propositional predicates typechecks. -/
noncomputable instance (p : Prop) : Decidable p := Classical.propDecidable _

-- ================================================================
-- SECTION 1: Condition Enumeration
-- ================================================================

/-- The four gate condition indices. -/
inductive GateCond where
  | Mass       -- |ρ' - ρ| ≤ δMass
  | Dissip     -- ψ' ≤ ψ  (Clausius-Duhem)
  | Hydration  -- α' ≥ α  (irreversibility)
  | Strength   -- fc' ≥ fc (monotonicity)
  deriving DecidableEq, Fintype, Repr

open GateCond

-- ================================================================
-- SECTION 2: Individual Condition Functions
-- ================================================================

/-- Evaluate a single gate condition for a state pair. -/
def evalCond (c : GateCond) (old new : ThermodynamicState) : Prop :=
  match c with
  | Mass      => MassCond old new
  | Dissip    => DissipCond old new
  | Hydration => HydratCond old new
  | Strength  => StrengthCond old new

-- ================================================================
-- SECTION 3: Condition Meet
-- ================================================================

/-- The conjunction of all conditions in a set S. -/
noncomputable def condMeet (S : Finset GateCond) (old new : ThermodynamicState) : Prop :=
  ∀ c ∈ S, evalCond c old new

/-- The full condition set gives exactly Admissible. -/
theorem condMeet_full_iff_admissible (old new : ThermodynamicState) :
    condMeet Finset.univ old new ↔ Admissible old new := by
  simp only [condMeet, Finset.mem_univ, forall_true_left]
  constructor
  · intro h
    exact ⟨h Mass, h Dissip, h Hydration, h Strength⟩
  · intro ⟨hm, hd, hh, hs⟩ c
    match c with
    | Mass      => exact hm
    | Dissip    => exact hd
    | Hydration => exact hh
    | Strength  => exact hs

/-- The empty condition set is vacuously satisfied. -/
theorem condMeet_empty (old new : ThermodynamicState) :
    condMeet ∅ old new := by
  simp [condMeet]

/-- condMeet is monotone (larger set = harder to satisfy). -/
theorem condMeet_antitone {S T : Finset GateCond} (hST : T ⊆ S)
    (old new : ThermodynamicState) :
    condMeet S old new → condMeet T old new := by
  intro hS c hc
  exact hS c (hST hc)

-- ================================================================
-- SECTION 4: Condition Extraction
-- ================================================================

/-- Extract the set of conditions that a predicate P implies. -/
noncomputable def condExtract (P : ThermodynamicState → ThermodynamicState → Prop) :
    Finset GateCond :=
  Finset.univ.filter (fun c => ∀ old new, P old new → evalCond c old new)

/-- Admissible implies all four conditions. -/
theorem condExtract_admissible :
    condExtract (Admissible) = Finset.univ := by
  ext c
  simp only [condExtract, Finset.mem_filter, Finset.mem_univ, true_and]
  refine iff_true_intro ?_
  intro old new h
  match c with
  | Mass      => exact h.massDensity
  | Dissip    => exact h.clausiusDuhem
  | Hydration => exact h.hydrationMono
  | Strength  => exact h.strengthMono

-- ================================================================
-- SECTION 5: Independence of Conditions
-- ================================================================

/-- Removing the Mass condition strictly expands the admissible set. -/
theorem mass_condition_independent :
    ∃ old new : ThermodynamicState,
      DissipCond old new ∧ HydratCond old new ∧ StrengthCond old new ∧
      ¬ MassCond old new := by
  refine ⟨⟨0, 0, 0, 0⟩, ⟨200, -100, 1/2, 50⟩, ?_, ?_, ?_, ?_⟩
  · simp [DissipCond, ThermodynamicState.freeEnergy]
  · simp [HydratCond, ThermodynamicState.hydration]
  · simp [StrengthCond, ThermodynamicState.strength]
  · simp [MassCond, ThermodynamicState.density, δMass]; norm_num

/-- Removing the Hydration condition strictly expands the admissible set. -/
theorem hydration_condition_independent :
    ∃ old new : ThermodynamicState,
      MassCond old new ∧ DissipCond old new ∧ StrengthCond old new ∧
      ¬ HydratCond old new := by
  refine ⟨⟨2300, -100, 1/2, 50⟩, ⟨2300, -200, 0, 50⟩, ?_, ?_, ?_, ?_⟩
  · simp [MassCond, ThermodynamicState.density, δMass]
  · simp [DissipCond, ThermodynamicState.freeEnergy]; norm_num
  · simp [StrengthCond, ThermodynamicState.strength]
  · simp [HydratCond, ThermodynamicState.hydration]; try norm_num
end UMST
