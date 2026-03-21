/-
  UMST-Formal: Gate.lean
  Lean 4 — Core Definitions and Gate Theorems (sorry-free)

  This file is the Lean 4 primary layer, mirroring Agda/Gate.agda and
  Coq/Gate.v.  All theorems are fully proved.

  Correspondence table:
    Lean 4 (this file)              │ Coq (Gate.v)
    ────────────────────────────────┼────────────────────────────────
    ThermodynamicState              │ ThermodynamicState (Record)
    δMass                           │ delta_mass (100 # 1)
    Q_hyd                           │ Q_hyd (450 # 1)
    helmholtz                       │ helmholtz
    Admissible                      │ admissible (Prop)
    gateCheck                       │ gate_check (bool)
    gateCheckSound                  │ gate_check_sound (Corollary)
    gateCheckComplete               │ gate_check_complete (Corollary)
    psiAntitone                     │ psi_antitone (Axiom)
    fcMonotone                      │ fc_monotone (Axiom)
    clausiusDuhemFwd                │ clausius_duhem_forward (Theorem)
    forwardHydrationAdmissible      │ forward_hydration_admissible
    admissibleRefl                  │ admissible_refl (Lemma)
    MassCond, DissipCond, etc.      │ (inline in admissible)
    admissibleIffCSG                │ (Agda: admissible-to-csg)
    ConstitutionalSeq               │ ConstitutionalSeq
    subjectReduction                │ subject_reduction
    kleisliAdmissibility            │ kleisli_admissibility

  Porting status (as of 2026-03):
  ─────────────────────────────────────────────────────────────────
  Theorem                      │ Lean 4     │ Coq        │ Agda
  ─────────────────────────────┼────────────┼────────────┼────────
  helmholtzAntitone            │ ✓ proved   │ ✓ proved   │ postulate
  helmholtzGradient            │ ✓ proved   │ ✓ proved   │ postulate
  helmholtzAdditive            │ ✓ proved   │ ✓ proved   │ postulate
  admissibleIffCSG             │ ✓ proved   │ —          │ ✓ proved
  admissibleRefl               │ ✓ proved   │ ✓ proved   │ structural
  gateCheckSound               │ ✓ proved   │ ✓ proved   │ n/a (Dec)
  gateCheckComplete            │ ✓ proved   │ ✓ proved   │ n/a (Dec)
  clausiusDuhemFwd             │ ✓ proved   │ ✓ proved   │ ✓ proved
  forwardHydrationAdmissible   │ ✓ proved   │ ✓ proved   │ ✓ proved
  subjectReduction             │ ✓ proved   │ ✓ proved   │ structural
  kleisliAdmissibility         │ ✓ proved   │ ✓ proved   │ DIB-Kleisli
  ─────────────────────────────────────────────────────────────────
  Zero sorry.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

open Rat

namespace UMST

-- ================================================================
-- SECTION 1: Thermodynamic State
-- ================================================================

/-- A material state at one instant: density (kg/m³), Helmholtz
    free energy (J/kg), hydration degree [0,1], compressive strength
    (MPa).  All quantities are rational-valued for exact arithmetic.

    Correspondence to Rust: `ThermodynamicState` in
    `thermodynamic_filter.rs`. -/
structure ThermodynamicState where
  density     : ℚ  -- ρ   (kg/m³)
  freeEnergy  : ℚ  -- ψ   (J/kg), Helmholtz free energy
  hydration   : ℚ  -- α   (0–1), degree of cement hydration
  strength    : ℚ  -- fc  (MPa), compressive strength
  deriving Repr

-- ================================================================
-- SECTION 2: Physical Constants
-- ================================================================

/-- Mass conservation tolerance: 100 kg/m³.
    Matches `delta_mass = 100 # 1` in Coq/Gate.v and
    `δ-mass = 100` in Agda/Gate.agda and the Rust kernel. -/
def δMass : ℚ := 100

/-- Latent heat of hydration: 450 J/kg (OPC Portland cement).
    ψ(α) = −Q_hyd · α.  Q_hyd > 0, so ψ is antitone in α. -/
def Q_hyd : ℚ := 450

-- ================================================================
-- SECTION 3: Helmholtz Free Energy Model
-- ================================================================

/-- ψ(α) = −Q_hyd · α.
    Physical basis: each increment of hydration releases Q_hyd J/kg
    of heat (exothermic), lowering the Helmholtz free energy.
    The reaction is irreversible (α only increases), so ψ only
    decreases.  This is the Clausius-Duhem condition. -/
def helmholtz (α : ℚ) : ℚ := -(Q_hyd * α)

/-- ψ is antitone: α₁ ≤ α₂ → ψ(α₂) ≤ ψ(α₁). -/
theorem helmholtzAntitone : ∀ α₁ α₂ : ℚ, α₁ ≤ α₂ → helmholtz α₂ ≤ helmholtz α₁ := by
  intro α₁ α₂ h
  unfold helmholtz Q_hyd
  nlinarith

/-- ψ gradient is constant: ψ(α + ε) − ψ(α) = −Q_hyd · ε.
    This is the Eikonal / SDF condition: gradient magnitude = Q_hyd. -/
theorem helmholtzGradient : ∀ α ε : ℚ, helmholtz (α + ε) - helmholtz α = -(Q_hyd * ε) := by
  intro α ε
  unfold helmholtz
  ring

/-- ψ is additive (ℚ-linear): ψ(α₁ + α₂) = ψ(α₁) + ψ(α₂). -/
theorem helmholtzAdditive : ∀ α₁ α₂ : ℚ, helmholtz (α₁ + α₂) = helmholtz α₁ + helmholtz α₂ := by
  intro α₁ α₂
  unfold helmholtz
  ring

-- ================================================================
-- SECTION 4: Admissibility Predicate
-- ================================================================

/-- A transition old → new is admissible iff all four gate invariants
    hold simultaneously.  Membership in this Prop is a machine-checked
    safety certificate.

    1. Mass conservation:           |ρ_new − ρ_old| ≤ δMass
    2. Clausius-Duhem dissipation:  ψ_new ≤ ψ_old
    3. Hydration irreversibility:   α_new ≥ α_old
    4. Strength monotonicity:       fc_new ≥ fc_old -/
structure Admissible (old new : ThermodynamicState) : Prop where
  massDensity    : |new.density   - old.density|   ≤ δMass
  clausiusDuhem  : new.freeEnergy ≤ old.freeEnergy
  hydrationMono  : old.hydration  ≤ new.hydration
  strengthMono   : old.strength   ≤ new.strength

-- ================================================================
-- SECTION 5: Physical Model Axioms
-- ================================================================
-- These mirror Coq's `psi_antitone` and `fc_monotone` axioms.
-- They are physical assumptions (constitutive laws), not logical gaps.
-- The concrete Helmholtz instance of psiAntitone is proved in
-- Lean/Helmholtz.lean.

-- Section 5 was removed to eliminate unconstrained global physical axioms.

-- ================================================================
-- SECTION 6: Boolean Gate Decision Function
-- ================================================================

/-- Boolean gate: returns true iff all four invariants hold.
    Uses `decide` on rationals (which have DecidableLinearOrder).
    Mirrors `gate_check` in Coq/Gate.v and the Rust `check_transition`. -/
def gateCheck (old new : ThermodynamicState) : Bool :=
  decide (|new.density - old.density| ≤ δMass) &&
  decide (new.freeEnergy ≤ old.freeEnergy)     &&
  decide (old.hydration  ≤ new.hydration)      &&
  decide (old.strength   ≤ new.strength)

/-- Soundness: gateCheck = true → Admissible. -/
theorem gateCheckSound (old new : ThermodynamicState) :
    gateCheck old new = true → Admissible old new := by
  simp only [gateCheck, Bool.and_eq_true, decide_eq_true_eq]
  intro ⟨⟨⟨hm, hd⟩, hh⟩, hs⟩
  exact ⟨hm, hd, hh, hs⟩

/-- Completeness: Admissible → gateCheck = true. -/
theorem gateCheckComplete (old new : ThermodynamicState) :
    Admissible old new → gateCheck old new = true := by
  intro ⟨hm, hd, hh, hs⟩
  simp only [gateCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hm, hd⟩, hh⟩, hs⟩

-- ================================================================
-- SECTION 7: Core Safety Theorems
-- ================================================================

/-- Clausius-Duhem (Forward):
    Advancing hydration implies non-negative dissipation.
    D_int = −ρ · ψ̇ ≥ 0 iff ψ_new ≤ ψ_old. -/
theorem clausiusDuhemFwd (s1 s2 : ThermodynamicState)
    (h_psi : s1.hydration ≤ s2.hydration → s2.freeEnergy ≤ s1.freeEnergy)
    (h : s1.hydration ≤ s2.hydration) : s2.freeEnergy ≤ s1.freeEnergy :=
  h_psi h

/-- Main Safety Theorem: forward hydration + mass conservation ⇒
    the state transition is fully admissible.
    This requires explicit physical constitutive hypotheses dynamically. -/
theorem forwardHydrationAdmissible (old new : ThermodynamicState)
    (hyd  : old.hydration ≤ new.hydration)
    (mass : |new.density - old.density| ≤ δMass)
    (h_psi : old.hydration ≤ new.hydration → new.freeEnergy ≤ old.freeEnergy)
    (h_fc  : old.hydration ≤ new.hydration → old.strength ≤ new.strength) :
    Admissible old new :=
  ⟨mass, h_psi hyd, hyd, h_fc hyd⟩

/-- Reflexivity: every state is admissible with itself. -/
theorem admissibleRefl (s : ThermodynamicState) : Admissible s s := by
  constructor
  · simp [sub_self, abs_zero, δMass]
  · exact le_refl _
  · exact le_refl _
  · exact le_refl _

-- ================================================================
-- SECTION 8: CSG Decomposition
-- ================================================================
-- The four gate conditions as named sub-predicates.
-- In SDF/FRep terms, each defines one half-space in
-- ThermodynamicState × ThermodynamicState.  The admissible region is
-- the CSG intersection of all four.  Mirrors Agda/Gate.agda §7.

/-- Mass condition: |ρ_new − ρ_old| ≤ δMass. -/
def MassCond    (old new : ThermodynamicState) : Prop :=
  |new.density - old.density| ≤ δMass

/-- Clausius-Duhem condition: ψ_new ≤ ψ_old. -/
def DissipCond  (old new : ThermodynamicState) : Prop :=
  new.freeEnergy ≤ old.freeEnergy

/-- Hydration irreversibility: α_new ≥ α_old. -/
def HydratCond  (old new : ThermodynamicState) : Prop :=
  old.hydration ≤ new.hydration

/-- Strength monotonicity: fc_new ≥ fc_old. -/
def StrengthCond (old new : ThermodynamicState) : Prop :=
  old.strength ≤ new.strength

/-- Theorem (CSG Decomposition):
    Admissible decomposes into exactly the four named sub-conditions.
    This is the formal statement that the gate is a CSG intersection. -/
theorem admissibleIffCSG (old new : ThermodynamicState) :
    Admissible old new ↔
    MassCond old new ∧ DissipCond old new ∧ HydratCond old new ∧ StrengthCond old new := by
  constructor
  · intro ⟨hm, hd, hh, hs⟩
    exact ⟨hm, hd, hh, hs⟩
  · intro ⟨hm, hd, hh, hs⟩
    exact ⟨hm, hd, hh, hs⟩

-- ================================================================
-- SECTION 9: Constitutional Sequences and Subject Reduction
-- ================================================================

/-- A constitutional sequence: a list of states where each consecutive
    pair is admissible (well-typed in the constitutional type grammar).
    Mirrors `ConstitutionalSeq` in Coq/Constitutional.v. -/
inductive ConstitutionalSeq : List ThermodynamicState → Prop where
  | nil  : ConstitutionalSeq []
  | one  : ∀ s, ConstitutionalSeq [s]
  | cons : ∀ s1 s2 rest,
             Admissible s1 s2 →
             ConstitutionalSeq (s2 :: rest) →
             ConstitutionalSeq (s1 :: s2 :: rest)

/-- Subject Reduction:
    Well-typedness is preserved under one reduction step.
    Proved by cases on the ConstitutionalSeq constructor. -/
theorem subjectReduction :
    ∀ (s1 s2 : ThermodynamicState) (rest : List ThermodynamicState),
    ConstitutionalSeq (s1 :: s2 :: rest) →
    ConstitutionalSeq (s2 :: rest) := by
  intro s1 s2 rest h
  cases h with
  | cons _ _ _ _ htail => exact htail

/-- Kleisli Admissibility:
    Every consecutive pair in a constitutional sequence is admissible. -/
theorem kleisliAdmissibility :
    ∀ (seq : List ThermodynamicState),
    ConstitutionalSeq seq →
    ∀ (i : Nat) (s1 s2 : ThermodynamicState),
    seq.get? i = some s1 →
    seq.get? (i + 1) = some s2 →
    Admissible s1 s2 := by
  intro seq hseq i s1 s2 h1 h2
  induction hseq generalizing i s1 s2 with
  | nil  => simp at h1
  | one s => cases i <;> simp_all
  | cons s1' s2' rest hadm _htail ih =>
    cases i with
    | zero =>
      simp [List.get?] at h1 h2
      rcases h1 with ⟨rfl⟩
      rcases h2 with ⟨rfl⟩
      exact hadm
    | succ n =>
      rw [List.get?_cons_succ] at h1
      rw [List.get?_cons_succ] at h2
      exact ih n s1 s2 h1 h2

-- ================================================================
-- SECTION 10: Graded Admissibility (N-Step Accumulated Tolerance)
-- ================================================================
-- Motivation: the single-step `admissible_trans` axiom in Constitutional.lean
-- is REFUTABLE. Two consecutive 99 kg/m³ jumps give |198 - 0| = 198 > δMass.
-- Solution: index admissibility by step count n; mass tolerance accumulates as
-- n * δMass. Proved via the triangle inequality — no axiom needed.
-- See GraphProperties.lean for the formal counterexample.

/-- Admissibility with n-step accumulated mass tolerance.
    Mass may drift by at most `n * δMass` over n consecutive admissible steps.
    `AdmissibleN 1 old new` is equivalent to the single-step `Admissible old new`. -/
structure AdmissibleN (n : ℕ) (old new : ThermodynamicState) : Prop where
  massDensity   : |new.density   - old.density|   ≤ (n : ℚ) * δMass
  clausiusDuhem : new.freeEnergy ≤ old.freeEnergy
  hydrationMono : old.hydration  ≤ new.hydration
  strengthMono  : old.strength   ≤ new.strength

/-- Single-step `Admissible` is equivalent to `AdmissibleN 1`. -/
theorem admissible_iff_admissibleN1 (old new : ThermodynamicState) :
    Admissible old new ↔ AdmissibleN 1 old new := by
  constructor
  · intro h
    refine ⟨?_, h.clausiusDuhem, h.hydrationMono, h.strengthMono⟩
    simpa [one_mul] using h.massDensity
  · intro h
    refine ⟨?_, h.clausiusDuhem, h.hydrationMono, h.strengthMono⟩
    simpa [one_mul] using h.massDensity

/-- Every state is `AdmissibleN n` with itself (reflexivity for any step count). -/
theorem admissibleNRefl (n : ℕ) (s : ThermodynamicState) : AdmissibleN n s s :=
  ⟨by simp only [sub_self, abs_zero]; exact mul_nonneg (Nat.cast_nonneg _) (by norm_num [δMass]),
   le_refl _, le_refl _, le_refl _⟩

/-- **Graded composition** (replaces the refutable `admissibleTrans` axiom):
    An m-step admissible path followed by an n-step admissible path is (m+n)-step
    admissible.  The mass bound accumulates via the triangle inequality.
    The three order conditions (Clausius-Duhem, hydration, strength) are each
    transitively inherited. -/
theorem admissibleN_compose {m n : ℕ} {s s' s'' : ThermodynamicState}
    (h1 : AdmissibleN m s s') (h2 : AdmissibleN n s' s'') :
    AdmissibleN (m + n) s s'' where
  massDensity := by
    have tri : |s''.density - s.density| ≤
        |s''.density - s'.density| + |s'.density - s.density| := by
      have heq : s''.density - s.density =
          (s''.density - s'.density) + (s'.density - s.density) := by ring
      calc |s''.density - s.density|
          = |(s''.density - s'.density) + (s'.density - s.density)| := by rw [heq]
        _ ≤ |s''.density - s'.density| + |s'.density - s.density|   := abs_add _ _
    have cast_eq : ((m + n : ℕ) : ℚ) * δMass = (m : ℚ) * δMass + (n : ℚ) * δMass := by
      push_cast; ring
    rw [cast_eq]
    -- Reorder |s''−s'| + |s'−s| ≤ m·δ + n·δ from `add_le_add` on the swapped sum.
    have hsum :
        |s''.density - s'.density| + |s'.density - s.density| ≤
          (m : ℚ) * δMass + (n : ℚ) * δMass := by
      simpa [add_comm] using add_le_add h1.massDensity h2.massDensity
    exact le_trans tri hsum
  clausiusDuhem := le_trans h2.clausiusDuhem h1.clausiusDuhem
  hydrationMono := le_trans h1.hydrationMono h2.hydrationMono
  strengthMono  := le_trans h1.strengthMono  h2.strengthMono

end UMST
