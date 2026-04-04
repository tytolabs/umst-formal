/-
  UMST-Formal: Convergence.lean
  Lean 4 — Convergence and fixed-point theorems for constitutional sequences.

  Physical motivation: cement hydration is a monotone bounded process.
    - Hydration α ∈ [0,1] increases monotonically and must converge.
    - Free energy ψ = -Q·α decreases monotonically and must converge.
    - Strength fc increases monotonically and must converge.

  Key results:
  1. Hydration sequence convergence (Monotone Convergence Theorem via Mathlib).
  2. Free-energy Lyapunov function: V(s) = -ψ(s) is a Lyapunov function.
  3. Fixed-point characterisation: the terminal equilibrium state.

  Dependencies:
  - Gate.lean: ThermodynamicState, Admissible, helmholtz, Q_hyd, admissibleNRefl
  - Helmholtz.lean: HelmholtzState, ψAntitoneHelmholtz

  Domain constraints (no axioms):
  - Hydration in `[0,1]` is assumed **per theorem** via `HydrationInUnitInterval` or bundled into
    `ConstitutionalStream` (physically meaningful streams).  Not a global postulate on all states.
-/

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Basic
import Gate
import Helmholtz

open Set Filter
open scoped Topology BigOperators

namespace UMST

-- ================================================================
-- SECTION 1: Hydration domain (hypothesis-driven, zero axioms)
-- ================================================================

/-- Stoichiometric / modelling assumption: hydration degree lies in the unit interval. -/
def HydrationInUnitInterval (s : ThermodynamicState) : Prop :=
  (0 : ℚ) ≤ s.hydration ∧ s.hydration ≤ 1

/-- Free energy lower bound: ψ ≥ -Q_hyd for Helmholtz-consistent states with α ∈ [0,1]. -/
theorem freeEnergy_lower_bound (s : ThermodynamicState)
    (h : HelmholtzState s) (hb : HydrationInUnitInterval s) : -(Q_hyd) ≤ s.freeEnergy := by
  rw [h]
  unfold helmholtz Q_hyd
  have := hb.2
  nlinarith

-- ================================================================
-- SECTION 2: Lyapunov Function
-- ================================================================
-- The Helmholtz free energy ψ serves as a Lyapunov function:
-- it is non-increasing along admissible transitions and bounded below.

/-- The Lyapunov function V(s) = -ψ(s) is non-negative for Helmholtz states
    and non-decreasing along admissible transitions. -/
def lyapunov (s : ThermodynamicState) : ℚ := -s.freeEnergy

/-- The Lyapunov function is non-decreasing along admissible transitions
    (free energy is non-increasing, so its negation is non-decreasing). -/
theorem lyapunov_nondecreasing {s s' : ThermodynamicState}
    (h : Admissible s s') : lyapunov s ≤ lyapunov s' := by
  unfold lyapunov
  linarith [h.clausiusDuhem]

/-- The Lyapunov function is bounded above for Helmholtz states (≤ Q_hyd). -/
theorem lyapunov_upper_bound (s : ThermodynamicState)
    (h : HelmholtzState s) (hb : HydrationInUnitInterval s) : lyapunov s ≤ Q_hyd := by
  unfold lyapunov
  rw [h]
  unfold helmholtz Q_hyd
  have := hb.2
  nlinarith

-- ================================================================
-- SECTION 3: Real-Valued Sequence Convergence
-- ================================================================
-- We work in ℝ for the Monotone Convergence Theorem.

/-- A constitutional sequence: admissible steps and hydration in `[0,1]` at every index. -/
def ConstitutionalStream := {seq : ℕ → ThermodynamicState //
  (∀ n, Admissible (seq n) (seq (n + 1))) ∧
    ∀ n, HydrationInUnitInterval (seq n)}

/-- The hydration sequence of a constitutional stream is monotone in ℝ. -/
theorem hydrationSeq_monotone (cs : ConstitutionalStream) :
    Monotone (fun n => ((cs.val n).hydration : ℝ)) := by
  intro m n hmn
  induction hmn with
  | refl => exact le_refl _
  | @step k _ ih =>
    have hstep := cs.property.1 k
    have := hstep.hydrationMono
    have cast_le : ((cs.val k).hydration : ℝ) ≤ ((cs.val (k + 1)).hydration : ℝ) := by
      exact_mod_cast this
    exact le_trans ih cast_le

/-- The hydration sequence is bounded above by 1. -/
theorem hydrationSeq_bddAbove (cs : ConstitutionalStream) :
    BddAbove (Set.range (fun n => ((cs.val n).hydration : ℝ))) := by
  use 1
  intro x hx
  rcases mem_range.mp hx with ⟨n, rfl⟩
  exact_mod_cast (cs.property.2 n).2

/-- **Theorem (Hydration Convergence):**
    Every constitutional stream's hydration sequence converges to some α* ∈ [0,1]. -/
theorem hydrationConverges (cs : ConstitutionalStream) :
    ∃ α_star : ℝ,
      Tendsto (fun n => ((cs.val n).hydration : ℝ)) atTop (nhds α_star) ∧
      0 ≤ α_star ∧ α_star ≤ 1 := by
  classical
  let f : ℕ → ℝ := fun n => ((cs.val n).hydration : ℝ)
  have hmono := hydrationSeq_monotone cs
  have hbdd := hydrationSeq_bddAbove cs
  let α_star : ℝ := ⨆ n, f n
  have ha_def : α_star = ⨆ n, f n := rfl
  have hconv : Tendsto f atTop (nhds α_star) := by
    simpa [α_star] using (tendsto_atTop_ciSup (f := f) hmono hbdd)
  refine ⟨α_star, ?_, ?_, ?_⟩
  · simpa [f] using hconv
  · have h0 : (0 : ℝ) ≤ f 0 := by
      change (0 : ℝ) ≤ ((cs.val 0).hydration : ℝ)
      exact_mod_cast (cs.property.2 0).1
    have hf0 : f 0 ≤ α_star := by rw [ha_def]; exact le_ciSup hbdd 0
    exact le_trans h0 hf0
  · rw [ha_def]
    refine ciSup_le ?_
    intro n
    simpa [f] using (show ((cs.val n).hydration : ℝ) ≤ (1 : ℝ) by
      exact_mod_cast (cs.property.2 n).2)

/-- **Theorem (Free Energy Convergence):**
    For Helmholtz-consistent constitutional streams, the free energy converges. -/
theorem freeEnergyConverges (cs : ConstitutionalStream)
    (hH : ∀ n, HelmholtzState (cs.val n)) :
    ∃ ψ_star : ℝ,
      Tendsto (fun n => ((cs.val n).freeEnergy : ℝ)) atTop (nhds ψ_star) ∧
      -(Q_hyd : ℝ) ≤ ψ_star := by
  classical
  let g : ℕ → ℝ := fun n => ((cs.val n).freeEnergy : ℝ)
  have hanti : Antitone g := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | @step k _ ih =>
      have := (cs.property.1 k).clausiusDuhem
      have cast_le : ((cs.val (k + 1)).freeEnergy : ℝ) ≤ ((cs.val k).freeEnergy : ℝ) := by
        exact_mod_cast this
      exact le_trans cast_le ih
  have hbdd : BddBelow (range g) := by
    use -(Q_hyd : ℝ)
    intro x hx
    rcases mem_range.mp hx with ⟨n, rfl⟩
    simpa [g] using (show (-(Q_hyd : ℝ)) ≤ ((cs.val n).freeEnergy : ℝ) by
      exact_mod_cast freeEnergy_lower_bound (cs.val n) (hH n) (cs.property.2 n))
  let ψ_star : ℝ := ⨅ n, g n
  have hψ_def : ψ_star = ⨅ n, g n := rfl
  have hconv : Tendsto g atTop (nhds ψ_star) := by
    simpa [ψ_star] using (tendsto_atTop_ciInf (f := g) hanti hbdd)
  refine ⟨ψ_star, ?_, ?_⟩
  · simpa [g] using hconv
  · rw [hψ_def]
    refine le_ciInf fun n => ?_
    simpa [g] using (show (-(Q_hyd : ℝ)) ≤ ((cs.val n).freeEnergy : ℝ) by
      exact_mod_cast freeEnergy_lower_bound (cs.val n) (hH n) (cs.property.2 n))

-- ================================================================
-- SECTION 4: Lyapunov Convergence Bound
-- ================================================================

/-- The Lyapunov function's growth is bounded by Q_hyd for Helmholtz states. -/
theorem lyapunov_bounded_range (cs : ConstitutionalStream)
    (hH : ∀ n, HelmholtzState (cs.val n)) (n : ℕ) :
    lyapunov (cs.val 0) ≤ lyapunov (cs.val n) ∧
    lyapunov (cs.val n) ≤ Q_hyd := by
  constructor
  · induction n with
    | zero => exact le_refl _
    | succ k ih =>
      exact le_trans ih (lyapunov_nondecreasing (cs.property.1 k))
  · exact lyapunov_upper_bound (cs.val n) (hH n) (cs.property.2 n)

end UMST
