-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Economic/CreativeExplorationTolerance.lean

  Wire exploration slack on identity-class writes: bounded positive feedback only
  inside sdf ≥ 0 (GoalRegion membership surrogate). Exploration tolerance is not a
  virus hole — self-propagation cannot hide behind creative slack.
-/

import Economic.CreativityBudget
import Mathlib.Tactic.Linarith

namespace UMST.Economics

open Rat

/-- Identity exploration evidence (bookkeeping surrogate for BurdenHormone fields). -/
structure IdentityExplorationEvidence where
  Q : ℚ
  Q_admitted : ℚ
  Δ : ℚ
  sdf : ℚ
  propagate : Bool

/-- Inside the goal / SDF set: sdf ≥ 0 (GoalRegion membership surrogate on the ℚ axis). -/
def sdfInsideSet (sdf : ℚ) : Prop :=
  0 ≤ sdf

/-- Virus hole: self-propagation flagged while charge still fits declared slack (hole ≠ tolerance). -/
def virusHole (e : IdentityExplorationEvidence) : Prop :=
  e.propagate ∧ withinCreativityBudget e.Q e.Q_admitted e.Δ

/-- Exploration slack on identity: budgeted charge, inside set, no self-propagation flag. -/
def explorationToleranceOnIdentity (e : IdentityExplorationEvidence) : Prop :=
  withinCreativityBudget e.Q e.Q_admitted e.Δ ∧
  sdfInsideSet e.sdf ∧
  ¬ e.propagate

/-- Bounded positive feedback inside the set: slack only while sdf ≥ 0. -/
def boundedPositiveFeedbackInsideSet (e : IdentityExplorationEvidence) : Prop :=
  withinCreativityBudget e.Q e.Q_admitted e.Δ ∧ sdfInsideSet e.sdf

theorem creativeExploration_accepted (Q Q_admitted Δ : ℚ) (h : Q ≤ Q_admitted + Δ) :
    withinCreativityBudget Q Q_admitted Δ :=
  h

theorem explorationTolerance_implies_bounded (e : IdentityExplorationEvidence)
    (h : explorationToleranceOnIdentity e) : boundedPositiveFeedbackInsideSet e := by
  rcases h with ⟨hb, hs, _⟩
  exact ⟨hb, hs⟩

theorem explorationTolerance_disjoint_virusHole (e : IdentityExplorationEvidence)
    (h : explorationToleranceOnIdentity e) : ¬ virusHole e := by
  rintro ⟨hprop, _⟩
  exact h.2.2 hprop

theorem virusHole_excludes_tolerance (e : IdentityExplorationEvidence) (hv : virusHole e) :
    ¬ explorationToleranceOnIdentity e := by
  rintro ⟨_, _, hnp⟩
  exact hnp hv.1

theorem identityExploration_admissible (e : IdentityExplorationEvidence) (hQ : e.Q ≤ e.Q_admitted + e.Δ)
    (hs : sdfInsideSet e.sdf) (hp : ¬ e.propagate) : explorationToleranceOnIdentity e := by
  refine ⟨?_, hs, hp⟩
  simpa [withinCreativityBudget] using hQ

theorem slack_inside_set_not_optional (e : IdentityExplorationEvidence)
    (h : explorationToleranceOnIdentity e) : sdfInsideSet e.sdf :=
  h.2.1

theorem propagate_blocks_tolerance (e : IdentityExplorationEvidence) (hp : e.propagate) :
    ¬ explorationToleranceOnIdentity e := fun ⟨_, _, hnp⟩ => hnp hp

end UMST.Economics
