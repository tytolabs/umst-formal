-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Economic/CollectiveCoherenceCost.lean

  Sum of nonnegative **penalty** terms (classical surrogate for multi-agent divergence).

  **Collision (AGENT-LOOP-08):** collective coherence cost is **not** one-host coalition
  prune.  A per-host coalition window can inspect only local MEMORY fragments; the honest
  object is **agent spread** — cross-host salami whose fragments carry distinct
  `core_id` (user / org / vendor / model-card nested setpoints).  Local prune cannot see
  distributed salami; this module names spread + nested `core_id` as the collective
  bookkeeping target.  Runtime wiring on agent identity remains open (`closed=false`).
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Tactic.Linarith

namespace UMST.Economics

open Rat

/-- Nested constitutional setpoint this host names (user / org / vendor / model card). -/
abbrev CoreId := String

/-- Agent host in a spread (Cursor session, Claude Code, OpenClaw, …). -/
abbrev AgentHostId := String

/-- One salami fragment: host, nested `core_id`, nonnegative divergence penalty. -/
structure SalamiFragment where
  host : AgentHostId
  core_id : CoreId
  penalty : ℚ

/-- Cross-host agent spread — the collective coherence object (not a one-host coalition). -/
structure AgentSpread where
  fragments : List SalamiFragment

/-- Per-host coalition window — local prune only; **not** the collective object. -/
structure OneHostCoalition where
  host : AgentHostId
  local_penalties : List ℚ

/-- Collective penalty is sum of nonnegative contributions (classical surrogate). -/
def collectivePenalty (xs : List ℚ) : ℚ :=
  xs.sum

/-- Penalty terms extracted from spread fragments. -/
def spreadPenalties (spread : AgentSpread) : List ℚ :=
  spread.fragments.map SalamiFragment.penalty

/-- Collective coherence cost on agent spread (cross-host salami). -/
def collectiveSpreadPenalty (spread : AgentSpread) : ℚ :=
  collectivePenalty (spreadPenalties spread)

/-- Local coalition cost on one host — distinct from collective spread. -/
def oneHostCoalitionPenalty (coal : OneHostCoalition) : ℚ :=
  collectivePenalty coal.local_penalties

/-- Spread is cross-host when fragments name more than one distinct host. -/
def isCrossHostSpread (spread : AgentSpread) : Prop :=
  match spread.fragments with
  | [] => False
  | f :: fs => (fs.map SalamiFragment.host).any (· ≠ f.host) ∨
      (fs.any fun g => g.host ≠ f.host)

/-- Honest collective object: spread with at least one fragment (salami named). -/
def collectiveCoherenceObject (spread : AgentSpread) : Prop :=
  spread.fragments ≠ []

/-- Nested `core_id` is named on every fragment (no anonymous spread bookkeeping). -/
def nestedCoreIdNamed (spread : AgentSpread) : Prop :=
  ∀ f ∈ spread.fragments, f.core_id ≠ ""

/-- Collective bookkeeping refuses to equate spread with one-host coalition. -/
def collectiveNotOneHostCoalition : Prop :=
  ∀ (spread : AgentSpread) (coal : OneHostCoalition),
    isCrossHostSpread spread →
      collectiveSpreadPenalty spread ≠ oneHostCoalitionPenalty coal ∨
        spreadPenalties spread ≠ coal.local_penalties

theorem collectivePenalty_nonneg (xs : List ℚ) (hx : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ collectivePenalty xs := by
  induction xs with
  | nil => simp [collectivePenalty, List.sum_nil]
  | cons x xs ih =>
    simp only [collectivePenalty, List.sum_cons]
    have hx0 : 0 ≤ x := hx x (List.mem_cons_self _ _)
    have htail : 0 ≤ xs.sum := ih fun y hy => hx y (List.mem_cons_of_mem x hy)
    linarith

theorem collectiveSpreadPenalty_nonneg (spread : AgentSpread)
    (h : ∀ f ∈ spread.fragments, 0 ≤ f.penalty) : 0 ≤ collectiveSpreadPenalty spread := by
  unfold collectiveSpreadPenalty collectivePenalty spreadPenalties
  exact collectivePenalty_nonneg _ fun x hx => by
    rcases List.mem_map.mp hx with ⟨f, hf, rfl⟩
    exact h f hf

end UMST.Economics
