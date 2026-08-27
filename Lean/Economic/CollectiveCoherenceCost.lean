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
  bookkeeping target.

  **Honesty (AGENT-LOOP-08):** cross-host salami formal **≠** wired on agent identity.
  Spread + nested `core_id` predicates land in Lean; runtime still does not consume
  cross-host penalties on identity-class writes.  `remainder_row_closed` /
  `agentLoopRemainderRow08Closed` and `physicsGreen` stay false — no GREEN theater.
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

/-- Identity-class collective object: nonempty spread with nested `core_id` named on every fragment.
    Runtime identity writes still do not consume this (`collectiveCoherenceWiredOnAgentIdentity`). -/
def identityClassSpreadAdmits (spread : AgentSpread) : Prop :=
  nestedCoreIdNamed spread ∧ collectiveCoherenceObject spread

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

/-- Formal module landed on agent spread bookkeeping (Lean present). -/
def formalPresentOnAgentSpread : Bool := true

/-- Runtime wiring on agent identity — measured false until spread gate consumes penalties. -/
def collectiveCoherenceWiredOnAgentIdentity : Bool := false

/-- Cross-host salami formal landed (spread bookkeeping present in Lean). -/
def crossHostSalamiFormalPresent : Bool := formalPresentOnAgentSpread

/-- Cross-host salami not wired on agent identity — runtime gate still open. -/
def crossHostSalamiWiredOnAgentIdentity : Bool := collectiveCoherenceWiredOnAgentIdentity

/-- Padma remainder row AGENT-LOOP-08 — stays open; do not bool-flip closed. -/
def agentLoopRemainderRow08Closed : Bool := false

/-- Alias for gate_deltas: remainder row stays open. -/
def remainderRowClosed : Bool := agentLoopRemainderRow08Closed

/-- Physics GREEN — toolkit does not measure agent collective wiring. -/
def physicsGreen : Bool := false

theorem formal_present_on_agent_spread : formalPresentOnAgentSpread = true := rfl

theorem collective_coherence_not_wired_on_agent_identity :
    collectiveCoherenceWiredOnAgentIdentity = false := rfl

theorem agent_loop_remainder_row_08_not_closed : agentLoopRemainderRow08Closed = false := rfl

theorem remainder_row_closed_false : remainderRowClosed = false := rfl

theorem physics_green_false : physicsGreen = false := rfl

theorem cross_host_salami_formal_present : crossHostSalamiFormalPresent = true := rfl

theorem cross_host_salami_not_wired_on_agent_identity :
    crossHostSalamiWiredOnAgentIdentity = false := rfl

/-- Named gap: cross-host salami formal present, unused on agent identity. -/
def crossHostSalamiFormalUnusedOnAgentIdentityGap : Prop :=
  crossHostSalamiFormalPresent = true ∧ crossHostSalamiWiredOnAgentIdentity = false

theorem cross_host_salami_formal_unused_on_agent_identity_gap :
    crossHostSalamiFormalUnusedOnAgentIdentityGap := by
  exact ⟨cross_host_salami_formal_present, cross_host_salami_not_wired_on_agent_identity⟩

/-- Named gap: formal present, unused on agent identity (spread predicates only). -/
def formalPresentUnusedOnAgentIdentityGap : Prop :=
  formalPresentOnAgentSpread = true ∧ collectiveCoherenceWiredOnAgentIdentity = false

theorem formal_present_unused_on_agent_identity_gap :
    formalPresentUnusedOnAgentIdentityGap := by
  exact ⟨formal_present_on_agent_spread, collective_coherence_not_wired_on_agent_identity⟩

/-- Local one-host coalition cannot witness cross-host salami wiring. -/
theorem local_coalition_cannot_witness_cross_host_wiring
    (_spread : AgentSpread) (_coal : OneHostCoalition) :
    crossHostSalamiWiredOnAgentIdentity = false :=
  cross_host_salami_not_wired_on_agent_identity

/-- Two distinct hosts are a cross-host spread (the collective object). -/
theorem isCrossHostSpread_pair (f g : SalamiFragment) (hhost : f.host ≠ g.host) :
    isCrossHostSpread ⟨[f, g]⟩ := by
  simp [isCrossHostSpread]
  exact hhost.symm

/-- Local one-host coalition that only sees `f` cannot match two-host spread cost when `g` pays. -/
theorem two_host_spread_penalty_exceeds_one_host_local
    (f g : SalamiFragment) (hhost : f.host ≠ g.host) (hg : 0 < g.penalty) :
    isCrossHostSpread ⟨[f, g]⟩ ∧
      oneHostCoalitionPenalty ⟨f.host, [f.penalty]⟩ < collectiveSpreadPenalty ⟨[f, g]⟩ := by
  refine ⟨isCrossHostSpread_pair f g hhost, ?_⟩
  simp [collectiveSpreadPenalty, spreadPenalties, oneHostCoalitionPenalty, collectivePenalty,
    List.map, List.sum_cons, List.sum_nil]
  linarith

/-- Anonymous `core_id` refuses the identity-class spread object. -/
theorem anonymous_core_refuses_identity_spread (host : AgentHostId) (p : ℚ) :
    ¬ identityClassSpreadAdmits ⟨[{ host := host, core_id := "", penalty := p }]⟩ := by
  intro h
  exact h.1 { host := host, core_id := "", penalty := p } (by simp) rfl

/-- Named nonempty spread admits as the collective object — still unused on live identity writes. -/
theorem named_spread_admits_identity_object (f : SalamiFragment) (hn : f.core_id ≠ "") :
    identityClassSpreadAdmits ⟨[f]⟩ := by
  refine ⟨?_, by simp [collectiveCoherenceObject]⟩
  intro g hg
  simp at hg
  simpa [hg] using hn

/-- Non-claims beside spread predicates — no fleet GREEN / production close. -/
def collectiveCoherenceNonClaims : List String :=
  [ "cross-host salami formal present ≠ wired on agent identity"
  , "local one-host coalition prune is not the collective object"
  , "nested core_id named on fragments — runtime identity gate still open"
  , "remainder_row_closed=false — do not bool-flip Padma row 08"
  , "physics_green=false — Lean penalty sum is not production wiring" ]

/-- AGENT-LOOP-08 formal close is honest: spread landed, wiring + remainder open. -/
def agentLoop08FormalCloseHonest : Bool :=
  crossHostSalamiFormalPresent = true &&
  crossHostSalamiWiredOnAgentIdentity = false &&
  remainderRowClosed = false &&
  physicsGreen = false

theorem agent_loop_08_formal_close_honest : agentLoop08FormalCloseHonest = true := by
  simp [agentLoop08FormalCloseHonest, cross_host_salami_formal_present,
    cross_host_salami_not_wired_on_agent_identity, remainder_row_closed_false,
    physics_green_false]

end UMST.Economics
