-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/Reconcile.lean

  Meso acting Urge — BP II §5.2 / §13.02 both-way union-preserving reconcile.
  Machine-checked Props mirroring Rust `reconcile_heads` + ContentConflict refuse.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Zero Lean `axiom`. Zero sorry. `physics_green` false.
-/

import Urge.AppendOnly
import LandauerLaw

namespace UMST.Urge.Reconcile

/-- Content-addressed head surrogate (id + digest). -/
structure Head where
  id     : Nat
  digest : Nat
  deriving DecidableEq, Repr

/-- Replica state summary. -/
structure StateSummary where
  heads : List Head

/-- Head id appears in summary. -/
def advertises (s : StateSummary) (id : Nat) : Prop :=
  ∃ h ∈ s.heads, h.id = id

/-- Digests agree when both advertise the same id. -/
def digestsAgree (left right : StateSummary) (id : Nat) : Prop :=
  ∀ hL ∈ left.heads, ∀ hR ∈ right.heads,
    hL.id = id → hR.id = id → hL.digest = hR.digest

/-- Both-way union membership: id in left or right. -/
def inUnion (left right : StateSummary) (id : Nat) : Prop :=
  advertises left id ∨ advertises right id

/-- No-Loss mech #4: every advertised id remains in the conceptual union. -/
def unionPreserving (left right : StateSummary) : Prop :=
  (∀ id, advertises left id → inUnion left right id) ∧
  (∀ id, advertises right id → inUnion left right id)

theorem unionPreserving_trivial (left right : StateSummary) :
    unionPreserving left right := by
  refine ⟨?_, ?_⟩
  · intro id h; exact Or.inl h
  · intro id h; exact Or.inr h

/-- Content conflict — same id, divergent digest. -/
def contentConflict (left right : StateSummary) (id : Nat) : Prop :=
  ∃ hL ∈ left.heads, ∃ hR ∈ right.heads,
    hL.id = id ∧ hR.id = id ∧ hL.digest ≠ hR.digest

/-- Reconcile admissible when digests agree on overlapping ids. -/
def reconcileAdmissible (left right : StateSummary) : Prop :=
  ∀ id, advertises left id → advertises right id → digestsAgree left right id

theorem contentConflict_not_admissible
    (left right : StateSummary) (id : Nat)
    (hc : contentConflict left right id) :
    ¬ reconcileAdmissible left right := by
  intro ha
  rcases hc with ⟨hL, hL_in, hR, hR_in, hidL, hidR, hneq⟩
  have hal : advertises left id := ⟨hL, hL_in, hidL⟩
  have har : advertises right id := ⟨hR, hR_in, hidR⟩
  have hagree := ha id hal har hL hL_in hR hR_in hidL hidR
  exact hneq hagree

/-- Honest physics GREEN posture. -/
def reconcilePhysicsGreen : Bool := false

theorem reconcilePhysicsGreen_false : reconcilePhysicsGreen = false := rfl

def fixtureLeft : StateSummary :=
  { heads := [{ id := 1, digest := 10 }, { id := 2, digest := 20 }] }

def fixtureRight : StateSummary :=
  { heads := [{ id := 2, digest := 20 }, { id := 3, digest := 30 }] }

def fixtureConflictL : StateSummary :=
  { heads := [{ id := 1, digest := 1 }] }

def fixtureConflictR : StateSummary :=
  { heads := [{ id := 1, digest := 9 }] }

theorem fixture_union_preserving :
    unionPreserving fixtureLeft fixtureRight :=
  unionPreserving_trivial fixtureLeft fixtureRight

theorem fixture_conflict_refused :
    contentConflict fixtureConflictL fixtureConflictR 1 := by
  refine ⟨{ id := 1, digest := 1 }, ?_, { id := 1, digest := 9 }, ?_, rfl, rfl, ?_⟩
  · simp [fixtureConflictL]
  · simp [fixtureConflictR]
  · decide

theorem fixture_conflict_blocks_admit :
    ¬ reconcileAdmissible fixtureConflictL fixtureConflictR :=
  contentConflict_not_admissible fixtureConflictL fixtureConflictR 1 fixture_conflict_refused

end UMST.Urge.Reconcile
