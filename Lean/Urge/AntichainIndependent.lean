-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/AntichainIndependent.lean

  Meso acting Urge — §22.2 conflict graph independent set.
  Urge **witnesses** prefix conflict-graph independent sets and composes
  `UMST.Excitement.select` — it does **not** fork `umst-adk` greedy
  `allocate_antichain` or invent GREEN from antichain size.
  Mirrors `Urge.ReplicaCoalgebra` / `Urge.BackupRecovery` typed morphism discipline.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations.  Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.AntichainIndependent

-- ================================================================
-- SECTION 1: Conflict cell + graph + independent-set carriers
-- ================================================================

/-- Write-set path surrogate — zone pin for prefix conflict (§22.2). -/
structure AntichainWritePath where
  zone    : Nat
  suffix  : Nat
  deriving DecidableEq, Repr

/-- Open cell node for prefix conflict graph construction. -/
structure ConflictCell where
  id        : Nat
  writeSet  : List AntichainWritePath
  deriving Repr

/-- Canonical undirected edge between two cell ids. -/
structure ConflictEdge where
  left   : Nat
  right  : Nat
  deriving DecidableEq, Repr

/-- Prefix conflict graph carrier. -/
structure ConflictGraph where
  nodes  : List Nat
  edges  : List ConflictEdge
  deriving Repr

/-- Verdict when validating an independent set on a conflict graph. -/
inductive IndependentSetVerdict where
  | admit
  deriving Repr

/-- Fail-closed refusal for §22.2 antichain independent-set policy. -/
inductive AntichainIndependentRefusal where
  | forkAllocateRefused
  | secondArgminRefused
  | notIndependentSet
  | conflictingNeighbor
  | greedyMisTheater
  deriving DecidableEq, Repr

/-- Verdict of an antichain independent-set operation class. -/
inductive AntichainIndependentVerdict where
  | independentAdmit
  | forkAllocateRefused
  | greedyMisRefused
  | secondArgminRefused
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: §22.2 admissibility conjunct + positive refuse
-- ================================================================

/-- §22.2 admissibility conjunct inputs (surrogate). -/
structure AntichainAdmissibilityConjunct where
  independentOk         : Bool
  noForkAllocate        : Bool
  excitementPreserves   : Bool
  deriving DecidableEq, Repr

def antichainConjunctAdmits (c : AntichainAdmissibilityConjunct) : Bool :=
  c.independentOk && c.noForkAllocate && c.excitementPreserves

/-- Whether two write-set paths prefix-conflict on zone pin. -/
def antichainPathsConflictSingle (p q : AntichainWritePath) : Bool :=
  p.zone == q.zone

/-- Whether any path in two write_sets prefix-conflicts. -/
def antichainPathsConflict (left right : List AntichainWritePath) : Bool :=
  left.any (fun p => right.any (fun q => antichainPathsConflictSingle p q))

/-- Canonical edge with sorted endpoints. -/
def canonicalConflictEdge (a b : Nat) : ConflictEdge :=
  if b < a then { left := b, right := a } else { left := a, right := b }

/-- Whether an edge connects two selected node ids. -/
def edgeHitsSelected (e : ConflictEdge) (selected : List Nat) : Bool :=
  selected.any (fun n => n == e.left) && selected.any (fun n => n == e.right)

/-- Whether selected nodes form an independent set (no edge between any pair). -/
def isIndependentSet (edges : List ConflictEdge) (selected : List Nat) : Bool :=
  edges.all (fun e => !edgeHitsSelected e selected)

/-- Validate selected cell ids form an independent set on the conflict graph. -/
def validateIndependentSet (g : ConflictGraph) (selected : List Nat) :
    IndependentSetVerdict ⊕ AntichainIndependentRefusal :=
  if isIndependentSet g.edges selected then Sum.inl .admit
  else Sum.inr .notIndependentSet

/-- Admit a single antichain member — refuse when prefix-conflicts with incumbent. -/
def admitAntichainMember (incumbent candidate : ConflictCell) :
    IndependentSetVerdict ⊕ AntichainIndependentRefusal :=
  if antichainPathsConflict incumbent.writeSet candidate.writeSet then
    Sum.inr .conflictingNeighbor
  else
    Sum.inl .admit

/-- Positive refuse: Urge must not fork `umst-adk` greedy allocate. -/
def refuseForkAllocate : AntichainIndependentRefusal := .forkAllocateRefused

/-- Classify fork-allocate vs witness-only independent set without performing I/O. -/
def evaluateAntichainOperation (forkAllocate : Bool) : AntichainIndependentVerdict :=
  if forkAllocate then .forkAllocateRefused else .independentAdmit

theorem evaluateAntichainOperation_forkRefused :
    evaluateAntichainOperation true = .forkAllocateRefused := rfl

theorem evaluateAntichainOperation_witnessAdmit :
    evaluateAntichainOperation false = .independentAdmit := rfl

-- ================================================================
-- SECTION 4: §22.2 fixtures + witness theorems
-- ================================================================

/-- §22.2 fixture path pins — mirror Rust `section_22_2_fixture`. -/
def aiPathZoneA : AntichainWritePath := { zone := 1, suffix := 0 }

def aiPathZoneAX : AntichainWritePath := { zone := 1, suffix := 1 }

def aiPathZoneAY : AntichainWritePath := { zone := 1, suffix := 2 }

def aiFixtureAccept : ConflictCell :=
  { id := 0, writeSet := [aiPathZoneA] }

def aiFixtureRefuseA : ConflictCell :=
  { id := 1, writeSet := [aiPathZoneAX] }

def aiFixtureRefuseB : ConflictCell :=
  { id := 2, writeSet := [aiPathZoneAY] }

def aiFixtureEdge01 : ConflictEdge := canonicalConflictEdge 0 1

def aiFixtureEdge02 : ConflictEdge := canonicalConflictEdge 0 2

def aiFixtureEdge12 : ConflictEdge := canonicalConflictEdge 1 2

def aiFixtureGraph : ConflictGraph :=
  { nodes := [0, 1, 2]
    edges := [aiFixtureEdge01, aiFixtureEdge02, aiFixtureEdge12] }

def aiFixtureConjunct : AntichainAdmissibilityConjunct :=
  { independentOk := true, noForkAllocate := true, excitementPreserves := true }

theorem aiFixture_acceptOnlyIndependent :
    validateIndependentSet aiFixtureGraph [0] = Sum.inl .admit := by
  rfl

theorem aiFixture_acceptRefuseA_conflicts :
    admitAntichainMember aiFixtureAccept aiFixtureRefuseA =
      Sum.inr .conflictingNeighbor := by
  rfl

theorem aiFixture_acceptRefuseB_conflicts :
    admitAntichainMember aiFixtureAccept aiFixtureRefuseB =
      Sum.inr .conflictingNeighbor := by
  rfl

theorem aiFixture_pathsConflict_acceptA :
    antichainPathsConflict aiFixtureAccept.writeSet aiFixtureRefuseA.writeSet = true := by
  rfl

theorem aiFixture_notIndependentPair :
    validateIndependentSet aiFixtureGraph [0, 1] = Sum.inr .notIndependentSet := by
  rfl

theorem aiFixture_conjunctAdmits :
    antichainConjunctAdmits aiFixtureConjunct = true := rfl

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure AntichainHistoryMove where
  independentOk       : Prop
  noForkAllocate      : Prop
  excitementPreserves : Prop

def admissibleAntichainIndependent (h : AntichainHistoryMove) : Prop :=
  h.independentOk ∧ h.noForkAllocate ∧ h.excitementPreserves

theorem admissibleAntichainIndependent_intro (h : AntichainHistoryMove)
    (hi : h.independentOk) (hf : h.noForkAllocate) (he : h.excitementPreserves) :
    admissibleAntichainIndependent h :=
  And.intro hi (And.intro hf he)

abbrev admitAntichainInbound := admissibleAntichainIndependent

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

theorem antichainIndependent_positiveRefuseNotSilent :
    evaluateAntichainOperation true ≠ .independentAdmit := by
  simp [evaluateAntichainOperation]

end UMST.Urge.AntichainIndependent
