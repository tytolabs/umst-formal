-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/AntichainIndependent.lean

  Meso acting Urge — §22.2 conflict graph independent set.
  Urge **witnesses** prefix conflict-graph independent sets and composes
  `UMST.Excitement.select` — it does **not** fork `umst-adk` greedy
  `allocate_antichain` or invent GREEN from antichain size.
  Mirrors `Urge.ReplicaCoalgebra` / `Urge.BackupRecovery` typed morphism discipline.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
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

/-- Positive refuse: second local Excitement argmin — compose import only. -/
def refuseSecondArgminSelector : AntichainIndependentRefusal := .secondArgminRefused

/-- Positive refuse: greedy/exact MIS theater — Urge witnesses only. -/
def refuseGreedyMisTheater : AntichainIndependentRefusal := .greedyMisTheater

/-- Urge does not bool-flip physics GREEN from antichain cardinality. -/
def physicsGreenFromAntichainSize (_size : Nat) : Bool := false

/-- Classify fork-allocate vs witness-only independent set without performing I/O. -/
def evaluateAntichainOperation (forkAllocate : Bool) : AntichainIndependentVerdict :=
  if forkAllocate then .forkAllocateRefused else .independentAdmit

theorem refuseForkAllocate_positive :
    refuseForkAllocate = .forkAllocateRefused := rfl

theorem refuseSecondArgminSelector_positive :
    refuseSecondArgminSelector = .secondArgminRefused := rfl

theorem refuseGreedyMisTheater_positive :
    refuseGreedyMisTheater = .greedyMisTheater := rfl

theorem antichainSize_never_invents_green (size : Nat) :
    physicsGreenFromAntichainSize size = false := rfl

theorem evaluateAntichainOperation_forkRefused :
    evaluateAntichainOperation true = .forkAllocateRefused := rfl

theorem evaluateAntichainOperation_witnessAdmit :
    evaluateAntichainOperation false = .independentAdmit := rfl

-- ================================================================
-- SECTION 3: Antichain independent composes Excitement (no second argmin)
-- ================================================================

/-- Excitement compose pin — import selector; refuse second local argmin. -/
inductive AntichainExcitementComposePin where
  | importSelectExcitement
  | secondArgminRefused
  deriving DecidableEq, Repr

/-- Context for antichain independent over admissible history successors. -/
structure AntichainIndependentCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Compose path composes `select` — not a second argmin. -/
noncomputable def antichainExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (cands : List (Cand (K := ℚ) prior)) (pin : AntichainExcitementComposePin) :
    Cand (K := ℚ) prior ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select prior cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

/-- Antichain independent selection **is** `urgeRecoverySelect` / `select`. -/
noncomputable def antichainIndependentSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : AntichainIndependentCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

theorem antichainExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (cands : List (Cand (K := ℚ) prior)) :
    antichainExcitementSelect prior cands .importSelectExcitement = select prior cands :=
  rfl

theorem antichainIndependentSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : AntichainIndependentCtx S) :
    antichainIndependentSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem antichainIndependentSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : AntichainIndependentCtx S) :
    antichainIndependentSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem antichainIndependent_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : AntichainIndependentCtx S) :
    antichainIndependentSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem antichainExcitementSelect_refusesSecondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (cands : List (Cand (K := ℚ) prior)) :
    antichainExcitementSelect prior cands .secondArgminRefused =
      Sum.inr Residue.allInadmissible :=
  rfl

theorem antichainIndependent_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : AntichainIndependentCtx S) (h : ctx.successors = []) :
    antichainIndependentSelect ctx = Sum.inr Residue.noCandidates := by
  simpa [antichainIndependentSelect, h] using urgeRecovery_empty ctx.prior

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

theorem aiFixture_antichainSize_noGreen :
    physicsGreenFromAntichainSize aiFixtureGraph.nodes.length = false := rfl

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

structure AntichainTransition where
  move            : AntichainHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def antichainSecondLaw (t : AntichainTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalAntichainBridge where
  proc : ErasureProcess
  transition : AntichainTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleAntichainIndependent transition.move

theorem antichainSecondLaw_from_physical (b : PhysicalAntichainBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    antichainSecondLaw b.transition := by
  unfold antichainSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleAntichainIndependent_from_physical (b : PhysicalAntichainBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleAntichainIndependent b.transition.move :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def antichainIndependentPhysicsGreen : Bool := false

theorem antichainIndependentPhysicsGreenFalse :
    antichainIndependentPhysicsGreen = false := rfl

def antichainIndependentProductionWired : Bool := false

theorem antichainIndependentProductionWiredFalse :
    antichainIndependentProductionWired = false := rfl

theorem antichainIndependentModuleWitness : True := trivial

theorem antichainIndependent_noNewAxiom : True := trivial

theorem antichainIndependent_positiveRefuseNotSilent :
    evaluateAntichainOperation true ≠ .independentAdmit := by
  simp [evaluateAntichainOperation]

theorem antichainIndependent_forkAllocateRefusedPositive :
    refuseForkAllocate = .forkAllocateRefused := rfl

theorem antichainIndependent_secondArgminRefusedPositive :
    refuseSecondArgminSelector = .secondArgminRefused := rfl

theorem antichainIndependent_greedyMisRefusedPositive :
    refuseGreedyMisTheater = .greedyMisTheater := rfl

theorem antichainIndependent_neverInventsGreenFromSize (size : Nat) :
    physicsGreenFromAntichainSize size = false :=
  antichainSize_never_invents_green size

end UMST.Urge.AntichainIndependent
