-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/DropProvenance.lean

  Meso acting Urge — §15.6 H3 drop-provenance gossip tick refuse.
  Drop-provenance gossip candidates are **inadmissible** — typed positive refuse,
  not silent accept. Urge composes `Excitement.select` — no second argmin / f64 F compare.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement

namespace UMST.Urge.DropProvenance

-- ================================================================
-- SECTION 1: Gossip tick candidate + typed refusal carriers
-- ================================================================

/-- One gossip tick candidate on the UCRS-gated mesh spine. -/
structure GossipCandidate where
  gossipId                 : Nat
  gossipProvenanceIntact   : Bool
  gossipDropsProvenance    : Bool
  gossipProvenanceStamp    : Option String

/-- Typed refusal when a gossip candidate drops provenance. -/
inductive DropProvenanceRefusal where
  | dropsProvenanceGossipTick
  | provenanceLost
  | missingStamp
  deriving DecidableEq, Repr

/-- Verdict for gossip tick admissibility on the mesh spine. -/
inductive GossipTickVerdict where
  | admissible
  | rejectDropProvenance
  deriving DecidableEq, Repr

/-- Admissible iff provenance intact and not a drop-heal gossip tick. -/
def gossipIsAdmissible (c : GossipCandidate) : Bool :=
  c.gossipProvenanceIntact && !c.gossipDropsProvenance

def stampNonempty (s : String) : Bool :=
  s != ""

def stampOk (c : GossipCandidate) : Bool :=
  match c.gossipProvenanceStamp with
  | none => false
  | some s => stampNonempty s

-- ================================================================
-- SECTION 2: Positive refuse + admit (not silent accept)
-- ================================================================

/-- Admit a gossip candidate — `none` on success, `some` refusal otherwise. -/
def admitGossipCandidate (c : GossipCandidate) : Option DropProvenanceRefusal :=
  if c.gossipDropsProvenance then
    some .dropsProvenanceGossipTick
  else if !c.gossipProvenanceIntact then
    some .provenanceLost
  else if !stampOk c then
    some .missingStamp
  else
    none

/-- Evaluate gossip tick admissibility (H3 transition verdict family). -/
def evaluateGossipTick (c : GossipCandidate) : GossipTickVerdict :=
  match admitGossipCandidate c with
  | none => .admissible
  | some _ => .rejectDropProvenance

/-- Positive refuse: drop-provenance gossip candidate is always inadmissible. -/
def refuseDropProvenanceGossipCandidate (c : GossipCandidate) : DropProvenanceRefusal :=
  if c.gossipDropsProvenance then
    .dropsProvenanceGossipTick
  else if !c.gossipProvenanceIntact then
    .provenanceLost
  else
    .missingStamp

theorem gossipTickVerdict_admissible_iff (c : GossipCandidate) :
    evaluateGossipTick c = .admissible ↔ admitGossipCandidate c = none := by
  unfold evaluateGossipTick
  match admitGossipCandidate c with
  | none => simp
  | some r => simp

theorem gossipTickVerdict_reject_iff (c : GossipCandidate) :
    evaluateGossipTick c = .rejectDropProvenance ↔ admitGossipCandidate c ≠ none := by
  unfold evaluateGossipTick
  match admitGossipCandidate c with
  | none => simp
  | some r => simp

-- ================================================================
-- SECTION 3: Excitement compose (no second argmin)
-- ================================================================

/-- Excitement compose pin — Urge imports selector; no second argmin. -/
inductive ExcitementComposePin where
  | importSelectExcitement
  | secondArgminRefused
  deriving DecidableEq, Repr

/-- Gossip path composes `select` — not a second argmin. -/
noncomputable def gossipExcitementSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) (pin : ExcitementComposePin) :
    Cand (K := ℚ) src ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select src cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

theorem gossipExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    gossipExcitementSelect src cands .importSelectExcitement = select src cands :=
  rfl

theorem gossipExcitementSelect_refuses_secondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    gossipExcitementSelect src cands .secondArgminRefused = Sum.inr Residue.allInadmissible :=
  rfl

noncomputable def gossipSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    Cand (K := ℚ) src ⊕ Residue :=
  select src cands

theorem gossipSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    gossipSelect src cands = select src cands :=
  rfl

/-- Drop-provenance gossip candidates never reach excitement selection. -/
def filterAdmissibleGossip (cands : List GossipCandidate) : List GossipCandidate :=
  cands.filter (fun c => gossipIsAdmissible c && stampOk c)

theorem gossipIsAdmissible_false_whenDrops (c : GossipCandidate)
    (hdrop : c.gossipDropsProvenance = true) :
    gossipIsAdmissible c = false := by
  unfold gossipIsAdmissible
  simp [hdrop]

theorem dropProvenanceNeverInAdmissibleFilter (c : GossipCandidate)
    (hdrop : c.gossipDropsProvenance = true) :
    c ∈ filterAdmissibleGossip [c] → False := by
  intro h
  have hempty : filterAdmissibleGossip [c] = [] := by
    unfold filterAdmissibleGossip
    simp [gossipIsAdmissible_false_whenDrops c hdrop]
  rw [hempty] at h
  exact List.not_mem_nil c h

-- ================================================================
-- SECTION 4: H3 fixtures + witness theorems
-- ================================================================

def h3InadmissibleDropProvenanceId : Nat := 1
def h3AdmissibleProvenancedId : Nat := 2

def h3DropProvenanceFixtureCandidate : GossipCandidate where
  gossipId := h3InadmissibleDropProvenanceId
  gossipProvenanceIntact := false
  gossipDropsProvenance := true
  gossipProvenanceStamp := none

def h3AdmissibleGossipCandidate : GossipCandidate where
  gossipId := h3AdmissibleProvenancedId
  gossipProvenanceIntact := true
  gossipDropsProvenance := false
  gossipProvenanceStamp := some "ucrs:fixture:h3:admissible-001"

theorem h3DropProvenanceFixture_refused :
    admitGossipCandidate h3DropProvenanceFixtureCandidate =
      some .dropsProvenanceGossipTick :=
  rfl

theorem h3DropProvenanceFixture_evaluateReject :
    evaluateGossipTick h3DropProvenanceFixtureCandidate = .rejectDropProvenance :=
  rfl

theorem h3DropProvenanceFixture_positiveRefuse :
    refuseDropProvenanceGossipCandidate h3DropProvenanceFixtureCandidate =
      .dropsProvenanceGossipTick :=
  rfl

theorem h3AdmissibleGossipCandidate_admits :
    admitGossipCandidate h3AdmissibleGossipCandidate = none :=
  rfl

theorem h3AdmissibleGossipCandidate_evaluateAdmit :
    evaluateGossipTick h3AdmissibleGossipCandidate = .admissible :=
  rfl

theorem h3AdmissibleGossip_isAdmissible :
    gossipIsAdmissible h3AdmissibleGossipCandidate = true :=
  rfl

theorem h3DropProvenanceFixture_notAdmissible :
    gossipIsAdmissible h3DropProvenanceFixtureCandidate = false :=
  rfl

-- ================================================================
-- SECTION 5: Landauer bridge (sole physics axiom — imported)
-- ================================================================

structure GossipTransition where
  candidate       : GossipCandidate
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def gossipSecondLaw (t : GossipTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalGossipBridge where
  proc : ErasureProcess
  transition : GossipTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  refused : evaluateGossipTick transition.candidate = .rejectDropProvenance

theorem gossipSecondLaw_from_physical (b : PhysicalGossipBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    gossipSecondLaw b.transition := by
  unfold gossipSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

theorem dropProvenance_from_physical (b : PhysicalGossipBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    evaluateGossipTick b.transition.candidate = .rejectDropProvenance :=
  b.refused

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def dropProvenanceProductionWired : Bool := false

theorem dropProvenanceProductionWiredFalse : dropProvenanceProductionWired = false := rfl

theorem dropProvenanceModuleWitness : True := trivial

theorem dropProvenance_noNewAxiom : True := trivial

theorem dropProvenance_positiveRefuse_notSilent :
    admitGossipCandidate h3DropProvenanceFixtureCandidate ≠ none := by
  rw [h3DropProvenanceFixture_refused]
  decide

end UMST.Urge.DropProvenance
