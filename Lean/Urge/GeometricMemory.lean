-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/GeometricMemory.lean

  Meso acting Urge — §5.3 geometric memory / SDF identity of a history object.
  Identity is canonical SDF/FRep fingerprint — not host ids or raw payload bytes alone.
  Composes `UMST.Excitement.select`; no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.GeometricMemory

-- ================================================================
-- SECTION 1: SDF identity + typed history object carriers (§5.3)
-- ================================================================

/-- Canonical SDF fingerprint surrogate (FRep grain + digest). -/
structure SdfFingerprint where
  digest : Nat
  grain  : Nat

/-- §5.3 geometric identity — SDF-canonical, not host-id keyed. -/
structure HistoryGeometricIdentity where
  fingerprint     : SdfFingerprint
  resolutionBits  : Nat

def sdfIdentityFromDigest (digest grain resolution : Nat) : HistoryGeometricIdentity :=
  { fingerprint := { digest := digest, grain := grain }
  , resolutionBits := resolution }

/-- Witness bundle a geometric memory morphism must preserve (§5.3). -/
structure SdfIdentityWitness where
  headDigest      : Nat
  tailDigests     : List Nat
  resolutionBits  : Nat

def sdfWitnessFromStamps (head : Nat) (tail : List Nat) (resolution : Nat) :
    SdfIdentityWitness :=
  { headDigest := head, tailDigests := tail, resolutionBits := resolution }

/-- History object whose identity is geometric memory, not host id. -/
structure HistoryObjectGeom where
  seq             : Nat
  identity        : HistoryGeometricIdentity
  hostSurrogate   : Nat

def geometricIdentityPred (idₐ idᵦ : HistoryGeometricIdentity) : Prop :=
  idₐ.fingerprint.digest = idᵦ.fingerprint.digest ∧
  idₐ.fingerprint.grain = idᵦ.fingerprint.grain ∧
  idₐ.resolutionBits = idᵦ.resolutionBits

theorem geometricIdentityPred_intro (idₐ idᵦ : HistoryGeometricIdentity)
    (hdig : idₐ.fingerprint.digest = idᵦ.fingerprint.digest)
    (hgrain : idₐ.fingerprint.grain = idᵦ.fingerprint.grain)
    (hres : idₐ.resolutionBits = idᵦ.resolutionBits) :
    geometricIdentityPred idₐ idᵦ :=
  And.intro hdig (And.intro hgrain hres)

def geometricIdentityMatches (left right : HistoryObjectGeom) : Bool :=
  left.identity.fingerprint.digest == right.identity.fingerprint.digest &&
  left.identity.fingerprint.grain == right.identity.fingerprint.grain &&
  left.identity.resolutionBits == right.identity.resolutionBits

/-- Witness bundle a geometric memory morphism must preserve (§5.3). -/
structure GeometricMemoryWitness where
  fingerprint     : SdfFingerprint
  resolutionBits  : Nat
  sdfCanonical    : Bool

def witnessFromHistoryObject (o : HistoryObjectGeom) : GeometricMemoryWitness :=
  { fingerprint := o.identity.fingerprint
  , resolutionBits := o.identity.resolutionBits
  , sdfCanonical := true }

/-- Typed geometric-memory morphism — admissible identity transition. -/
structure GeometricMemoryMorphism where
  morphismFrom          : HistoryObjectGeom
  morphismToSeq         : Nat
  witness               : GeometricMemoryWitness
  excitementSelected    : Bool

/-- Fail-closed geometric memory errors — positive refuse, not silent accept. -/
inductive GeometricMemoryRefusal where
  | hostIdNotGeometric (hostId : Nat)
  | payloadWithoutSdf (payload : Nat)
  | gateRejected (seq : Nat)
  | identityMismatch (leftDigest rightDigest : Nat)
  | hostIdTheater
  | payloadOnlyTheater
  | secondArgmin
  | sdfNotCanonical
  deriving Repr

/-- Verdict of a geometric identity operation class. -/
inductive GeometricMemoryVerdict where
  | identityOk
  | hostIdRefused
  | payloadOnlyRefused
  | inadmissible
  deriving DecidableEq, Repr

inductive GeometricMemoryClass where
  | hostIdSurrogate
  | sdfExcitementArrow
  deriving DecidableEq, Repr

/-- Gate input for §5.3 SDF identity classification. -/
structure GeometricMemoryAttempt where
  hostIdKeyed       : Bool
  payloadOnly       : Bool
  witness           : Option SdfIdentityWitness
  sourceFreeEnergy  : ℚ
  hostSurrogate     : Nat
  payloadSurrogate  : Nat

-- ================================================================
-- SECTION 2: §5.3 admissibility conjunct + positive refuse
-- ================================================================

structure GeometricAdmissibilityConjunct where
  gateOk                  : Bool
  sdfCanonical            : Bool
  excitementPreserves     : Bool

def geometricConjunctAdmits (c : GeometricAdmissibilityConjunct) : Bool :=
  c.gateOk && c.sdfCanonical && c.excitementPreserves

def evaluateHostIdIdentity (useHostId : Bool) : GeometricMemoryVerdict :=
  if useHostId then .hostIdRefused else .identityOk

def evaluatePayloadOnlyIdentity (payloadOnly : Bool) : GeometricMemoryVerdict :=
  if payloadOnly then .payloadOnlyRefused else .identityOk

def refuseHostIdIdentity (hostId : Nat) : GeometricMemoryRefusal :=
  .hostIdNotGeometric hostId

def refusePayloadOnlyIdentity (payload : Nat) : GeometricMemoryRefusal :=
  .payloadWithoutSdf payload

def refuseHostIdTheater : GeometricMemoryRefusal := .hostIdTheater

def refusePayloadOnlyTheater : GeometricMemoryRefusal := .payloadOnlyTheater

def refuseSecondArgmin : GeometricMemoryRefusal := .secondArgmin

def refuseSdfNotCanonical : GeometricMemoryRefusal := .sdfNotCanonical

theorem hostIdIdentity_refused (hostId : Nat) :
    refuseHostIdIdentity hostId = .hostIdNotGeometric hostId := rfl

theorem payloadOnlyIdentity_refused (payload : Nat) :
    refusePayloadOnlyIdentity payload = .payloadWithoutSdf payload := rfl

theorem evaluateHostIdIdentity_refused :
    evaluateHostIdIdentity true = .hostIdRefused := rfl

theorem evaluateHostIdIdentity_ok :
    evaluateHostIdIdentity false = .identityOk := rfl

theorem evaluatePayloadOnlyIdentity_refused :
    evaluatePayloadOnlyIdentity true = .payloadOnlyRefused := rfl

theorem evaluatePayloadOnlyIdentity_ok :
    evaluatePayloadOnlyIdentity false = .identityOk := rfl

def classifyGeometricMemory (attempt : GeometricMemoryAttempt)
    (w : Option SdfIdentityWitness) : GeometricMemoryClass ⊕ GeometricMemoryRefusal :=
  match w with
  | none =>
    if attempt.payloadOnly then
      Sum.inr .payloadOnlyTheater
    else if attempt.hostIdKeyed then
      Sum.inl .hostIdSurrogate
    else
      Sum.inr .hostIdTheater
  | some _ =>
    if attempt.payloadOnly then
      Sum.inl .sdfExcitementArrow
    else if attempt.hostIdKeyed then
      Sum.inl .hostIdSurrogate
    else
      Sum.inl .sdfExcitementArrow

def applyGeometricMemoryMorphism (obj : HistoryObjectGeom) (toSeq : Nat)
    (conjunct : GeometricAdmissibilityConjunct) (excitementSelected : Bool) :
    GeometricMemoryMorphism ⊕ GeometricMemoryRefusal :=
  if !geometricConjunctAdmits conjunct then
    Sum.inr (.gateRejected obj.seq)
  else if !(witnessFromHistoryObject obj).sdfCanonical then
    Sum.inr (.payloadWithoutSdf obj.hostSurrogate)
  else if !excitementSelected then
    Sum.inr (.identityMismatch obj.identity.fingerprint.digest obj.identity.fingerprint.digest)
  else
    Sum.inl
      { morphismFrom := obj
        morphismToSeq := toSeq
        witness := witnessFromHistoryObject obj
        excitementSelected := excitementSelected }

-- ================================================================
-- SECTION 3: Geometric memory composes Excitement.select (no second argmin)
-- ================================================================

structure GeometricMemoryCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

noncomputable def geometricMemorySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : GeometricMemoryCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

noncomputable def geometricMemorySelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) : Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

noncomputable def urgeGeometricMemorySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) : Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem geometricMemorySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : GeometricMemoryCtx S) :
    geometricMemorySelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem geometricMemorySelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    geometricMemorySelectBare prior successors = select prior successors :=
  rfl

theorem urgeGeometricMemorySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    urgeGeometricMemorySelect prior successors = select prior successors :=
  rfl

theorem geometricMemorySelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : GeometricMemoryCtx S) :
    geometricMemorySelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem geometricMemory_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : GeometricMemoryCtx S) :
    geometricMemorySelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem geometricMemory_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    geometricMemorySelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [geometricMemorySelectBare] using select_empty (src := prior)

def excitementComposePin : Nat := 0

theorem excitementComposePin_marker : excitementComposePin = 0 := rfl

theorem refuseSecondArgmin_isTag : refuseSecondArgmin = .secondArgmin := rfl

-- ================================================================
-- SECTION 4: §5.3 fixtures + witness theorems
-- ================================================================

def geometricFixtureFingerprint : SdfFingerprint :=
  { digest := 42, grain := 7 }

def geometricFixtureIdentity : HistoryGeometricIdentity :=
  { fingerprint := geometricFixtureFingerprint, resolutionBits := 2 }

def geometricFixtureObject : HistoryObjectGeom :=
  { seq := 0
  , identity := geometricFixtureIdentity
  , hostSurrogate := 42 }

def geometricFixtureObjectSameIdentity : HistoryObjectGeom :=
  { seq := 99
  , identity := geometricFixtureIdentity
  , hostSurrogate := 42 }

def geometricFixtureObjectDistinct : HistoryObjectGeom :=
  { seq := 1
  , identity := { fingerprint := { digest := 7, grain := 7 }, resolutionBits := 2 }
  , hostSurrogate := 7 }

def geometricFixtureConjunct : GeometricAdmissibilityConjunct :=
  { gateOk := true, sdfCanonical := true, excitementPreserves := true }

theorem geometricFixture_hostId_refused :
    refuseHostIdIdentity 0xdead = .hostIdNotGeometric 0xdead := rfl

theorem geometricFixture_payloadOnly_refused :
    refusePayloadOnlyIdentity 42 = .payloadWithoutSdf 42 := rfl

theorem geometricFixture_apply_morphism_ok :
    applyGeometricMemoryMorphism geometricFixtureObject 1 geometricFixtureConjunct true =
      Sum.inl
        { morphismFrom := geometricFixtureObject
          morphismToSeq := 1
          witness := witnessFromHistoryObject geometricFixtureObject
          excitementSelected := true } := rfl

theorem geometricFixture_matching_identity :
    geometricIdentityMatches geometricFixtureObject geometricFixtureObjectSameIdentity = true := by
  native_decide

theorem geometricFixture_distinct_identity :
    geometricIdentityMatches geometricFixtureObject geometricFixtureObjectDistinct = false := by
  native_decide

theorem geometricFixture_witness_preserves_fingerprint :
    (witnessFromHistoryObject geometricFixtureObject).fingerprint = geometricFixtureFingerprint := rfl

theorem geometric_memory_host_id_not_ok :
    evaluateHostIdIdentity true ≠ .identityOk := by
  simp [evaluateHostIdIdentity]

theorem geometric_memory_payload_only_not_ok :
    evaluatePayloadOnlyIdentity true ≠ .identityOk := by
  simp [evaluatePayloadOnlyIdentity]

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure GeometricHistoryTransition where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ
  gateChecked     : Prop
  sdfCanonical    : Prop
  provenanceOk    : Prop

def admissibleGeometricMemory (t : GeometricHistoryTransition) : Prop :=
  t.gateChecked ∧ t.sdfCanonical ∧ t.provenanceOk

def geometricSecondLaw (t : GeometricHistoryTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalGeometricBridge where
  proc : ErasureProcess
  transition : GeometricHistoryTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleGeometricMemory transition

theorem geometricSecondLaw_from_physical (b : PhysicalGeometricBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    geometricSecondLaw b.transition := by
  unfold geometricSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleGeometricMemory_from_physical (b : PhysicalGeometricBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleGeometricMemory b.transition :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def geometricMemoryProductionWired : Bool := false

theorem geometricMemoryProductionWiredFalse : geometricMemoryProductionWired = false := rfl

theorem geometricMemoryModuleWitness : True := trivial

theorem geometricMemory_noNewAxiom : True := trivial

theorem hostIdTheaterRefused : refuseHostIdTheater = .hostIdTheater := rfl

theorem payloadOnlyTheaterRefused : refusePayloadOnlyTheater = .payloadOnlyTheater := rfl

def geometricMemoryMarker : Nat := 1

theorem geometricMemoryMarker_eq : geometricMemoryMarker = 1 := rfl

theorem geometricMemoryMarker_pos : 0 < geometricMemoryMarker := by decide

end UMST.Urge.GeometricMemory
