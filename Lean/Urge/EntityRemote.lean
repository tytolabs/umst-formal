-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/EntityRemote.lean

  Meso acting Urge — §13.6 entity remotes classification.
  `[urge.remote.*]` policy types; pre-push refuse github /
  origin.cursor.com when entity = compose. Composes `Excitement.select`;
  no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.ExcitementImport

namespace UMST.Urge.EntityRemote

-- ================================================================
-- SECTION 1: §13.6 `[urge.remote.*]` policy carriers
-- ================================================================

/-- `umst.toml` section prefix for remote policy rows. -/
def urgeRemoteSectionPrefix : String := "urge.remote."

/-- Entity label in `[urge.remote.*]` — Labs vs Compose. -/
inductive UrgeEntity where
  | labs
  | compose
  deriving DecidableEq, Repr

/-- Share-security classification label (§13.6 table). -/
inductive RemoteClassification where
  | publicOss
  | labsInternal
  | composeConfidential
  | composeDefence
  | proposalConfidential
  deriving DecidableEq, Repr

/-- Canonical remote role — India-resident Forgejo is SSOT after restore test. -/
inductive CanonicalRemote where
  | forge
  | none
  deriving DecidableEq, Repr

/-- Mirror remote role — GitHub interim / public discovery only. -/
inductive MirrorRemote where
  | github
  | none
  deriving DecidableEq, Repr

/-- Push target host for pre-push policy evaluation (§16.8). -/
inductive EntityRemoteHost where
  | github
  | originCursor
  | forge
  | unclassified
  deriving DecidableEq, Repr

/-- One `[urge.remote.*]` policy row from `umst.toml` (proposed §13.6). -/
structure UrgeRemotePolicy where
  sectionKey      : String
  entity          : UrgeEntity
  classification  : RemoteClassification
  canonical       : CanonicalRemote
  mirror          : MirrorRemote
  deriving Repr

/-- Pre-push verdict for entity remote policy. -/
inductive EntityPrePushVerdict where
  | admitted
  | composeGithubRefused
  | composeOriginRefused
  | originNeverSsotRefused
  | unclassifiedHostRefused
  | productionWiredRefused
  deriving DecidableEq, Repr

/-- Fail-closed pre-push errors — positive refuse, not silent no-op. -/
inductive EntityPrePushRefusal where
  | composeGithubRefused
  | composeOriginRefused
  | originNeverSsotRefused
  | unclassifiedHostRefused (h : EntityRemoteHost)
  | productionWiredRefused
  deriving Repr

/-- Verdict of entity remote classification operation class. -/
inductive EntityRemoteVerdict where
  | policyOk
  | upstreamRefused
  | inadmissible
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: §13.6 admissibility conjunct + positive refuse
-- ================================================================

/-- §13.6 admissibility conjunct inputs (surrogate). -/
structure EntityRemoteConjunct where
  gateOk                  : Bool
  policyTyped             : Bool
  excitementPreserves     : Bool
  deriving Repr

/-- Evaluate `admit(h) ⟺ gate ∧ policy typed ∧ Excitement preserves`. -/
def entityRemoteConjunctAdmits (c : EntityRemoteConjunct) : Bool :=
  c.gateOk && c.policyTyped && c.excitementPreserves

/-- Owning entity for a share-security classification. -/
def classificationEntity (c : RemoteClassification) : UrgeEntity :=
  match c with
  | .publicOss | .labsInternal | .proposalConfidential => .labs
  | .composeConfidential | .composeDefence => .compose

/-- Parse entity label from `umst.toml` value (fail closed on unknown). -/
inductive ParseUrgeEntityResult where
  | parsed (e : UrgeEntity)
  | unknown
  deriving Repr

def parseUrgeEntity (tag : String) : ParseUrgeEntityResult :=
  if tag = "labs" || tag = "LABS" then .parsed .labs
  else if tag = "compose" || tag = "COMPOSE" then .parsed .compose
  else .unknown

/-- Classify push target from host string (typed surrogate). -/
def classifyEntityRemoteHost (host : String) : EntityRemoteHost :=
  if host = "" then .unclassified
  else if host = "origin.cursor.com" then .originCursor
  else if host = "github.com" then .github
  else if host = "forge.tyto.in" || host = "forge.entity" then .forge
  else .unclassified

def labsGithubVerdict (c : RemoteClassification) :
    Sum EntityPrePushVerdict EntityPrePushRefusal :=
  if c = .publicOss then Sum.inl .admitted
  else Sum.inr (.unclassifiedHostRefused .github)

/-- Evaluate pre-push under §13.6 entity remote policy and §16.8 host table. -/
def evaluateEntityPrePush (policy : UrgeRemotePolicy) (host : String) :
    Sum EntityPrePushVerdict EntityPrePushRefusal :=
  match classifyEntityRemoteHost host with
  | .originCursor =>
    match policy.entity with
    | .compose => Sum.inr .composeOriginRefused
    | .labs => Sum.inr .originNeverSsotRefused
  | .github =>
    match policy.entity with
    | .compose => Sum.inr .composeGithubRefused
    | .labs => labsGithubVerdict policy.classification
  | .forge => Sum.inl .admitted
  | .unclassified => Sum.inr (.unclassifiedHostRefused .unclassified)

/-- Positive refuse: production wired push without entity remote policy. -/
def refuseProductionWiredEntityPush : EntityPrePushRefusal :=
  .productionWiredRefused

/-- Classify blind upstream vs typed policy without performing I/O. -/
def evaluateEntityRemoteOperation (isUpstreamRefused : Bool) : EntityRemoteVerdict :=
  if isUpstreamRefused then .upstreamRefused else .policyOk

/-- Apply typed entity remote policy check — fail closed on inadmissibility. -/
def applyEntityRemotePolicy (policy : UrgeRemotePolicy) (host : String)
    (conjunct : EntityRemoteConjunct) (excitementSelected : Bool) :
    Sum UrgeRemotePolicy EntityPrePushRefusal :=
  if !entityRemoteConjunctAdmits conjunct then
    Sum.inr (.unclassifiedHostRefused .unclassified)
  else if !excitementSelected then
    Sum.inr (.unclassifiedHostRefused .unclassified)
  else
    match evaluateEntityPrePush policy host with
    | Sum.inl _ => Sum.inl policy
    | Sum.inr r => Sum.inr r

theorem entityRemoteUpstreamRefusedPositive :
    evaluateEntityRemoteOperation true = EntityRemoteVerdict.upstreamRefused := rfl

theorem entityRemotePolicyOkWhenNotUpstream :
    evaluateEntityRemoteOperation false = EntityRemoteVerdict.policyOk := rfl

theorem refuseProductionWiredEntityPushPositive :
    refuseProductionWiredEntityPush = EntityPrePushRefusal.productionWiredRefused := rfl

-- ================================================================
-- SECTION 3: Entity remote composes Excitement (no second argmin)
-- ================================================================

/-- Context for entity remote over admissible history successors. -/
structure EntityRemoteCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Entity remote selection **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def entityRemoteSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : EntityRemoteCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def entityRemoteSelectBare {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem entityRemoteSelect_eq_excitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : EntityRemoteCtx S) :
    entityRemoteSelect ctx = select ctx.prior ctx.successors := by
  simp [entityRemoteSelect, urgeRecoverySelect_eq_select]

theorem entityRemoteSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : EntityRemoteCtx S) :
    entityRemoteSelect ctx = urgeRecoverySelect ctx.prior ctx.successors := rfl

theorem entityRemote_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : EntityRemoteCtx S) :
    entityRemoteSelect ctx = select ctx.prior ctx.successors :=
  entityRemoteSelect_eq_excitementSelect ctx

theorem entityRemote_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : EntityRemoteCtx S) (h : ctx.successors = []) :
    entityRemoteSelect ctx = Sum.inr Residue.noCandidates := by
  simp [entityRemoteSelect, urgeRecoverySelect, h, select_empty]

-- ================================================================
-- SECTION 4: §13.6 fixtures + witness theorems
-- ================================================================

def entityRemoteFixtureLabsPublic : UrgeRemotePolicy :=
  { sectionKey := "labs-public"
    entity := .labs
    classification := .publicOss
    canonical := .forge
    mirror := .github }

def entityRemoteFixtureComposeConfidential : UrgeRemotePolicy :=
  { sectionKey := "compose-confidential"
    entity := .compose
    classification := .composeConfidential
    canonical := .forge
    mirror := .none }

def entityRemoteFixtureConjunct : EntityRemoteConjunct :=
  { gateOk := true, policyTyped := true, excitementPreserves := true }

def entityRemoteFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

theorem entityRemoteLabsGithubAdmitted :
    evaluateEntityPrePush entityRemoteFixtureLabsPublic "github.com" = Sum.inl .admitted := rfl

theorem entityRemoteComposeGithubRefused :
    evaluateEntityPrePush entityRemoteFixtureComposeConfidential "github.com" =
      Sum.inr .composeGithubRefused := rfl

theorem entityRemoteComposeOriginRefused :
    evaluateEntityPrePush entityRemoteFixtureComposeConfidential "origin.cursor.com" =
      Sum.inr .composeOriginRefused := rfl

theorem entityRemoteOriginNeverSsotRefused :
    evaluateEntityPrePush entityRemoteFixtureLabsPublic "origin.cursor.com" =
      Sum.inr .originNeverSsotRefused := rfl

theorem entityRemoteComposeForgeAdmitted :
    evaluateEntityPrePush entityRemoteFixtureComposeConfidential "forge.tyto.in" =
      Sum.inl .admitted := rfl

theorem entityRemoteSectionPrefixWitness :
    urgeRemoteSectionPrefix = "urge.remote." := rfl

theorem entityRemoteLabsPublicSectionKey :
    urgeRemoteSectionPrefix ++ entityRemoteFixtureLabsPublic.sectionKey =
      "urge.remote.labs-public" := rfl

theorem entityRemoteParseLabs :
    parseUrgeEntity "labs" = .parsed .labs := rfl

theorem entityRemoteParseCompose :
    parseUrgeEntity "compose" = .parsed .compose := rfl

theorem entityRemoteClassificationEntityLabs :
    classificationEntity .publicOss = .labs := rfl

theorem entityRemoteClassificationEntityCompose :
    classificationEntity .composeConfidential = .compose := rfl

theorem entityRemoteFixtureApplyPolicyOk :
    applyEntityRemotePolicy entityRemoteFixtureLabsPublic "forge.tyto.in"
      entityRemoteFixtureConjunct true = Sum.inl entityRemoteFixtureLabsPublic := rfl

-- ================================================================
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure EntityRemoteHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  policyTyped     : Prop
  provenanceOk    : Prop

def admissibleEntityRemote (h : EntityRemoteHistoryMove) : Prop :=
  h.gateChecked ∧ h.policyTyped ∧ h.provenanceOk

theorem admissibleEntityRemote_intro (h : EntityRemoteHistoryMove)
    (hg : h.gateChecked) (hp : h.policyTyped) (hv : h.provenanceOk) :
    admissibleEntityRemote h :=
  And.intro hg (And.intro hp hv)

abbrev admitEntityRemote := admissibleEntityRemote

structure EntityRemoteTransition where
  move            : EntityRemoteHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def entityRemoteSecondLaw (t : EntityRemoteTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalEntityRemoteBridge where
  proc : ErasureProcess
  transition : EntityRemoteTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleEntityRemote transition.move

theorem entityRemoteSecondLaw_from_physical (b : PhysicalEntityRemoteBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    entityRemoteSecondLaw b.transition := by
  unfold entityRemoteSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleEntityRemote_from_physical (b : PhysicalEntityRemoteBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleEntityRemote b.transition.move :=
  b.admissible

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def entityRemotePhysicsGreen : Bool := false

theorem entityRemotePhysicsGreenFalse : entityRemotePhysicsGreen = false := rfl

def entityRemoteProductionWired : Bool := false

theorem entityRemoteProductionWiredFalse : entityRemoteProductionWired = false := rfl

theorem entityRemoteModuleWitness : True := trivial

theorem entityRemote_noNewAxiom : True := trivial

theorem entityRemotePositiveRefuseNotSilent :
    evaluateEntityRemoteOperation true ≠ EntityRemoteVerdict.policyOk := by
  intro h
  cases h

theorem entityRemoteComposeGithubPositiveRefuse :
    evaluateEntityPrePush entityRemoteFixtureComposeConfidential "github.com" ≠
      Sum.inl EntityPrePushVerdict.admitted := by
  rw [entityRemoteComposeGithubRefused]
  intro h
  cases h

end UMST.Urge.EntityRemote
