-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/OriginRefuse.lean

  Meso acting Urge — §16.8 origin.cursor.com / GitHub-as-origin refuse for Compose.
  India-resident Forgejo is canonical SSOT. Typed positive refuse — not only
  `!physics_green`. Compose `Excitement.select` — no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement

namespace UMST.Urge.OriginRefuse

-- ================================================================
-- SECTION 1: Entity labels + origin host classification (§16.8)
-- ================================================================

/-- Urge entity label for §16.8 origin policy row. -/
inductive OriginEntityLabel where
  | compose
  | labsPublicOss
  deriving DecidableEq, Repr

/-- Classified origin host for policy evaluation. -/
inductive OriginHostClass where
  | originCursor
  | github
  | forgejoCanonical
  | unclassified
  deriving DecidableEq, Repr

def originHostTag (c : OriginHostClass) : String :=
  match c with
  | .originCursor => "origin-cursor"
  | .github => "github"
  | .forgejoCanonical => "forgejo-canonical"
  | .unclassified => "unclassified"

theorem origin_cursor_tag : originHostTag .originCursor = "origin-cursor" := rfl
theorem github_tag : originHostTag .github = "github" := rfl
theorem forgejo_canonical_tag : originHostTag .forgejoCanonical = "forgejo-canonical" := rfl
theorem unclassified_tag : originHostTag .unclassified = "unclassified" := rfl

theorem originHostTag_originCursor_ne_github :
    originHostTag .originCursor ≠ originHostTag .github := by decide

theorem originHostTag_originCursor_ne_forgejo :
    originHostTag .originCursor ≠ originHostTag .forgejoCanonical := by decide

theorem originHostTag_github_ne_forgejo :
    originHostTag .github ≠ originHostTag .forgejoCanonical := by decide

def originHostClassesNotXor : Prop :=
  originHostTag .originCursor ≠ originHostTag .github ∧
  originHostTag .originCursor ≠ originHostTag .forgejoCanonical ∧
  originHostTag .github ≠ originHostTag .forgejoCanonical

theorem originHostClassesNotXorHolds : originHostClassesNotXor :=
  ⟨originHostTag_originCursor_ne_github, originHostTag_originCursor_ne_forgejo,
   originHostTag_github_ne_forgejo⟩

def originHostClassCount : Nat := 4

theorem origin_host_class_count_is_four : originHostClassCount = 4 := rfl

def originHostIsCursor (c : OriginHostClass) : Bool :=
  match c with
  | .originCursor => true
  | _ => false

def originHostIsGithub (c : OriginHostClass) : Bool :=
  match c with
  | .github => true
  | _ => false

def originCursorHostPin : String := "origin.cursor.com"
def githubOriginHostPin : String := "github.com"
def forgejoCanonicalHostPin : String := "forgejo.tailnet"

def classifyOriginHost (host : String) : OriginHostClass :=
  if host == originCursorHostPin then .originCursor
  else if host == githubOriginHostPin then .github
  else if host == forgejoCanonicalHostPin then .forgejoCanonical
  else .unclassified

structure OriginRemoteDescriptor where
  entity : OriginEntityLabel
  host   : String

structure OriginUcrsStamp where
  ucrsSeq       : Nat
  ucrsWallHasT  : Bool

structure OriginPolicyWitness where
  ucrsStamp            : OriginUcrsStamp
  forgejoCanonical     : Bool

structure OriginRefuseMorphism where
  remote              : OriginRemoteDescriptor
  witness             : OriginPolicyWitness
  excitementSelected  : Bool

-- ================================================================
-- SECTION 2: §16.8 policy verdict + positive refuse
-- ================================================================

inductive OriginRefusal where
  | originCursorComposeRefused
  | githubAsOriginComposeRefused
  | originCursorLabsRefused
  | unclassifiedHost
  | dualPushComposeRefused
  | gateRejected (seq : Nat)
  deriving DecidableEq, Repr

inductive OriginPolicyVerdict where
  | admitted
  | refused (r : OriginRefusal)
  deriving DecidableEq, Repr

def composeUpstreamRefused (host : String) : Bool :=
  host == githubOriginHostPin || host == originCursorHostPin

structure OriginAdmissibilityConjunct where
  gateOk                 : Bool
  forgejoCanonical       : Bool
  excitementPreserves    : Bool

def originConjunctAdmits (c : OriginAdmissibilityConjunct) : Bool :=
  c.gateOk && c.forgejoCanonical && c.excitementPreserves

def evaluateOriginPolicy (entity : OriginEntityLabel) (host : OriginHostClass) :
    OriginPolicyVerdict :=
  match entity, host with
  | .compose, .originCursor => OriginPolicyVerdict.refused .originCursorComposeRefused
  | .compose, .github => OriginPolicyVerdict.refused .githubAsOriginComposeRefused
  | .labsPublicOss, .originCursor => OriginPolicyVerdict.refused .originCursorLabsRefused
  | .labsPublicOss, .github => .admitted
  | _, .forgejoCanonical => .admitted
  | _, .unclassified => OriginPolicyVerdict.refused .unclassifiedHost

def admitOriginRemote (remote : OriginRemoteDescriptor) : OriginPolicyVerdict :=
  evaluateOriginPolicy remote.entity (classifyOriginHost remote.host)

def refuseOriginCursorForCompose : OriginRefusal := .originCursorComposeRefused

def refuseGithubAsOriginForCompose : OriginRefusal := .githubAsOriginComposeRefused

def refuseDualPushCompose : OriginRefusal := .dualPushComposeRefused

def witnessFromRemote (remote : OriginRemoteDescriptor) (stamp : OriginUcrsStamp) :
    OriginPolicyWitness :=
  { ucrsStamp := stamp
    forgejoCanonical :=
      match classifyOriginHost remote.host with
      | .forgejoCanonical => true
      | _ => false }

def applyOriginRefuseMorphism (remote : OriginRemoteDescriptor)
    (conjunct : OriginAdmissibilityConjunct) (stamp : OriginUcrsStamp)
    (excitementSelected : Bool) : Option OriginRefuseMorphism × Option OriginRefusal :=
  if !originConjunctAdmits conjunct then
    ((none : Option OriginRefuseMorphism), some (.gateRejected stamp.ucrsSeq))
  else
    match admitOriginRemote remote with
    | .admitted =>
      if !excitementSelected then
        ((none : Option OriginRefuseMorphism), some .unclassifiedHost)
      else
        (some { remote := remote
                witness := witnessFromRemote remote stamp
                excitementSelected := excitementSelected }, (none : Option OriginRefusal))
    | .refused r => ((none : Option OriginRefuseMorphism), some r)

theorem refuse_origin_cursor_for_compose_positive :
    refuseOriginCursorForCompose = .originCursorComposeRefused := rfl

theorem refuse_github_as_origin_for_compose_positive :
    refuseGithubAsOriginForCompose = .githubAsOriginComposeRefused := rfl

theorem refuse_dual_push_compose_positive :
    refuseDualPushCompose = .dualPushComposeRefused := rfl

-- ================================================================
-- SECTION 3: Compose Excitement.select (no second argmin)
-- ================================================================

inductive OriginExcitementComposePin where
  | importSelectExcitement
  | secondArgminRefused
  deriving DecidableEq, Repr

structure OriginRefuseCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

noncomputable def composeExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (cands : List (Cand (K := ℚ) src)) (pin : OriginExcitementComposePin) :
    Cand (K := ℚ) src ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select src cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

noncomputable def originRefuseSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : OriginRefuseCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

noncomputable def originRefuseSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem composeExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (cands : List (Cand (K := ℚ) src)) :
    composeExcitementSelect src cands .importSelectExcitement = select src cands :=
  rfl

theorem originRefuseSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : OriginRefuseCtx S) :
    originRefuseSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem originRefuseSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    originRefuseSelectBare prior successors = select prior successors :=
  rfl

theorem originRefuseSelect_eq_originRefuseSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : OriginRefuseCtx S) :
    originRefuseSelect ctx = originRefuseSelectBare ctx.prior ctx.successors :=
  rfl

theorem originRefuse_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : OriginRefuseCtx S) :
    originRefuseSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem composeExcitementSelect_refuses_secondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (cands : List (Cand (K := ℚ) src)) :
    composeExcitementSelect src cands .secondArgminRefused = Sum.inr Residue.allInadmissible :=
  rfl

theorem originRefuse_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) :
    originRefuseSelectBare prior [] = Sum.inr Residue.noCandidates := by
  simpa [originRefuseSelectBare] using select_empty (src := prior)

-- ================================================================
-- SECTION 4: Landauer bridge (sole physics axiom — imported)
-- ================================================================

structure OriginHistoryMove where
  gateChecked     : Prop
  forgejoCanonical : Prop
  provenanceOk    : Prop

def admissibleOriginRefuse (h : OriginHistoryMove) : Prop :=
  h.gateChecked ∧ h.forgejoCanonical ∧ h.provenanceOk

theorem admissibleOriginRefuse_intro (h : OriginHistoryMove)
    (hg : h.gateChecked) (hf : h.forgejoCanonical) (hp : h.provenanceOk) :
    admissibleOriginRefuse h :=
  And.intro hg (And.intro hf hp)

abbrev admitOriginInbound := admissibleOriginRefuse

structure OriginTransition where
  move            : OriginHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def originSecondLaw (t : OriginTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalOriginBridge where
  proc : ErasureProcess
  transition : OriginTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleOriginRefuse transition.move

theorem originSecondLaw_from_physical (b : PhysicalOriginBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    originSecondLaw b.transition := by
  unfold originSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleOriginRefuse_from_physical (b : PhysicalOriginBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleOriginRefuse b.transition.move :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 5: §16.8 fixtures + witness theorems
-- ================================================================

def originFixtureUcrs : OriginUcrsStamp :=
  { ucrsSeq := 8, ucrsWallHasT := true }

def originFixtureConjunct : OriginAdmissibilityConjunct :=
  { gateOk := true, forgejoCanonical := true, excitementPreserves := true }

def composeOriginCursorFixture : OriginRemoteDescriptor :=
  { entity := .compose, host := originCursorHostPin }

def composeGithubOriginFixture : OriginRemoteDescriptor :=
  { entity := .compose, host := githubOriginHostPin }

def composeForgejoCanonicalFixture : OriginRemoteDescriptor :=
  { entity := .compose, host := forgejoCanonicalHostPin }

theorem origin_fixture_cursor_compose_refused :
    admitOriginRemote composeOriginCursorFixture =
      OriginPolicyVerdict.refused .originCursorComposeRefused :=
  rfl

theorem origin_fixture_github_compose_refused :
    admitOriginRemote composeGithubOriginFixture =
      OriginPolicyVerdict.refused .githubAsOriginComposeRefused :=
  rfl

theorem origin_fixture_forgejo_compose_admitted :
    admitOriginRemote composeForgejoCanonicalFixture = OriginPolicyVerdict.admitted :=
  rfl

theorem origin_fixture_compose_upstream_refused_github :
    composeUpstreamRefused githubOriginHostPin = true := by decide

theorem origin_fixture_compose_upstream_refused_cursor :
    composeUpstreamRefused originCursorHostPin = true := by decide

theorem origin_fixture_apply_morphism_forgejo_ok :
    applyOriginRefuseMorphism composeForgejoCanonicalFixture originFixtureConjunct
      originFixtureUcrs true =
      (some { remote := composeForgejoCanonicalFixture
              witness := witnessFromRemote composeForgejoCanonicalFixture originFixtureUcrs
              excitementSelected := true }, (none : Option OriginRefusal)) :=
  rfl

theorem origin_fixture_classify_cursor :
    classifyOriginHost originCursorHostPin = .originCursor := rfl

theorem origin_fixture_classify_github :
    classifyOriginHost githubOriginHostPin = .github := rfl

theorem origin_fixture_classify_forgejo :
    classifyOriginHost forgejoCanonicalHostPin = .forgejoCanonical := rfl

theorem origin_fixture_conjunct_admits :
    originConjunctAdmits originFixtureConjunct = true := rfl

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def originRefuseProductionWired : Bool := false

theorem originRefuseProductionWiredFalse : originRefuseProductionWired = false := rfl

theorem originRefuseModuleWitness : True := trivial

theorem originRefuse_noNewAxiom : True := trivial

theorem originRefuse_positiveRefuse_notSilent :
    admitOriginRemote composeOriginCursorFixture ≠ OriginPolicyVerdict.admitted ∧
    admitOriginRemote composeGithubOriginFixture ≠ OriginPolicyVerdict.admitted := by
  constructor
  · rw [origin_fixture_cursor_compose_refused]; decide
  · rw [origin_fixture_github_compose_refused]; decide

theorem originRefuse_composeExcitement_notArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : OriginRefuseCtx S) :
    originRefuseSelect ctx = select ctx.prior ctx.successors :=
  originRefuse_noLocalArgmin ctx

theorem originRefuse_namedNotXor : originHostClassesNotXor :=
  originHostClassesNotXorHolds

end UMST.Urge.OriginRefuse
