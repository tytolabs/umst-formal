-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/UmstTomlRemotes.lean

  Meso acting Urge — §13.6 `[urge.remote.*]` in root `umst.toml` types.
  Typed parse of proposed remote policy rows; pre-push positive refuse —
  not only `!physics_green`. Composes `Excitement.select`; no second argmin.

  Anchored in `Urge.EntityRemote` / `Urge.ExcitementImport`.
  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import Urge.EntityRemote
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.EntityRemote UMST.Urge.ExcitementImport

namespace UMST.Urge.UmstTomlRemotes

-- ================================================================
-- SECTION 1: Root `umst.toml` `[urge.remote.*]` carriers
-- ================================================================

/-- One parsed `[urge.remote.*]` row from root `umst.toml` (§13.6). -/
structure UrgeRemoteTomlRow where
  sectionSuffix   : String
  entity          : UrgeEntity
  classification  : RemoteClassification
  canonical       : CanonicalRemote
  mirror          : MirrorRemote
  deriving Repr

/-- Parsed root `umst.toml` remote policy document. -/
structure UmstTomlRemotesDocument where
  rows : List UrgeRemoteTomlRow
  deriving Repr

/-- Parse failure for root `umst.toml` remote sections. -/
inductive TomlRemoteParseError where
  | noRemoteSections
  | missingField (sect field : String)
  | unknownValue (sect field value : String)
  deriving Repr

/-- Fail-closed import refusal — second local argmin is inadmissible. -/
inductive UmstTomlRemotesImportRefusal where
  | secondArgmin
  deriving Repr

/-- Verdict of root `umst.toml` remote operation class. -/
inductive UmstTomlRemotesVerdict where
  | documentOk
  | parseRefused
  | inadmissible
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: Row ↔ policy bridge + pre-push evaluation
-- ================================================================

/-- Full `umst.toml` section key for a parsed row. -/
def urgeRemoteTomlSectionKey (row : UrgeRemoteTomlRow) : String :=
  urgeRemoteSectionPrefix ++ row.sectionSuffix

/-- Bridge parsed TOML row to `EntityRemote` policy carrier. -/
def urgeRemoteTomlRowToPolicy (row : UrgeRemoteTomlRow) : UrgeRemotePolicy :=
  { sectionKey := row.sectionSuffix
    entity := row.entity
    classification := row.classification
    canonical := row.canonical
    mirror := row.mirror }

/-- Evaluate pre-push under parsed root `umst.toml` row (§16.8 host table). -/
def evaluateTomlPrePush (row : UrgeRemoteTomlRow) (host : String) :
    Sum EntityPrePushVerdict EntityPrePushRefusal :=
  evaluateEntityPrePush (urgeRemoteTomlRowToPolicy row) host

/-- §13.6 admissibility conjunct for root `umst.toml` rows (surrogate). -/
structure UmstTomlRemotesConjunct where
  gateOk                  : Bool
  documentTyped           : Bool
  excitementPreserves     : Bool
  deriving Repr

/-- Evaluate `admit(h) ⟺ gate ∧ document typed ∧ Excitement preserves`. -/
def umstTomlRemotesConjunctAdmits (c : UmstTomlRemotesConjunct) : Bool :=
  c.gateOk && c.documentTyped && c.excitementPreserves

/-- Classify blind parse vs typed document without performing I/O. -/
def evaluateUmstTomlRemotesOperation (isParseRefused : Bool) : UmstTomlRemotesVerdict :=
  if isParseRefused then .parseRefused else .documentOk

/-- Apply typed root `umst.toml` row check — fail closed on inadmissibility. -/
def applyUmstTomlRemoteRow (row : UrgeRemoteTomlRow) (host : String)
    (conjunct : UmstTomlRemotesConjunct) (excitementSelected : Bool) :
    Sum UrgeRemoteTomlRow EntityPrePushRefusal :=
  if !umstTomlRemotesConjunctAdmits conjunct then
    Sum.inr (.unclassifiedHostRefused .unclassified)
  else if !excitementSelected then
    Sum.inr (.unclassifiedHostRefused .unclassified)
  else
    match evaluateTomlPrePush row host with
    | Sum.inl _ => Sum.inl row
    | Sum.inr r => Sum.inr r

theorem umstTomlRemotesParseRefusedPositive :
    evaluateUmstTomlRemotesOperation true = UmstTomlRemotesVerdict.parseRefused := rfl

theorem umstTomlRemotesDocumentOkWhenNotParseRefused :
    evaluateUmstTomlRemotesOperation false = UmstTomlRemotesVerdict.documentOk := rfl

-- ================================================================
-- SECTION 3: Fixture document + honest parse surrogate
-- ================================================================

/-- Blueprint §13.6 `[urge.remote.labs-public]` from typed constants. -/
def umstTomlFixtureLabsPublic : UrgeRemoteTomlRow :=
  { sectionSuffix := "labs-public"
    entity := .labs
    classification := .publicOss
    canonical := .forge
    mirror := .github }

/-- Blueprint §13.6 `[urge.remote.compose-confidential]` from typed constants. -/
def umstTomlFixtureComposeConfidential : UrgeRemoteTomlRow :=
  { sectionSuffix := "compose-confidential"
    entity := .compose
    classification := .composeConfidential
    canonical := .forge
    mirror := .none }

/-- Fixture document from blueprint §13.6 root `umst.toml` excerpt. -/
def rootUmstTomlFixtureDocument : UmstTomlRemotesDocument :=
  { rows := [umstTomlFixtureLabsPublic, umstTomlFixtureComposeConfidential] }

/-- Honest parse surrogate — fixture-bounded document builder (no I/O). -/
def parseRootUmstTomlRemotesFixture :
    Sum UmstTomlRemotesDocument TomlRemoteParseError :=
  Sum.inl rootUmstTomlFixtureDocument

/-- Empty document surrogate — positive refuse `noRemoteSections`. -/
def parseRootUmstTomlRemotesEmpty :
    Sum UmstTomlRemotesDocument TomlRemoteParseError :=
  Sum.inr .noRemoteSections

theorem rootUmstTomlFixtureDocumentTwoRows :
    rootUmstTomlFixtureDocument.rows.length = 2 := rfl

theorem parseRootUmstTomlRemotesEmptyRefused :
    parseRootUmstTomlRemotesEmpty = Sum.inr TomlRemoteParseError.noRemoteSections := rfl

-- ================================================================
-- SECTION 5: §13.6 fixtures + witness theorems
-- ================================================================

def umstTomlFixtureConjunct : UmstTomlRemotesConjunct :=
  { gateOk := true, documentTyped := true, excitementPreserves := true }

def umstTomlFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

theorem umstTomlLabsPublicSectionKey :
    urgeRemoteTomlSectionKey umstTomlFixtureLabsPublic = "urge.remote.labs-public" := rfl

theorem umstTomlComposeConfidentialSectionKey :
    urgeRemoteTomlSectionKey umstTomlFixtureComposeConfidential =
      "urge.remote.compose-confidential" := rfl

theorem umstTomlRowToPolicyLabsPublic :
    urgeRemoteTomlRowToPolicy umstTomlFixtureLabsPublic = entityRemoteFixtureLabsPublic := rfl

theorem umstTomlRowToPolicyComposeConfidential :
    urgeRemoteTomlRowToPolicy umstTomlFixtureComposeConfidential =
      entityRemoteFixtureComposeConfidential := rfl

theorem umstTomlLabsGithubAdmitted :
    evaluateTomlPrePush umstTomlFixtureLabsPublic "github.com" = Sum.inl .admitted := rfl

theorem umstTomlComposeGithubRefused :
    evaluateTomlPrePush umstTomlFixtureComposeConfidential "github.com" =
      Sum.inr .composeGithubRefused := rfl

theorem umstTomlComposeOriginRefused :
    evaluateTomlPrePush umstTomlFixtureComposeConfidential "origin.cursor.com" =
      Sum.inr .composeOriginRefused := rfl

theorem umstTomlComposeForgeAdmitted :
    evaluateTomlPrePush umstTomlFixtureComposeConfidential "forge.tyto.in" =
      Sum.inl .admitted := rfl

theorem umstTomlFixtureApplyRowOk :
    applyUmstTomlRemoteRow umstTomlFixtureLabsPublic "forge.tyto.in"
      umstTomlFixtureConjunct true = Sum.inl umstTomlFixtureLabsPublic := rfl

theorem umstTomlSectionPrefixWitness :
    urgeRemoteSectionPrefix = "urge.remote." := rfl

-- ================================================================
-- SECTION 6: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure UmstTomlRemotesHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  documentTyped   : Prop
  provenanceOk    : Prop

def admissibleUmstTomlRemotes (h : UmstTomlRemotesHistoryMove) : Prop :=
  h.gateChecked ∧ h.documentTyped ∧ h.provenanceOk

theorem admissibleUmstTomlRemotes_intro (h : UmstTomlRemotesHistoryMove)
    (hg : h.gateChecked) (hd : h.documentTyped) (hp : h.provenanceOk) :
    admissibleUmstTomlRemotes h :=
  And.intro hg (And.intro hd hp)

abbrev admitUmstTomlRemotes := admissibleUmstTomlRemotes

-- ================================================================
-- SECTION 7: Honesty flags + catalog witnesses
-- ================================================================

theorem umstTomlRemotesPositiveRefuseNotSilent :
    evaluateUmstTomlRemotesOperation true ≠ UmstTomlRemotesVerdict.documentOk := by
  intro h
  cases h

theorem umstTomlComposeGithubPositiveRefuse :
    evaluateTomlPrePush umstTomlFixtureComposeConfidential "github.com" ≠
      Sum.inl EntityPrePushVerdict.admitted := by
  rw [umstTomlComposeGithubRefused]
  intro h
  cases h

theorem umstTomlComposeOriginPositiveRefuse :
    evaluateTomlPrePush umstTomlFixtureComposeConfidential "origin.cursor.com" ≠
      Sum.inl EntityPrePushVerdict.admitted := by
  rw [umstTomlComposeOriginRefused]
  intro h
  cases h

end UMST.Urge.UmstTomlRemotes
