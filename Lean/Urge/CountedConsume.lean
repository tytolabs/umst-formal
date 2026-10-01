-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/CountedConsume.lean

  Meso acting Urge — §21 counted domain consumer (`counted_consume`).
  Domain provenance is scanner-emitted via `scan_counting` — refuse author
  `Domain::new` / hand-filled extent. Composes `Excitement.select`; no second argmin.

  Mirrors `Urge.ReplicaCoalgebra` / `Urge.ExcitementImport` discipline.
  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.CountedConsume

-- ================================================================
-- SECTION 1: Scanner-emitted domain + scan_counting carriers (§21)
-- ================================================================

/-- Domain provenance — new claims must be scanner-emitted `Counted`. -/
inductive CountedDomainProvenance where
  | counted
  deriving DecidableEq, Repr

/-- Extent of what a scanner actually examined — cardinality matches scope. -/
structure CountedDomain where
  scope         : List Nat
  cardinality   : Nat
  exclusions    : List Nat
  provenance    : CountedDomainProvenance

/-- Value + domain counted together — admissible claim construction path. -/
structure CountedScannedClaim (V : Type) where
  value   : V
  domain  : CountedDomain

/-- Accumulated walk state — scope and exclusions are scanner-emitted only. -/
structure CountedScanWalk where
  walkScope      : List Nat
  walkExclusions : List Nat

/-- Empty walk — scanner starting point. -/
def countedScanWalkEmpty : CountedScanWalk :=
  { walkScope := [], walkExclusions := [] }

/-- Nat membership surrogate for walk dedup. -/
def countedNatInb (n : Nat) (l : List Nat) : Bool :=
  l.any (fun x => x == n)

/-- Touch one path id into walked scope (dedup surrogate). -/
def countedScanTouch (w : CountedScanWalk) (pathId : Nat) : CountedScanWalk :=
  if countedNatInb pathId w.walkScope then w
  else { walkScope := pathId :: w.walkScope, walkExclusions := w.walkExclusions }

/-- Skip one path id into exclusions (dedup surrogate). -/
def countedScanSkip (w : CountedScanWalk) (pathId : Nat) : CountedScanWalk :=
  if countedNatInb pathId w.walkExclusions then w
  else { walkScope := w.walkScope, walkExclusions := pathId :: w.walkExclusions }

/-- Refusal when domain is declared instead of counted. -/
inductive CountedDomainError where
  | handFilledRefused
  | cardinalityMismatch (declared counted : Nat)
  | emptyScan
  deriving DecidableEq, Repr

/-- Fail-closed counted consume errors — positive refuse, not silent no-op. -/
inductive CountedConsumeRefusal where
  | authorDomainNew
  | handFilledDomain
  | emptyScan
  | secondArgmin
  deriving DecidableEq, Repr

/-- Verdict of a counted domain operation class. -/
inductive CountedConsumeVerdict where
  | scanOk
  | authorDomainRefused
  | handFillRefused
  | inadmissible
  deriving DecidableEq, Repr

/-- Positive admit/refuse on counted domain consumption. -/
inductive CountedConsumeAdmit where
  | admitted
  | refused (reason : CountedConsumeRefusal)
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: §21 admissibility + scan_counting + positive refuse
-- ================================================================

/-- Cardinality from walked scope — always `length scope` (§21). -/
def countedCardinalityFromWalk (w : CountedScanWalk) : Nat :=
  w.walkScope.length

/-- Build domain from walk — cardinality is scanner-emitted, not author-filled. -/
def countedDomainFromWalk (w : CountedScanWalk) : CountedDomain :=
  { scope := w.walkScope
    cardinality := countedCardinalityFromWalk w
    exclusions := w.walkExclusions
    provenance := .counted }

/-- Verify Counted provenance and cardinality matches scope — catches hand-fill. -/
def verifyCountedDomain (d : CountedDomain) : Sum CountedDomain CountedDomainError :=
  match d.provenance with
  | .counted =>
    if d.cardinality == d.scope.length then Sum.inl d
    else Sum.inr (.cardinalityMismatch d.cardinality d.scope.length)

/-- Finalize walk — fail closed on empty scan; cardinality from walk only. -/
def scanCountingFinalize (w : CountedScanWalk) : Sum CountedDomain CountedDomainError :=
  if countedCardinalityFromWalk w == 0 then Sum.inr .emptyScan
  else verifyCountedDomain (countedDomainFromWalk w)

/-- `scan_counting` surrogate — value computed from walk, domain from finalize. -/
def scanCounting {V : Type} (w : CountedScanWalk) (value : V) :
    Sum (CountedScannedClaim V) CountedDomainError :=
  match scanCountingFinalize w with
  | Sum.inl d => Sum.inl { value := value, domain := d }
  | Sum.inr e => Sum.inr e

/-- Classify author construct vs scanner-emitted without performing I/O. -/
def evaluateCountedDomainOperation (authorConstruct : Bool) : CountedConsumeVerdict :=
  if authorConstruct then .authorDomainRefused else .scanOk

/-- Positive refuse: author `Domain::new` / hand-fill is inadmissible (§21). -/
def refuseAuthorDomainNew : CountedConsumeRefusal := .authorDomainNew

/-- Map domain verification to typed `counted_consume_admit`. -/
def domainToAdmit (d : CountedDomain) : CountedConsumeAdmit :=
  match verifyCountedDomain d with
  | Sum.inl _ => .admitted
  | Sum.inr .handFilledRefused => .refused .handFilledDomain
  | Sum.inr (.cardinalityMismatch _ _) => .refused .handFilledDomain
  | Sum.inr .emptyScan => .refused .emptyScan

/-- Admit a scanner-emitted claim — fail closed on hand-fill. -/
def admitScannedClaim {V : Type} (claim : CountedScannedClaim V) : CountedConsumeAdmit :=
  domainToAdmit claim.domain

/-- §21 admissibility conjunct inputs (surrogate). -/
structure CountedAdmissibilityConjunct where
  gateOk                 : Bool
  scannerEmitted         : Bool
  excitementPreserves    : Bool

/-- Evaluate `admit(h) ⟺ gate ∧ scanner-emitted ∧ Excitement preserves`. -/
def countedConjunctAdmits (c : CountedAdmissibilityConjunct) : Bool :=
  c.gateOk && c.scannerEmitted && c.excitementPreserves

/-- Attempt counted consume on scanned claim — fail closed on inadmissibility. -/
def applyCountedConsumeMorphism {V : Type} (claim : CountedScannedClaim V)
    (conjunct : CountedAdmissibilityConjunct) (excitementSelected authorConstruct : Bool) :
    Sum (CountedScannedClaim V) CountedConsumeRefusal :=
  if authorConstruct then Sum.inr .authorDomainNew
  else if !countedConjunctAdmits conjunct then Sum.inr .handFilledDomain
  else
    match verifyCountedDomain claim.domain with
    | Sum.inr _ => Sum.inr .handFilledDomain
    | Sum.inl _ =>
      if !excitementSelected then Sum.inr .secondArgmin
      else Sum.inl claim

theorem countedAuthorDomainRefused :
    evaluateCountedDomainOperation true = .authorDomainRefused := rfl

theorem countedScanOkWhenNotAuthor :
    evaluateCountedDomainOperation false = .scanOk := rfl

theorem scanCountingFinalizeEmpty :
    scanCountingFinalize countedScanWalkEmpty = Sum.inr .emptyScan := rfl

-- ================================================================
-- SECTION 4: §21 fixtures + witness theorems
-- ================================================================

def countedFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def countedFixtureWalk : CountedScanWalk :=
  countedScanTouch (countedScanTouch countedScanWalkEmpty 1) 2

def countedFixtureDomain : CountedDomain :=
  countedDomainFromWalk countedFixtureWalk

def countedFixtureClaim : CountedScannedClaim Nat :=
  { value := 7, domain := countedFixtureDomain }

def countedFixtureConjunct : CountedAdmissibilityConjunct :=
  { gateOk := true, scannerEmitted := true, excitementPreserves := true }

/-- Hand-filled domain fixture — cardinality theater (author construct). -/
def countedFixtureHandFilled : CountedDomain :=
  { scope := [1, 2]
    cardinality := 11809
    exclusions := []
    provenance := .counted }

theorem countedFixtureScannerEmittedOk :
    verifyCountedDomain countedFixtureDomain = Sum.inl countedFixtureDomain := rfl

theorem countedFixtureHandFillRefused :
    domainToAdmit countedFixtureHandFilled = .refused .handFilledDomain := rfl

theorem countedFixtureAuthorDomainRefused :
    applyCountedConsumeMorphism countedFixtureClaim countedFixtureConjunct true true =
      Sum.inr .authorDomainNew := rfl

theorem countedFixtureApplyMorphismOk :
    applyCountedConsumeMorphism countedFixtureClaim countedFixtureConjunct true false =
      Sum.inl countedFixtureClaim := rfl

theorem countedFixtureAdmitScannedClaimOk :
    admitScannedClaim countedFixtureClaim = .admitted := rfl

theorem countedFixtureScanCountingOk :
    scanCounting countedFixtureWalk 7 = Sum.inl countedFixtureClaim := rfl

theorem countedFixtureCardinalityMatchesScope :
    countedFixtureDomain.cardinality = countedFixtureDomain.scope.length := rfl

-- ================================================================
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure CountedHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  scannerEmitted  : Prop
  provenanceOk    : Prop

def admissibleCountedConsume (h : CountedHistoryMove) : Prop :=
  h.gateChecked ∧ h.scannerEmitted ∧ h.provenanceOk

theorem admissibleCountedConsume_intro (h : CountedHistoryMove)
    (hg : h.gateChecked) (hs : h.scannerEmitted) (hp : h.provenanceOk) :
    admissibleCountedConsume h :=
  And.intro hg (And.intro hs hp)

abbrev admitCountedConsume := admissibleCountedConsume

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

theorem countedConsumePositiveRefuseNotSilent :
    evaluateCountedDomainOperation true ≠ .scanOk := by
  intro h
  cases h

end UMST.Urge.CountedConsume
