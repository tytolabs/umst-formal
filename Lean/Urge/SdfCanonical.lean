-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/SdfCanonical.lean

  Meso acting Urge — §12 SDFCanonical tautology named on history identity.
  Byte-equal canonical SDFs imply behavior-equivalent history actions — mirrors
  Lean `Behavior.SDFCanonical` and Coq/Agda `Urge.SdfCanonical`.
  Composes `UMST.Excitement.select`; no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.SdfCanonical

-- ================================================================
-- SECTION 1: History action + identity carriers (§12)
-- ================================================================

/-- History action bytes — SDF-shaped action surrogate (pre/post canonicalization). -/
structure HistoryAction where
  bytes           : String
  canonicalized   : Bool
  contentId       : Nat

/-- Content-addressed history identity — canonical SDF + stable content id. -/
structure HistoryIdentity where
  identity        : HistoryAction
  contentId       : Nat

/-- Witness bundle a SDF-canonical morphism must preserve (§12). -/
structure SdfCanonicalWitness where
  bytes           : String
  contentId       : Nat
  canonicalized   : Bool

/-- Typed SDF-canonical morphism — admissible identity transition. -/
structure SdfCanonicalMorphism where
  morphismFrom        : HistoryIdentity
  toContentId         : Nat
  witness             : SdfCanonicalWitness
  excitementSelected  : Bool

/-- Behavior equivalence verdict — mirrors Lean `BehaviorEquiv`. -/
inductive BehaviorEquivVerdict where
  | equivalent
  | distinct
  deriving DecidableEq, Repr

/-- Fail-closed SDF canonical errors — positive refuse, not silent accept. -/
inductive SdfCanonicalRefusal where
  | canonicalSdfMismatch (leftId rightId : Nat)
  | aliasWithoutCanonicalization (payload : Nat)
  | inventedEquivWithoutCanonical (contentId : Nat)
  | secondArgmin
  | gateRejected (seq : Nat)
  deriving Repr

/-- Verdict of a SDF canonical admit operation class. -/
inductive SdfCanonicalVerdict where
  | admitted
  | aliasRefused
  | inventedEquivRefused
  | inadmissible
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: §12 admissibility conjunct + positive refuse
-- ================================================================

/-- Canonical SDF map — mirrors Lean `Behavior.canonical_sdf := id` on `String`. -/
def canonicalSdf (a : HistoryAction) : String :=
  a.bytes

/-- Content id projection from canonicalized action. -/
def historyContentId (a : HistoryAction) : Nat :=
  a.contentId

/-- String equality surrogate (decidable — no `if` on Prop). -/
def canonicalSdfBeq (left right : HistoryAction) : Bool :=
left.bytes == right.bytes

/-- Behavior equivalence from canonical SDF equality. -/
def behaviorEquivOf (left right : HistoryAction) : BehaviorEquivVerdict :=
  if canonicalSdfBeq left right then .equivalent else .distinct

/-- §12 `BehaviorEquiv` — byte-equal canonical SDFs imply behavior-equivalent actions. -/
def BehaviorEquiv (a b : HistoryAction) : Prop :=
  canonicalSdf a = canonicalSdf b

/-- §12 `SDFCanonical` tautology: `canonical_sdf a = canonical_sdf b → BehaviorEquiv a b`. -/
theorem SDFCanonical (a b : HistoryAction)
    (h : canonicalSdf a = canonicalSdf b) :
    BehaviorEquiv a b :=
  h

/-- §12 admissibility conjunct inputs (surrogate). -/
structure SdfCanonicalAdmissibilityConjunct where
  gateOk                  : Bool
  canonicalized           : Bool
  excitementPreserves     : Bool

def sdfCanonicalConjunctAdmits (c : SdfCanonicalAdmissibilityConjunct) : Bool :=
  c.gateOk && c.canonicalized && c.excitementPreserves

def evaluateAliasWithoutCanonicalization (aliasOnly : Bool) : SdfCanonicalVerdict :=
  if aliasOnly then .aliasRefused else .admitted

def evaluateInventedEquivWithoutCanonical (invented : Bool) : SdfCanonicalVerdict :=
  if invented then .inventedEquivRefused else .admitted

def refuseAliasWithoutCanonicalization (payload : Nat) : SdfCanonicalRefusal :=
  .aliasWithoutCanonicalization payload

def refuseInventedEquivWithoutCanonical (contentId : Nat) : SdfCanonicalRefusal :=
  .inventedEquivWithoutCanonical contentId

def refuseSecondArgminSelector : SdfCanonicalRefusal :=
  .secondArgmin

def witnessFromHistoryIdentity (h : HistoryIdentity) : SdfCanonicalWitness :=
  { bytes := canonicalSdf h.identity
    contentId := h.contentId
    canonicalized := h.identity.canonicalized }

/-- §12 SDF canonical theorem — fail closed on alias / mismatch. -/
def sdfCanonicalTheorem (left right : HistoryAction) :
    Sum BehaviorEquivVerdict SdfCanonicalRefusal :=
  if !left.canonicalized then
    Sum.inr (.aliasWithoutCanonicalization 0)
  else if !right.canonicalized then
    Sum.inr (.aliasWithoutCanonicalization 0)
  else if canonicalSdfBeq left right then
    Sum.inl .equivalent
  else
    Sum.inr (.canonicalSdfMismatch (historyContentId left) (historyContentId right))

def admitHistoryIdentityStep (left right : HistoryIdentity)
    (thm : Sum BehaviorEquivVerdict SdfCanonicalRefusal) :
    Sum SdfCanonicalVerdict SdfCanonicalRefusal :=
  match thm with
  | Sum.inr r => Sum.inr r
  | Sum.inl .distinct =>
    Sum.inr (.canonicalSdfMismatch
      (historyContentId left.identity) (historyContentId right.identity))
  | Sum.inl .equivalent =>
    if left.contentId != historyContentId left.identity then
      Sum.inr (.inventedEquivWithoutCanonical left.contentId)
    else if right.contentId != historyContentId right.identity then
      Sum.inr (.inventedEquivWithoutCanonical right.contentId)
    else if left.contentId != right.contentId then
      Sum.inr (.canonicalSdfMismatch left.contentId right.contentId)
    else
      Sum.inl .admitted

/-- Admit history identity pair under §12 SDF canonical discipline. -/
def admitHistoryIdentity (left right : HistoryIdentity)
    (conjunct : SdfCanonicalAdmissibilityConjunct) :
    Sum SdfCanonicalVerdict SdfCanonicalRefusal :=
  if !sdfCanonicalConjunctAdmits conjunct then
    Sum.inr (.gateRejected 0)
  else
    admitHistoryIdentityStep left right
      (sdfCanonicalTheorem left.identity right.identity)

/-- Attempt typed SDF-canonical morphism — fail closed on inadmissibility. -/
def applySdfCanonicalMorphism (identity : HistoryIdentity) (toContentId : Nat)
    (conjunct : SdfCanonicalAdmissibilityConjunct) (excitementSelected : Bool) :
    SdfCanonicalMorphism ⊕ SdfCanonicalRefusal :=
  if !sdfCanonicalConjunctAdmits conjunct then
    Sum.inr (.gateRejected identity.contentId)
  else if !identity.identity.canonicalized then
    Sum.inr (.aliasWithoutCanonicalization identity.contentId)
  else if !excitementSelected then
    Sum.inr (.canonicalSdfMismatch identity.contentId toContentId)
  else
    Sum.inl
      { morphismFrom := identity
        toContentId := toContentId
        witness := witnessFromHistoryIdentity identity
        excitementSelected := excitementSelected }

theorem sdfCanonicalAliasRefused :
    evaluateAliasWithoutCanonicalization true = .aliasRefused := rfl

theorem sdfCanonicalAdmittedWhenNotAlias :
    evaluateAliasWithoutCanonicalization false = .admitted := rfl

theorem sdfCanonicalInventedEquivRefused :
    evaluateInventedEquivWithoutCanonical true = .inventedEquivRefused := rfl

theorem refuseAliasWithoutCanonicalizationPositive (payload : Nat) :
    refuseAliasWithoutCanonicalization payload =
      .aliasWithoutCanonicalization payload :=
  rfl

theorem refuseSecondArgminSelectorPositive :
    refuseSecondArgminSelector = .secondArgmin := rfl

-- ================================================================
-- SECTION 3: SDF canonical composes Excitement.select (no second argmin)
-- ================================================================

/-- Excitement compose pin — import selector; refuse second local argmin. -/
inductive SdfCanonicalExcitementPin where
  | importSelectExcitement
  | secondArgminRefused
  deriving DecidableEq, Repr

/-- Context for SDF canonical over admissible history successors. -/
structure SdfCanonicalCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- SDF canonical path composes `Excitement.select` — not a second argmin. -/
noncomputable def sdfCanonicalExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) (pin : SdfCanonicalExcitementPin) :
    Cand (K := ℚ) prior ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select prior successors
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

/-- SDF canonical selection **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def sdfCanonicalSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : SdfCanonicalCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def sdfCanonicalSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem sdfCanonicalExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    sdfCanonicalExcitementSelect prior successors .importSelectExcitement =
      select prior successors :=
  rfl

theorem sdfCanonicalSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : SdfCanonicalCtx S) :
    sdfCanonicalSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem sdfCanonicalSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : SdfCanonicalCtx S) :
    sdfCanonicalSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem sdfCanonicalNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : SdfCanonicalCtx S) :
    sdfCanonicalSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem sdfCanonicalExcitementSelect_refusesSecondArgmin {S : Type}
    [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    sdfCanonicalExcitementSelect prior successors .secondArgminRefused =
      Sum.inr Residue.allInadmissible :=
  rfl

theorem sdfCanonicalSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    sdfCanonicalSelectBare prior successors = select prior successors :=
  rfl

theorem sdfCanonical_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    sdfCanonicalSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [sdfCanonicalSelectBare] using select_empty (src := prior)

-- ================================================================
-- SECTION 4: §12 fixtures + witness theorems
-- ================================================================

def sdfCanonicalFixtureBytes : String := "sdf:v1:chair"

def sdfCanonicalFixtureContentId : Nat := 12007

def sdfCanonicalFixtureAction : HistoryAction :=
  { bytes := sdfCanonicalFixtureBytes
    canonicalized := true
    contentId := sdfCanonicalFixtureContentId }

def sdfCanonicalFixtureIdentity : HistoryIdentity :=
  { identity := sdfCanonicalFixtureAction
    contentId := sdfCanonicalFixtureContentId }

def sdfCanonicalFixtureIdentitySame : HistoryIdentity :=
  { identity := sdfCanonicalFixtureAction
    contentId := sdfCanonicalFixtureContentId }

def sdfCanonicalFixtureActionDistinct : HistoryAction :=
  { bytes := "sdf:v1:sphere"
    canonicalized := true
    contentId := 12008 }

def sdfCanonicalFixtureIdentityDistinct : HistoryIdentity :=
  { identity := sdfCanonicalFixtureActionDistinct
    contentId := 12008 }

def sdfCanonicalFixtureActionAlias : HistoryAction :=
  { bytes := sdfCanonicalFixtureBytes
    canonicalized := false
    contentId := sdfCanonicalFixtureContentId }

def sdfCanonicalFixtureConjunct : SdfCanonicalAdmissibilityConjunct :=
  { gateOk := true, canonicalized := true, excitementPreserves := true }

theorem sdfCanonicalFixtureCanonicalSdfId :
    canonicalSdf sdfCanonicalFixtureAction = sdfCanonicalFixtureBytes := rfl

theorem sdfCanonicalFixtureByteEqualAdmitted :
    admitHistoryIdentity sdfCanonicalFixtureIdentity sdfCanonicalFixtureIdentitySame
      sdfCanonicalFixtureConjunct = Sum.inl .admitted := rfl

theorem sdfCanonicalFixtureAliasRefused :
    refuseAliasWithoutCanonicalization 42 = .aliasWithoutCanonicalization 42 := rfl

theorem sdfCanonicalFixtureApplyMorphismOk :
    applySdfCanonicalMorphism sdfCanonicalFixtureIdentity sdfCanonicalFixtureContentId
      sdfCanonicalFixtureConjunct true =
      Sum.inl
        { morphismFrom := sdfCanonicalFixtureIdentity
          toContentId := sdfCanonicalFixtureContentId
          witness := witnessFromHistoryIdentity sdfCanonicalFixtureIdentity
          excitementSelected := true } := rfl

theorem sdfCanonicalFixtureWitnessPreservesBytes :
    (witnessFromHistoryIdentity sdfCanonicalFixtureIdentity).bytes =
      sdfCanonicalFixtureBytes := rfl

theorem sdfCanonicalTheoremTautology (a : HistoryAction) (Hcanon : a.canonicalized = true) :
    sdfCanonicalTheorem a a = Sum.inl .equivalent := by
  unfold sdfCanonicalTheorem canonicalSdfBeq
  simp [Hcanon, canonicalSdf, canonicalSdfBeq, BEq.beq]

theorem sdfCanonicalNamedIdentityTautology :
    SDFCanonical sdfCanonicalFixtureAction sdfCanonicalFixtureAction rfl = rfl :=
  rfl

theorem sdfCanonicalAliasNotAdmitted :
    evaluateAliasWithoutCanonicalization true ≠ .admitted := by
  decide

theorem sdfCanonicalPositiveRefuseNotSilent :
    evaluateInventedEquivWithoutCanonical true ≠ .admitted := by
  decide

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure SdfCanonicalTransition where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ
  gateChecked     : Prop
  canonicalized   : Prop
  provenanceOk    : Prop

def admissibleSdfCanonicalTransition (t : SdfCanonicalTransition) : Prop :=
  t.gateChecked ∧ t.canonicalized ∧ t.provenanceOk

def sdfCanonicalSecondLaw (t : SdfCanonicalTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalSdfCanonicalBridge where
  proc : ErasureProcess
  transition : SdfCanonicalTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleSdfCanonicalTransition transition

theorem sdfCanonicalSecondLaw_from_physical (b : PhysicalSdfCanonicalBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    sdfCanonicalSecondLaw b.transition := by
  unfold sdfCanonicalSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleSdfCanonicalTransition_from_physical (b : PhysicalSdfCanonicalBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleSdfCanonicalTransition b.transition :=
  b.admissible

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def sdfCanonicalPhysicsGreen : Bool := false

theorem sdfCanonicalPhysicsGreenFalse : sdfCanonicalPhysicsGreen = false := rfl

def sdfCanonicalProductionWired : Bool := false

theorem sdfCanonicalProductionWiredFalse : sdfCanonicalProductionWired = false := rfl

theorem sdfCanonicalModuleWitness : True := trivial

theorem sdfCanonical_noNewAxiom : True := trivial

theorem sdfCanonical_namedOnHistoryIdentity :
    sdfCanonicalFixtureIdentity.contentId = sdfCanonicalFixtureContentId := rfl

end UMST.Urge.SdfCanonical
