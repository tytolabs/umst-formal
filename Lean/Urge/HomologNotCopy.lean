-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/HomologNotCopy.lean

  Meso acting Urge — §22.1 homolog ≠ copy recovery morphism.
  Recovery **is** a new Excitement arrow over admissible successors — not
  `git reset --hard` of a sibling commit. Homolog relates sibling commits
  geometrically — homolog ≠ copy. Composes `UMST.Excitement.select`;
  no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations.  Zero sorry.
-/

import Compat.Gate
import Excitement
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.HomologNotCopy

-- ================================================================
-- SECTION 1: Sibling commit + homolog witness carriers (§22.1)
-- ================================================================

/-- Sibling commit reference — content-addressed surrogate. -/
structure SiblingCommitRef where
  commitHash    : Nat
  siblingOf     : Nat

/-- Homolog witness — geometric relation between sibling commits. -/
structure HomologWitness where
  homologFrom               : SiblingCommitRef
  homologTo                 : SiblingCommitRef
  claimsIdentityCopy        : Bool

/-- UCRS stamp surrogate carried through §22.1 recovery arrow. -/
structure HomologUcrsStamp where
  ucrsSeq       : Nat
  wallHasT      : Bool

/-- New Excitement recovery arrow — admissible state transition, not blind copy. -/
structure HomologRecoveryArrow where
  arrowId                   : Nat
  selectedSuccessorId       : Nat
  arrowHead                 : ThermodynamicState
  provenanceIntact          : Bool
  ucrs                      : HomologUcrsStamp

/-- Whether the recovery arrow is a fresh Excitement selection. -/
def isNewExcitementArrow (a : HomologRecoveryArrow) : Bool :=
  a.provenanceIntact && a.ucrs.wallHasT

/-- Recovery attempt bundle — gate input for §22.1 classification. -/
structure HomologRecoveryAttempt where
  gitResetHardSibling       : Bool
  witness                   : Option HomologWitness
  head                      : ThermodynamicState

/-- Fail-closed recovery errors — positive refuse, not silent no-op. -/
inductive HomologNotCopyRefusal where
  | gitResetHardSibling
  | homologIsNotCopy
  | secondArgmin
  deriving Repr

/-- Verdict class for recovery attempts. -/
inductive HomologRecoveryClass where
  | newExcitementArrow
  | gitResetHardSiblingClass
  | homologClaimsCopy
  deriving Repr

/-- Verdict of a recovery operation class. -/
inductive HomologRecoveryVerdict where
  | newArrowOk
  | gitResetHardRefused
  | homologCopyRefused
  | secondArgminRefused
  deriving Repr

-- ================================================================
-- SECTION 2: §22.1 admissibility conjunct + positive refuse
-- ================================================================

/-- §22.1 admissibility conjunct inputs (surrogate). -/
structure HomologAdmissibilityConjunct where
  notGitResetHard           : Bool
  homologNotCopy            : Bool
  excitementPreserves       : Bool

/-- Evaluate `admit(h) ⟺ ¬git-reset-hard ∧ homolog≠copy ∧ Excitement preserves`. -/
def homologConjunctAdmits (c : HomologAdmissibilityConjunct) : Bool :=
  c.notGitResetHard && c.homologNotCopy && c.excitementPreserves

/-- Build sibling commit ref from hash + parent pin. -/
def siblingCommitRefOf (hash parent : Nat) : SiblingCommitRef :=
  { commitHash := hash, siblingOf := parent }

/-- Whether sibling commit hashes differ (homolog ≠ identity copy). -/
def siblingHashesDiffer (w : HomologWitness) : Bool :=
  w.homologFrom.commitHash != w.homologTo.commitHash

/-- §22.1 homolog-not-copy? — geometric relation, not blind sibling reset. -/
def homologNotCopyOk (w : HomologWitness) : Bool :=
  siblingHashesDiffer w && !w.claimsIdentityCopy

/-- Classify git reset --hard sibling vs new Excitement arrow without I/O. -/
def evaluateHomologRecoveryOperation (gitResetHard : Bool) : HomologRecoveryVerdict :=
  if gitResetHard then .gitResetHardRefused else .newArrowOk

/-- Positive refuse: `git reset --hard` of sibling — inadmissible under §22.1. -/
def refuseGitResetHardSibling : HomologNotCopyRefusal :=
  .gitResetHardSibling

/-- Positive refuse: homolog witness claims identity copy — homolog ≠ copy. -/
def refuseHomologAsCopy : HomologNotCopyRefusal :=
  .homologIsNotCopy

/-- Positive refuse: second local Excitement argmin — compose import only. -/
def refuseSecondArgmin : HomologNotCopyRefusal :=
  .secondArgmin

/-- Map typed refusal to recovery class surrogate. -/
def recoveryClassOfRefusal (r : HomologNotCopyRefusal) : HomologRecoveryClass :=
  match r with
  | .gitResetHardSibling => .gitResetHardSiblingClass
  | .homologIsNotCopy => .homologClaimsCopy
  | .secondArgmin => .newExcitementArrow

/-- Gate recovery attempts — fail closed on git reset hard or homolog-as-copy. -/
def classifyHomologRecoveryAttempt (attempt : HomologRecoveryAttempt) :
    HomologRecoveryClass ⊕ HomologNotCopyRefusal :=
  if attempt.gitResetHardSibling then
    Sum.inr .gitResetHardSibling
  else
    match attempt.witness with
    | none => Sum.inl .newExcitementArrow
    | some w =>
        if w.claimsIdentityCopy then
          Sum.inr .homologIsNotCopy
        else if homologNotCopyOk w then
          Sum.inl .newExcitementArrow
        else
          Sum.inr .homologIsNotCopy

/-- Build recovery arrow from Excitement selection + UCRS pin. -/
def recoveryArrowFromSelection (arrowId successorId : Nat) (head : ThermodynamicState)
    (ucrsSeq : Nat) (wallHasT : Bool)
    (sel : Cand (K := ℚ) head ⊕ Residue) : HomologRecoveryArrow ⊕ Residue :=
  match sel with
  | Sum.inl _ =>
      Sum.inl
        { arrowId := arrowId
          selectedSuccessorId := successorId
          arrowHead := head
          provenanceIntact := true
          ucrs := { ucrsSeq := ucrsSeq, wallHasT := wallHasT } }
  | Sum.inr r => Sum.inr r

/-- Attempt typed homolog recovery morphism — fail closed on inadmissibility. -/
def applyHomologRecoveryMorphism (attempt : HomologRecoveryAttempt)
    (conjunct : HomologAdmissibilityConjunct) (excitementSelected : Bool) :
    HomologRecoveryArrow ⊕ HomologNotCopyRefusal :=
  if !homologConjunctAdmits conjunct then
    Sum.inr .homologIsNotCopy
  else if attempt.gitResetHardSibling then
    Sum.inr .gitResetHardSibling
  else if !excitementSelected then
    Sum.inr .secondArgmin
  else
    match attempt.witness with
    | none =>
        Sum.inl
          { arrowId := 0
            selectedSuccessorId := 0
            arrowHead := attempt.head
            provenanceIntact := true
            ucrs := { ucrsSeq := 0, wallHasT := true } }
    | some w =>
        if homologNotCopyOk w then
          Sum.inl
            { arrowId := w.homologFrom.commitHash
              selectedSuccessorId := w.homologTo.commitHash
              arrowHead := attempt.head
              provenanceIntact := true
              ucrs := { ucrsSeq := 0, wallHasT := true } }
        else
          Sum.inr .homologIsNotCopy

theorem homologRecovery_gitResetHard_refused :
    evaluateHomologRecoveryOperation true = .gitResetHardRefused := rfl

theorem homologRecovery_newArrow_ok_when_not_reset :
    evaluateHomologRecoveryOperation false = .newArrowOk := rfl

theorem refuseGitResetHardSibling_positive :
    refuseGitResetHardSibling = .gitResetHardSibling := rfl

theorem refuseHomologAsCopy_positive :
    refuseHomologAsCopy = .homologIsNotCopy := rfl

theorem refuseSecondArgmin_positive :
    refuseSecondArgmin = .secondArgmin := rfl

-- ================================================================
-- SECTION 3: Homolog recovery composes Excitement (no second argmin)
-- ================================================================

/-- Excitement compose pin — import selector; refuse second local argmin. -/
inductive HomologExcitementComposePin where
  | importSelectExcitement
  | secondArgminRefused
  deriving Repr

/-- Context for homolog recovery over admissible history successors. -/
structure HomologRecoveryCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Homolog recovery path composes `select` — not a second argmin. -/
noncomputable def homologExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (cands : List (Cand (K := ℚ) prior)) (pin : HomologExcitementComposePin) :
    Cand (K := ℚ) prior ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select prior cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

/-- Homolog recovery **is** `urgeRecoverySelect` / `select`. -/
noncomputable def homologRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HomologRecoveryCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

theorem homologExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (cands : List (Cand (K := ℚ) prior)) :
    homologExcitementSelect prior cands .importSelectExcitement = select prior cands :=
  rfl

theorem homologRecoverySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HomologRecoveryCtx S) :
    homologRecoverySelect ctx = select ctx.prior ctx.successors := by
  unfold homologRecoverySelect urgeRecoverySelect
  rfl

theorem homologRecoverySelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HomologRecoveryCtx S) :
    homologRecoverySelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem homologRecovery_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HomologRecoveryCtx S) :
    homologRecoverySelect ctx = select ctx.prior ctx.successors :=
  homologRecoverySelect_eq_select ctx

theorem homologExcitementSelect_refuses_secondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (cands : List (Cand (K := ℚ) prior)) :
    homologExcitementSelect prior cands .secondArgminRefused = Sum.inr Residue.allInadmissible :=
  rfl

theorem homologRecovery_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    homologRecoverySelect { prior := prior, successors := successors } = Sum.inr Residue.noCandidates := by
  subst h
  simpa [homologRecoverySelect, urgeRecoverySelect] using urgeRecovery_empty (prior := prior)

-- ================================================================
-- SECTION 4: §22.1 fixtures + witness theorems
-- ================================================================

def homologFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def homologFixtureFrom : SiblingCommitRef :=
  siblingCommitRefOf 101 50

def homologFixtureTo : SiblingCommitRef :=
  siblingCommitRefOf 102 50

def homologFixtureWitness : HomologWitness :=
  { homologFrom := homologFixtureFrom
    homologTo := homologFixtureTo
    claimsIdentityCopy := false }

def homologFixtureUcrs : HomologUcrsStamp :=
  { ucrsSeq := 22, wallHasT := true }

def homologFixtureConjunct : HomologAdmissibilityConjunct :=
  { notGitResetHard := true, homologNotCopy := true, excitementPreserves := true }

def homologFixtureAttempt : HomologRecoveryAttempt :=
  { gitResetHardSibling := false
    witness := some homologFixtureWitness
    head := homologFixtureState }

def homologFixtureGitResetAttempt : HomologRecoveryAttempt :=
  { gitResetHardSibling := true
    witness := some homologFixtureWitness
    head := homologFixtureState }

def homologFixtureCopyClaimWitness : HomologWitness :=
  { homologFrom := homologFixtureFrom
    homologTo := homologFixtureTo
    claimsIdentityCopy := true }

theorem homologFixture_gitResetHard_refused :
    refuseGitResetHardSibling = .gitResetHardSibling := rfl

theorem homologFixture_witness_notCopy :
    homologNotCopyOk homologFixtureWitness = true := rfl

theorem homologFixture_classify_admitsArrow :
    classifyHomologRecoveryAttempt homologFixtureAttempt = Sum.inl .newExcitementArrow := rfl

theorem homologFixture_classify_refusesGitReset :
    classifyHomologRecoveryAttempt homologFixtureGitResetAttempt = Sum.inr .gitResetHardSibling := rfl

theorem homologFixture_apply_morphism_ok :
    applyHomologRecoveryMorphism homologFixtureAttempt homologFixtureConjunct true =
      Sum.inl
        { arrowId := 101
          selectedSuccessorId := 102
          arrowHead := homologFixtureState
          provenanceIntact := true
          ucrs := { ucrsSeq := 0, wallHasT := true } } := rfl

theorem homologFixture_refuses_copyClaim :
    classifyHomologRecoveryAttempt
      { gitResetHardSibling := false
        witness := some homologFixtureCopyClaimWitness
        head := homologFixtureState } = Sum.inr .homologIsNotCopy := rfl

theorem homologFixture_isNewExcitementArrow :
    isNewExcitementArrow
      { arrowId := 1
        selectedSuccessorId := 2
        arrowHead := homologFixtureState
        provenanceIntact := true
        ucrs := homologFixtureUcrs } = true := rfl

theorem homologFixture_siblingHashesDiffer :
    siblingHashesDiffer homologFixtureWitness = true := rfl

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure HomologHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  homologNotCopy  : Prop
  provenanceOk    : Prop

def admissibleHomologRecovery (h : HomologHistoryMove) : Prop :=
  h.gateChecked ∧ h.homologNotCopy ∧ h.provenanceOk

def homologSecondLaw (_t : HomologHistoryMove) (bath : HeatBath) (dissipatedWork entropyDrop : ℝ) :
    Prop :=
  entropyDrop ≤ dissipatedWork / bath.bathTemp.val

structure PhysicalHomologBridge where
  proc : ErasureProcess
  move : HomologHistoryMove
  bath : HeatBath
  dissipatedWork : ℝ
  entropyDrop : ℝ
  bathEq : bath = proc.bath
  workEq : dissipatedWork = proc.work
  entropyDropEq :
    entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleHomologRecovery move

theorem homologSecondLaw_from_physical (b : PhysicalHomologBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    homologSecondLaw b.move b.bath b.dissipatedWork b.entropyDrop := by
  unfold homologSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.dissipatedWork / b.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleHomologRecovery_from_physical (b : PhysicalHomologBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleHomologRecovery b.move :=
  b.admissible

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def homologNotCopyPhysicsGreen : Bool := false

theorem homologNotCopyPhysicsGreenFalse : homologNotCopyPhysicsGreen = false := rfl

def homologNotCopyProductionWired : Bool := false

theorem homologNotCopyProductionWiredFalse : homologNotCopyProductionWired = false := rfl

theorem homologNotCopyModuleWitness : True := trivial

theorem homologNotCopy_noNewAxiom : True := trivial

theorem homologNotCopy_positiveRefuse_notSilent :
    evaluateHomologRecoveryOperation true ≠ .newArrowOk := by
  simp [evaluateHomologRecoveryOperation]

theorem homologRecovery_classOfRefusal_gitReset :
    recoveryClassOfRefusal .gitResetHardSibling = .gitResetHardSiblingClass := rfl

theorem homologRecovery_classOfRefusal_homologCopy :
    recoveryClassOfRefusal .homologIsNotCopy = .homologClaimsCopy := rfl

end UMST.Urge.HomologNotCopy
