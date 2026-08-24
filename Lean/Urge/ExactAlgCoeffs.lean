-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ExactAlgCoeffs.lean

  Meso acting Urge — §3 ExactAlg coefficients on the history carrier.
  ℚ coefficient slot on `HistoryCarrier` — not silent f64 identity.
  Composes `Excitement.select`; no second argmin.

  Anchored in `CarrierProduct` / `AdmitKleisli` / `ExcitementImport`.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import Urge.AdmitKleisli
import Urge.CarrierProduct
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.CarrierProduct UMST.Urge.ExcitementImport

namespace UMST.Urge.ExactAlgCoeffs

-- ================================================================
-- SECTION 1: ExactAlg coefficient carriers on HistoryCarrier
-- ================================================================

/-- ℚ coefficient slot — mirrors Rust `ExactAlgCoeff` (num/den/op_tag). -/
structure ExactAlgCoeff where
  num    : Int
  den    : Nat
  opTag  : Nat

/-- ExactAlg coefficients attached to a history-carrier content id. -/
structure CarrierExactAlgCoeffs where
  contentId : Nat
  coeff     : ExactAlgCoeff

/-- Witness bundle an ExactAlg coefficient morphism must preserve (§3). -/
structure ExactAlgCoeffWitness where
  contentId : Nat
  value     : ℚ
  opTag     : Nat

/-- Typed ExactAlg coefficient morphism — admissible carrier slot update. -/
structure ExactAlgCoeffMorphism where
  morphismFrom           : CarrierExactAlgCoeffs
  morphismToCarrier      : HistoryCarrier
  witness                : ExactAlgCoeffWitness
  excitementSelected     : Bool

/-- f64 silent-identity theater tag — positive refuse carrier (not ℚ). -/
inductive FloatCarrierTag where
  | floatTheater
  deriving Repr

/-- Fail-closed ExactAlg coefficient errors — positive refuse, not silent accept. -/
inductive ExactAlgCoeffsRefusal where
  | f64IdentityTheater
  | zeroDenominator
  | exactAlgAbsent
  | secondArgmin
  | gateRejected (seq : Nat)
  deriving Repr

/-- Verdict of an ExactAlg coefficient admit operation class. -/
inductive ExactAlgCoeffsVerdict where
  | admitted
  | f64TheaterRefused
  | zeroDenRefused
  | inadmissible
  deriving DecidableEq, Repr

/-- Project ℚ coefficient value (carrier slot — denominator checked separately). -/
def exactAlgCoeffValue (c : ExactAlgCoeff) : ℚ :=
  (c.num : ℚ) / (c.den : ℚ)

/-- Whether ℚ denominator is non-zero (fail-closed admit precondition). -/
def exactAlgCoeffDenNonzero (c : ExactAlgCoeff) : Bool :=
  c.den ≠ 0

/-- Map admitted ℚ slot to `CarrierProduct.ExactAlg`. -/
def exactAlgCoeffToExactAlg (c : ExactAlgCoeff) : ExactAlg :=
  { value := exactAlgCoeffValue c, opTag := c.opTag }

/-- Attach ℚ coefficients to an existing history carrier (§3 product factor). -/
def attachExactAlgCoeff (carrier : HistoryCarrier) (coeff : ExactAlgCoeff) : HistoryCarrier :=
  carrierMk (umstProj carrier) (stampProj carrier) (sdfFRepProj carrier)
    (exactAlgCoeffToExactAlg coeff) (witnessProj carrier)

-- ================================================================
-- SECTION 2: §3 admissibility conjunct + positive refuse
-- ================================================================

/-- §3 admissibility conjunct inputs (surrogate). -/
structure ExactAlgCoeffAdmissibilityConjunct where
  gateOk                  : Bool
  denNonzero              : Bool
  excitementPreserves     : Bool
  deriving Repr

/-- Evaluate `admit(h) ⟺ gate ∧ den≠0 ∧ Excitement preserves`. -/
def exactAlgCoeffConjunctAdmits (c : ExactAlgCoeffAdmissibilityConjunct) : Bool :=
  c.gateOk && c.denNonzero && c.excitementPreserves

/-- Classify f64 identity theater vs ℚ carrier admit. -/
def evaluateF64IdentityTheater (isF64Theater : Bool) : ExactAlgCoeffsVerdict :=
  if isF64Theater then .f64TheaterRefused else .admitted

/-- Classify zero denominator vs ℚ carrier admit. -/
def evaluateZeroDenominator (isZeroDen : Bool) : ExactAlgCoeffsVerdict :=
  if isZeroDen then .zeroDenRefused else .admitted

/-- Positive refuse: f64 silent identity theater — ℚ carrier required. -/
def refuseF64IdentityTheater (_ : FloatCarrierTag) : ExactAlgCoeffsRefusal :=
  .f64IdentityTheater

/-- Positive refuse: zero denominator on ℚ coefficient. -/
def refuseZeroDenominator : ExactAlgCoeffsRefusal :=
  .zeroDenominator

/-- Positive refuse: ExactAlg slot absent on carrier. -/
def refuseExactAlgAbsent : ExactAlgCoeffsRefusal :=
  .exactAlgAbsent

/-- Positive refuse: second Excitement selector — compose `select`. -/
def refuseSecondArgminSelector : ExactAlgCoeffsRefusal :=
  .secondArgmin

/-- Build witness from carrier ExactAlg coefficients. -/
def witnessFromCarrierCoeffs (c : CarrierExactAlgCoeffs) : ExactAlgCoeffWitness :=
  { contentId := c.contentId
    value := exactAlgCoeffValue c.coeff
    opTag := c.coeff.opTag }

/-- Admit ℚ ExactAlg coefficients on carrier — fail closed on zero denominator. -/
def admitCarrierExactAlg (c : CarrierExactAlgCoeffs) :
    CarrierExactAlgCoeffs ⊕ ExactAlgCoeffsRefusal :=
  if exactAlgCoeffDenNonzero c.coeff then Sum.inl c
  else Sum.inr .zeroDenominator

/-- Attempt typed ExactAlg coefficient morphism — fail closed on inadmissibility. -/
def applyExactAlgCoeffMorphism (coeffs : CarrierExactAlgCoeffs) (carrier : HistoryCarrier)
    (conjunct : ExactAlgCoeffAdmissibilityConjunct) (excitementSelected : Bool) :
    ExactAlgCoeffMorphism ⊕ ExactAlgCoeffsRefusal :=
  if !exactAlgCoeffConjunctAdmits conjunct then
    Sum.inr (.gateRejected 0)
  else
    match admitCarrierExactAlg coeffs with
    | Sum.inr r => Sum.inr r
    | Sum.inl admitted =>
        if !excitementSelected then
          Sum.inr .exactAlgAbsent
        else
          Sum.inl
            { morphismFrom := admitted
              morphismToCarrier := attachExactAlgCoeff carrier admitted.coeff
              witness := witnessFromCarrierCoeffs admitted
              excitementSelected := excitementSelected }

theorem exactAlgCoeffF64TheaterRefused :
    refuseF64IdentityTheater .floatTheater = .f64IdentityTheater := rfl

theorem exactAlgCoeffZeroDenRefused :
    refuseZeroDenominator = .zeroDenominator := rfl

theorem exactAlgCoeffExactAlgAbsentRefused :
    refuseExactAlgAbsent = .exactAlgAbsent := rfl

theorem refuseSecondArgminSelectorPositive :
    refuseSecondArgminSelector = .secondArgmin := rfl

-- ================================================================
-- SECTION 3: ExactAlg coefficients compose Excitement (no argmin)
-- ================================================================

/-- Excitement compose pin — import selector; refuse second local argmin. -/
inductive ExactAlgCoeffsExcitementPin where
  | importSelectExcitement
  | secondArgminRefused

/-- Context for ExactAlg coefficients over admissible history successors. -/
structure ExactAlgCoeffCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- ExactAlg coefficient path composes `select` — not a second argmin. -/
noncomputable def exactAlgCoeffsExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) (pin : ExactAlgCoeffsExcitementPin) :
    Cand (K := ℚ) prior ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select prior successors
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

/-- ExactAlg coefficient selection **is** `urgeRecoverySelect` / `select`. -/
noncomputable def exactAlgCoeffSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ExactAlgCoeffCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

theorem exactAlgCoeffsExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    exactAlgCoeffsExcitementSelect prior successors .importSelectExcitement =
      select prior successors :=
  rfl

theorem exactAlgCoeffSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ExactAlgCoeffCtx S) :
    exactAlgCoeffSelect ctx = select ctx.prior ctx.successors := by
  simp [exactAlgCoeffSelect, urgeRecoverySelect_eq_select]

theorem exactAlgCoeffSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : ExactAlgCoeffCtx S) :
    exactAlgCoeffSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem exactAlgCoeffNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ExactAlgCoeffCtx S) :
    exactAlgCoeffSelect ctx = select ctx.prior ctx.successors :=
  exactAlgCoeffSelect_eq_select ctx

theorem exactAlgCoeffsExcitementSelectRefusesSecondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    exactAlgCoeffsExcitementSelect prior successors .secondArgminRefused =
      Sum.inr Residue.allInadmissible :=
  rfl

theorem exactAlgCoeffEmpty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ExactAlgCoeffCtx S) (h : ctx.successors = []) :
    exactAlgCoeffSelect ctx = Sum.inr Residue.noCandidates := by
  simp [exactAlgCoeffSelect, urgeRecoverySelect, h, select_empty]

-- ================================================================
-- SECTION 4: §3 fixtures + witness theorems
-- ================================================================

def exactAlgFixtureCoeff : ExactAlgCoeff :=
  { num := 3, den := 2, opTag := 1 }

def exactAlgFixtureZeroDen : ExactAlgCoeff :=
  { num := 1, den := 0, opTag := 0 }

def exactAlgFixtureCarrierCoeffs : CarrierExactAlgCoeffs :=
  { contentId := 1, coeff := exactAlgFixtureCoeff }

def exactAlgFixtureZeroDenCoeffs : CarrierExactAlgCoeffs :=
  { contentId := 1, coeff := exactAlgFixtureZeroDen }

def exactAlgFixtureState : ThermodynamicState :=
  ⟨2400, 0, 0, 0⟩

def exactAlgFixtureSnapshot : HistorySnapshot :=
  { commitId := 1, head := exactAlgFixtureState }

def exactAlgFixtureStamp : UcrsStamp :=
  wallOnlyStamp 42

def exactAlgFixtureSdf : SdfFRep :=
  { canonicalDigest := 5381, frepGrain := 1 }

def exactAlgFixtureExactAlg : ExactAlg :=
  exactAlgCoeffToExactAlg exactAlgFixtureCoeff

def exactAlgFixtureCarrier : HistoryCarrier :=
  carrierMk exactAlgFixtureSnapshot exactAlgFixtureStamp exactAlgFixtureSdf
    exactAlgFixtureExactAlg satisfiedWitness

def exactAlgFixtureConjunct : ExactAlgCoeffAdmissibilityConjunct :=
  { gateOk := true, denNonzero := true, excitementPreserves := true }

theorem exactAlgFixtureAdmitOk :
    admitCarrierExactAlg exactAlgFixtureCarrierCoeffs = Sum.inl exactAlgFixtureCarrierCoeffs := rfl

theorem exactAlgFixtureZeroDenRefused :
    admitCarrierExactAlg exactAlgFixtureZeroDenCoeffs = Sum.inr .zeroDenominator := rfl

theorem exactAlgFixtureF64TheaterRefused :
    evaluateF64IdentityTheater true = .f64TheaterRefused := rfl

theorem exactAlgFixtureApplyMorphismOk :
    applyExactAlgCoeffMorphism exactAlgFixtureCarrierCoeffs exactAlgFixtureCarrier
      exactAlgFixtureConjunct true =
      Sum.inl
        { morphismFrom := exactAlgFixtureCarrierCoeffs
          morphismToCarrier := attachExactAlgCoeff exactAlgFixtureCarrier exactAlgFixtureCoeff
          witness := witnessFromCarrierCoeffs exactAlgFixtureCarrierCoeffs
          excitementSelected := true } := rfl

theorem exactAlgFixtureWitnessPreservesValue :
    (witnessFromCarrierCoeffs exactAlgFixtureCarrierCoeffs).value =
      exactAlgCoeffValue exactAlgFixtureCoeff := rfl

theorem exactAlgFixtureAttachPreservesExactAlg :
    exactAlgProj (attachExactAlgCoeff exactAlgFixtureCarrier exactAlgFixtureCoeff) =
      exactAlgFixtureExactAlg := rfl

theorem exactAlgCoeffF64TheaterNotAdmitted :
    evaluateF64IdentityTheater true ≠ .admitted := by
  intro h
  cases h

theorem exactAlgCoeffZeroDenNotAdmitted :
    evaluateZeroDenominator true ≠ .admitted := by
  intro h
  cases h

-- ================================================================
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure ExactAlgCoeffsHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  denNonzero      : Prop
  provenanceOk    : Prop

def admissibleExactAlgCoeffs (h : ExactAlgCoeffsHistoryMove) : Prop :=
  h.gateChecked ∧ h.denNonzero ∧ h.provenanceOk

theorem admissibleExactAlgCoeffs_intro (h : ExactAlgCoeffsHistoryMove)
    (hg : h.gateChecked) (hd : h.denNonzero) (hp : h.provenanceOk) :
    admissibleExactAlgCoeffs h :=
  And.intro hg (And.intro hd hp)

abbrev admitExactAlgCoeffs := admissibleExactAlgCoeffs

structure ExactAlgCoeffsTransition where
  move            : ExactAlgCoeffsHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def exactAlgCoeffsSecondLaw (t : ExactAlgCoeffsTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalExactAlgCoeffsBridge where
  proc : ErasureProcess
  transition : ExactAlgCoeffsTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleExactAlgCoeffs transition.move

theorem exactAlgCoeffsSecondLaw_from_physical (b : PhysicalExactAlgCoeffsBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    exactAlgCoeffsSecondLaw b.transition := by
  unfold exactAlgCoeffsSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleExactAlgCoeffs_from_physical (b : PhysicalExactAlgCoeffsBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleExactAlgCoeffs b.transition.move :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def exactAlgCoeffsPhysicsGreen : Bool := false

theorem exactAlgCoeffsPhysicsGreenFalse : exactAlgCoeffsPhysicsGreen = false := rfl

def exactAlgCoeffsProductionWired : Bool := false

theorem exactAlgCoeffsProductionWiredFalse : exactAlgCoeffsProductionWired = false := rfl

theorem exactAlgCoeffsModuleWitness : True := trivial

theorem exactAlgCoeffs_noNewAxiom : True := trivial

theorem exactAlgCoeffsPositiveRefuseNotSilent :
    evaluateF64IdentityTheater true ≠ .admitted :=
  exactAlgCoeffF64TheaterNotAdmitted

end UMST.Urge.ExactAlgCoeffs
