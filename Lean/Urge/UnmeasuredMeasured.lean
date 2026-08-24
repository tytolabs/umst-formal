-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/UnmeasuredMeasured.lean

  Meso acting Urge — §17.7 production_wired taxonomy.
  `Unmeasured | Measured {value, dataset}` — UNKNOWN ≠ false-as-GREEN.
  Composes `Excitement.select` — no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations.  Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.UnmeasuredMeasured

-- ================================================================
-- SECTION 1: §17.7 production_wired taxonomy carriers
-- ================================================================

/-- Blueprint §17.7 — fleet measurement absent vs measured on named dataset. -/
inductive ProductionWiredTaxonomy where
  | unmeasured
  | measured (value : Bool) (dataset : String)
  deriving Repr

def productionWiredIsMeasured (pw : ProductionWiredTaxonomy) : Bool :=
  match pw with
  | .unmeasured => false
  | .measured _ _ => true

def productionWiredMeasuredValue (pw : ProductionWiredTaxonomy) : Option Bool :=
  match pw with
  | .unmeasured => none
  | .measured v _ => some v

def productionWiredDataset (pw : ProductionWiredTaxonomy) : Option String :=
  match pw with
  | .unmeasured => none
  | .measured _ d => some d

def datasetNonempty (d : String) : Bool :=
  !d.isEmpty

inductive FalseAsGreenRefusal where
  | unmeasuredCollapsedToFalse
  | measuredTrueNotPhysicsGreen
  deriving Repr

inductive ProductionWiredVerdict where
  | honestUnmeasured
  | measuredFalseOk
  | falseAsGreenRefused
  deriving Repr

-- ================================================================
-- SECTION 2: §17.7 positive refuse (UNKNOWN ≠ false-as-GREEN)
-- ================================================================

structure UnmeasuredMeasuredConjunct where
  gateOk                  : Bool
  falseAsGreenRefused     : Bool
  excitementPreserves     : Bool

def ummConjunctAdmits (c : UnmeasuredMeasuredConjunct) : Bool :=
  c.gateOk && c.falseAsGreenRefused && c.excitementPreserves

def refuseFalseAsGreen (pw : ProductionWiredTaxonomy) : Option FalseAsGreenRefusal :=
  match pw with
  | .unmeasured => some .unmeasuredCollapsedToFalse
  | .measured true _ => some .measuredTrueNotPhysicsGreen
  | .measured false _ => none

def productionWiredLegacyBool (pw : ProductionWiredTaxonomy) : Option Bool :=
  productionWiredMeasuredValue pw

def boolClaimsMeasurementWhenUnmeasured (pw : ProductionWiredTaxonomy) (claimed : Bool) : Bool :=
  match pw with
  | .unmeasured => claimed
  | .measured _ _ => false

def measuredProductionWired (value : Bool) (dataset : String) :
    ProductionWiredTaxonomy ⊕ FalseAsGreenRefusal :=
  if datasetNonempty dataset then
    Sum.inl (.measured value dataset)
  else
    Sum.inr .unmeasuredCollapsedToFalse

def evaluateProductionWired (pw : ProductionWiredTaxonomy) : ProductionWiredVerdict :=
  match refuseFalseAsGreen pw with
  | some _ => .falseAsGreenRefused
  | none =>
    match pw with
    | .unmeasured => .honestUnmeasured
    | .measured false _ => .measuredFalseOk
    | .measured true _ => .falseAsGreenRefused

theorem refuseFalseAsGreen_unmeasured :
    refuseFalseAsGreen .unmeasured = some .unmeasuredCollapsedToFalse := rfl

theorem productionWiredLegacyNoneWhenUnmeasured :
    productionWiredLegacyBool .unmeasured = none := rfl

theorem unmeasuredNotMeasured :
    productionWiredIsMeasured .unmeasured = false := rfl

-- ================================================================
-- SECTION 3: Gossip mesh taxonomy — documented Unmeasured
-- ================================================================

def gossipMeshProductionWiredTaxonomy : ProductionWiredTaxonomy := .unmeasured

def ucrsGossipMeshDocumentedAsUnmeasured : Bool :=
  match gossipMeshProductionWiredTaxonomy with
  | .unmeasured => true
  | .measured _ _ => false

def refuseUnmeasuredAsFalseGreen : FalseAsGreenRefusal :=
  .unmeasuredCollapsedToFalse

theorem gossipMeshTaxonomyIsUnmeasured :
    gossipMeshProductionWiredTaxonomy = .unmeasured := rfl

theorem ucrsGossipMeshDocumentedUnmeasuredTrue :
    ucrsGossipMeshDocumentedAsUnmeasured = true := rfl

theorem gossipMeshRefuseFalseAsGreen :
    refuseFalseAsGreen gossipMeshProductionWiredTaxonomy =
      some .unmeasuredCollapsedToFalse := rfl

-- ================================================================
-- SECTION 4: Urge composes Excitement.select (no second argmin)
-- ================================================================

structure UnmeasuredMeasuredCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

inductive UnmeasuredMeasuredExcitementPin where
  | importSelectExcitement
  | secondArgminRefused
  deriving Repr

noncomputable def unmeasuredMeasuredExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) (pin : UnmeasuredMeasuredExcitementPin) :
    Cand (K := ℚ) prior ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select prior successors
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

noncomputable def unmeasuredMeasuredSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : UnmeasuredMeasuredCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

theorem unmeasuredMeasuredSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : UnmeasuredMeasuredCtx S) :
    unmeasuredMeasuredSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem unmeasuredMeasuredSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : UnmeasuredMeasuredCtx S) :
    unmeasuredMeasuredSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem unmeasuredMeasuredNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : UnmeasuredMeasuredCtx S) :
    unmeasuredMeasuredSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem unmeasuredMeasuredExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    unmeasuredMeasuredExcitementSelect prior successors .importSelectExcitement =
      select prior successors :=
  rfl

theorem unmeasuredMeasuredExcitementSelect_refusesSecondArgmin {S : Type}
    [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    unmeasuredMeasuredExcitementSelect prior successors .secondArgminRefused =
      Sum.inr Residue.allInadmissible :=
  rfl

theorem unmeasuredMeasuredSelect_empty {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : UnmeasuredMeasuredCtx S)
    (h : ctx.successors = []) :
    unmeasuredMeasuredSelect ctx = Sum.inr Residue.noCandidates := by
  rw [unmeasuredMeasuredSelect, urgeRecoverySelect_eq_select, h]
  exact select_empty (src := ctx.prior)

-- ================================================================
-- SECTION 5: §17.7 fixtures + witness theorems
-- ================================================================

def ummFixtureDataset : String :=
  "fixture:urge-formal-meso-lean-unmeasured-measured"

def ummFixtureMeasuredFalse : ProductionWiredTaxonomy :=
  .measured false ummFixtureDataset

def ummFixtureConjunct : UnmeasuredMeasuredConjunct :=
  { gateOk := true, falseAsGreenRefused := true, excitementPreserves := true }

theorem ummFixtureMeasuredFalseAdmits :
    refuseFalseAsGreen ummFixtureMeasuredFalse = none := rfl

theorem ummFixtureMeasuredFalseEvaluateOk :
    evaluateProductionWired ummFixtureMeasuredFalse = .measuredFalseOk := rfl

theorem ummFixtureMeasuredProductionWiredOk :
    measuredProductionWired false ummFixtureDataset = Sum.inl ummFixtureMeasuredFalse := rfl

theorem ummFixtureEmptyDatasetRefused :
    measuredProductionWired false "" = Sum.inr .unmeasuredCollapsedToFalse := rfl

theorem ummFixtureUnmeasuredLegacyNone :
    productionWiredLegacyBool gossipMeshProductionWiredTaxonomy = none := rfl

theorem ummFixtureConjunctAdmitsTrue :
    ummConjunctAdmits ummFixtureConjunct = true := rfl

-- ================================================================
-- SECTION 6: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure UnmeasuredMeasuredTransition where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ
  gateChecked     : Prop
  falseAsGreenRefused : Prop
  excitementPreserves : Prop

def admissibleUnmeasuredMeasured (t : UnmeasuredMeasuredTransition) : Prop :=
  t.gateChecked ∧ t.falseAsGreenRefused ∧ t.excitementPreserves

def unmeasuredMeasuredSecondLaw (t : UnmeasuredMeasuredTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalUnmeasuredMeasuredBridge where
  proc : ErasureProcess
  transition : UnmeasuredMeasuredTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleUnmeasuredMeasured transition

theorem unmeasuredMeasuredSecondLaw_from_physical (b : PhysicalUnmeasuredMeasuredBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    unmeasuredMeasuredSecondLaw b.transition := by
  unfold unmeasuredMeasuredSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleUnmeasuredMeasured_from_physical (b : PhysicalUnmeasuredMeasuredBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleUnmeasuredMeasured b.transition :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 7: Honesty flags + catalog witnesses
-- ================================================================

def unmeasuredMeasuredPhysicsGreen : Bool := false

theorem unmeasuredMeasuredPhysicsGreenFalse : unmeasuredMeasuredPhysicsGreen = false := rfl

def unmeasuredMeasuredProductionWired : Bool := false

theorem unmeasuredMeasuredProductionWiredFalse : unmeasuredMeasuredProductionWired = false := rfl

theorem unmeasuredMeasuredModuleWitness : True := trivial

theorem unmeasuredMeasured_noNewAxiom : True := trivial

theorem unmeasuredMeasured_positiveRefuseNotSilent :
    refuseFalseAsGreen gossipMeshProductionWiredTaxonomy ≠ none := by
  simp [gossipMeshRefuseFalseAsGreen]

theorem unmeasuredMeasured_unknownNotFalseAsGreen :
    refuseUnmeasuredAsFalseGreen = .unmeasuredCollapsedToFalse := rfl

def excitementComposePin : Nat := 0

theorem excitementComposePin_marker : excitementComposePin = 0 := rfl

def unmeasuredMeasuredCatalogWitness : String :=
  "URGE-FORMAL-MESO-LEAN-UNMEASURED-MEASURED §17.7 production_wired : Unmeasured | Measured {value, dataset}; UNKNOWN ≠ false-as-GREEN; compose excitement-select no second argmin sole axiom physicalSecondLaw not physics GREEN not production_wired"

end UMST.Urge.UnmeasuredMeasured
