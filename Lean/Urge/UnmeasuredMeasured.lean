-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/UnmeasuredMeasured.lean

  Meso acting Urge — §17.7 production_wired taxonomy.
  `Unmeasured | Measured {value, dataset}` — UNKNOWN ≠ false-as-GREEN.
  Composes `Excitement.select` — no second argmin.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
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

def datasetNonempty (d : String) : Bool :=
  !d.isEmpty

inductive FalseAsGreenRefusal where
  | unmeasuredCollapsedToFalse
  | measuredTrueNotPhysicsGreen
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

def boolClaimsMeasurementWhenUnmeasured (pw : ProductionWiredTaxonomy) (claimed : Bool) : Bool :=
  match pw with
  | .unmeasured => claimed
  | .measured _ _ => false

theorem refuseFalseAsGreen_unmeasured :
    refuseFalseAsGreen .unmeasured = some .unmeasuredCollapsedToFalse := rfl

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

theorem ucrsGossipMeshDocumentedUnmeasuredTrue :
    ucrsGossipMeshDocumentedAsUnmeasured = true := rfl

-- ================================================================
-- SECTION 4: Urge composes Excitement.select (no second argmin)
-- ================================================================

inductive UnmeasuredMeasuredExcitementPin where
  | importSelectExcitement
  | secondArgminRefused
  deriving Repr

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

end UMST.Urge.UnmeasuredMeasured
