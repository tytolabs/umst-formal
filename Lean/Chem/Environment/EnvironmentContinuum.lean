-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/Environment/EnvironmentContinuum.lean

  Meso/acting environment continuum — vacuum / contained / messy as **named Interact-graph
  Env sheaf sections**, not XOR sample-space pins.  Env sheaf anchored in
  `LandauerLaw.physicalSecondLaw` via `Chem.SecondLaw`.

  Mirrors `Haskell/UMST/Chem/Environment/EnvironmentContinuum.hs` and
  `Coq/Chem/Environment/EnvironmentContinuum.v` on `umst-formal/meso_acting`.
  Adds **zero** Lean `axiom` declarations.

  v15: Env sheaf from physicalSecondLaw; vacuum/contained/messy are named sections, not XOR.
  `physics_green` stays false — thermo witnesses remain Unwired.
-/

import Chem.Constants.TemperatureGraph
import Chem.KleisliInteract
import Chem.SecondLaw
import Chem.Conservation
import LandauerLaw

open Real UMST UMST.LandauerLaw UMST.Chem.KleisliInteract UMST.Chem.SecondLaw
open UMST.Chem.Conservation UMST.Chem.Constants.TemperatureGraph

namespace UMST.Chem.Environment.EnvironmentContinuum

-- ================================================================
-- SECTION 1: Interact-graph carrier (design scaffold — four slots)
-- ================================================================

/-- Vertex field `S : GraphVertex → ℝ` (Coq `sample_scale_graph_field`). -/
abbrev SampleScaleGraphField := InteractGraphVertex → ℝ

/-- Vertex field `T : GraphVertex → ℝ` (Coq `thermo_continuum_graph_field`). -/
abbrev ThermoContinuumGraphField := InteractGraphVertex → ℝ

/-- Vertex field coupling neighbors (Coq `neighbor_coupling_graph_field`). -/
abbrev NeighborCouplingGraphField := InteractGraphVertex → ℝ

/-- Interdependent sample scale, thermo continuum, neighbor coupling on the Interact graph
    (Coq `environment_sheaf`). -/
structure MesoEnvironmentSheaf where
  sheaf_sample_scale : SampleScaleGraphField
  sheaf_thermo_continuum : ThermoContinuumGraphField
  sheaf_neighbor_coupling : NeighborCouplingGraphField

/-- Every vertex thermo continuum is strictly positive. -/
def thermoContinuumFieldPositive (T : ThermoContinuumGraphField) : Prop :=
  ∀ v, 0 < T v

/-- Every vertex sample scale is strictly positive. -/
def sampleScaleFieldPositive (S : SampleScaleGraphField) : Prop :=
  ∀ v, 0 < S v

/-- Named sample-space vertices (vacuum / contained / messy — not XOR). -/
def vacuumGraphVertex : InteractGraphVertex := .H

def containedGraphVertex : InteractGraphVertex := .O

def messyGraphVertex : InteractGraphVertex := .Ca

def vacuumSampleSection (E : MesoEnvironmentSheaf) : ℝ :=
  E.sheaf_sample_scale vacuumGraphVertex

def containedSampleSection (E : MesoEnvironmentSheaf) : ℝ :=
  E.sheaf_sample_scale containedGraphVertex

def messySampleSection (E : MesoEnvironmentSheaf) : ℝ :=
  E.sheaf_sample_scale messyGraphVertex

def vacuumThermoContinuumSection (E : MesoEnvironmentSheaf) : ℝ :=
  E.sheaf_thermo_continuum vacuumGraphVertex

def containedThermoContinuumSection (E : MesoEnvironmentSheaf) : ℝ :=
  E.sheaf_thermo_continuum containedGraphVertex

def messyThermoContinuumSection (E : MesoEnvironmentSheaf) : ℝ :=
  E.sheaf_thermo_continuum messyGraphVertex

/-- Admissible one-step edge in the Interact graph (HS `InteractGraphEdge`). -/
abbrev InteractGraphEdge := ThermodynamicState × ThermodynamicState

theorem vacuumContainedVerticesDistinct :
    vacuumGraphVertex ≠ containedGraphVertex := by decide

theorem vacuumMessyVerticesDistinct :
    vacuumGraphVertex ≠ messyGraphVertex := by decide

theorem containedMessyVerticesDistinct :
    containedGraphVertex ≠ messyGraphVertex := by decide

/-- Named sections are distinct vertices — not XOR regime selection. -/
def envSampleSectionsNotXor : Prop :=
  vacuumGraphVertex ≠ containedGraphVertex ∧
  vacuumGraphVertex ≠ messyGraphVertex ∧
  containedGraphVertex ≠ messyGraphVertex

theorem envSampleSectionsNotXorHolds : envSampleSectionsNotXor :=
  ⟨vacuumContainedVerticesDistinct, vacuumMessyVerticesDistinct, containedMessyVerticesDistinct⟩

/-- Vacuum does not close messy: witness sheaf with distinct sample sections. -/
def vacuumDoesNotCloseMessy : Prop :=
  ∃ E : MesoEnvironmentSheaf, vacuumSampleSection E ≠ messySampleSection E

noncomputable def witnessEnvironmentSheaf : MesoEnvironmentSheaf where
  sheaf_sample_scale := fun v =>
    match v with
    | .H => 1
    | .O => 2
    | .Ca => 3
    | .Si => 4
  sheaf_thermo_continuum := fun _ => 1
  sheaf_neighbor_coupling := fun _ => 0

theorem vacuumDoesNotCloseMessyHolds : vacuumDoesNotCloseMessy :=
  ⟨witnessEnvironmentSheaf, by simp [vacuumSampleSection, messySampleSection,
    vacuumGraphVertex, messyGraphVertex, witnessEnvironmentSheaf]⟩

-- ================================================================
-- SECTION 2: Conjugate witnesses (finite difference on meso carrier)
-- ================================================================

/-- Gate dissipation witness (J/m³) from contained Interact admissibility. -/
def gateDissipationWitness (old new : ThermodynamicState) : ℚ :=
  old.freeEnergy - new.freeEnergy

/-- Hydration irreversibility witness for messy Ore/Refine neighbor coupling. -/
def hydrationIrreversibilityWitness (s : ThermodynamicState) : ℚ :=
  s.hydration

/-- Vacuum section: second-law entropy production ΔS at monoidal unit (no neighbor channel). -/
def vacuumSectionOnEdge (old new : ThermodynamicState) : Option ℚ :=
  if gateCheck old new then
    let dS := entropyWitness new - entropyWitness old
    if 0 ≤ dS then some dS else none
  else none

/-- Contained section: gate dissipation on Kleisli Interact walls. -/
def containedSectionOnEdge (old new : ThermodynamicState) : Option ℚ :=
  if gateCheck old new then
    let diss := gateDissipationWitness old new
    if 0 ≤ diss then some diss else none
  else none

/-- Messy section: hydration irreversibility Δn proxy for Ore/Refine neighbor impact. -/
def messySectionOnEdge (old new : ThermodynamicState) : Option ℚ :=
  if gateCheck old new then
    let dH := hydrationIrreversibilityWitness new - hydrationIrreversibilityWitness old
    if 0 ≤ dH then some dH else none
  else none

/-- Coupled vacuum, contained, messy sections on an admissible Interact-graph edge. -/
def environmentSheafOnEdge (old new : ThermodynamicState) : Option (ℚ × ℚ × ℚ) :=
  if gateCheck old new then
    match vacuumSectionOnEdge old new with
    | none => none
    | some v =>
      match containedSectionOnEdge old new with
      | none => none
      | some c =>
        match messySectionOnEdge old new with
        | none => none
        | some m => some (v, c, m)
  else none

/-- Well-typed edge: inadmissible, or optional non-negative named sections. -/
def environmentContinuumWellTyped (old new : ThermodynamicState) : Prop :=
  gateCheck old new = false ∨
    match environmentSheafOnEdge old new with
    | none => True
    | some (v, c, m) => 0 ≤ v ∧ 0 ≤ c ∧ 0 ≤ m

/-- Second-law coherence: contained dissipation matches gate witness on coupled sections. -/
def environmentContinuumSecondLawEq (old new : ThermodynamicState) : Prop :=
  match environmentSheafOnEdge old new with
  | none => True
  | some (_, c, _) => c = gateDissipationWitness old new

/-- Cardinality of named environment sections (not XOR — all three named). -/
def environmentRegimeCardinality : ℕ := 3

theorem environmentSectionsNamedNotXor :
    environmentRegimeCardinality = 3 := rfl

-- ================================================================
-- SECTION 3: Composition interdependence (Coq dot_list mirror)
-- ================================================================

/-- Dot product of two rational lists (Coq `dot_list`). -/
def dotList (xs ys : List ℚ) : ℚ :=
  match xs, ys with
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs', y :: ys' => x * y + dotList xs' ys'

/-- At constant sample scale: ∑ xᵢ dSᵢ = 0 on normalized composition fractions. -/
def envCompositionInterdependence (fractions sampleVariations : List ℚ) : Prop :=
  dotList fractions sampleVariations = 0

theorem dotList_zero_map (xs : List ℚ) :
    dotList xs (List.map (fun _ => (0 : ℚ)) xs) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    simp only [dotList, List.map]
    rw [ih]
    ring

theorem envCompositionZeroVariation (fractions : List ℚ) :
    envCompositionInterdependence fractions (List.map (fun _ => (0 : ℚ)) fractions) := by
  unfold envCompositionInterdependence
  exact dotList_zero_map fractions

-- ================================================================
-- SECTION 4: Vertex-field Landauer bridge (Coq mirror — zero new axioms)
-- ================================================================

noncomputable def landauerFloorAtEnvSheaf
    (E : MesoEnvironmentSheaf) (v : InteractGraphVertex) : ℝ :=
  chemLandauerFloor (E.sheaf_thermo_continuum v)

noncomputable def measurementFloorAtEnvSheaf
    (E : MesoEnvironmentSheaf) (v : InteractGraphVertex) (miBits : ℝ) : ℝ :=
  chemMeasurementFloor (E.sheaf_thermo_continuum v) miBits

theorem landauerFloorAtEnvSheaf_pos (E : MesoEnvironmentSheaf) (v : InteractGraphVertex)
    (hT : 0 < E.sheaf_thermo_continuum v) : 0 < landauerFloorAtEnvSheaf E v := by
  unfold landauerFloorAtEnvSheaf chemLandauerFloor
  exact landauerBitEnergy_pos hT

theorem measurementFloorAtEnvSheaf_zero (E : MesoEnvironmentSheaf) (v : InteractGraphVertex) :
    measurementFloorAtEnvSheaf E v 0 = 0 := by
  unfold measurementFloorAtEnvSheaf chemMeasurementFloor chemLandauerFloor
  ring

theorem measurementFloorAtEnvSheaf_scale (E : MesoEnvironmentSheaf) (v : InteractGraphVertex)
    (k : ℝ) :
    measurementFloorAtEnvSheaf E v k = k * landauerFloorAtEnvSheaf E v := by
  unfold measurementFloorAtEnvSheaf landauerFloorAtEnvSheaf chemMeasurementFloor chemLandauerFloor
  ring

-- ================================================================
-- SECTION 5: Edge conjugate + physicalSecondLaw bridge
-- ================================================================

theorem environmentSheafOnEdge_ungated (old new : ThermodynamicState)
    (h : gateCheck old new = false) :
    environmentSheafOnEdge old new = none := by
  unfold environmentSheafOnEdge
  simp [h]

theorem environmentSheafOnEdge_admissible (old new : ThermodynamicState)
    (h : admissibleStep old new) :
    environmentSheafOnEdge old new =
      (if gateCheck old new then
        match vacuumSectionOnEdge old new with
        | none => none
        | some v =>
          match containedSectionOnEdge old new with
          | none => none
          | some c =>
            match messySectionOnEdge old new with
            | none => none
            | some m => some (v, c, m)
      else none) := by
  unfold environmentSheafOnEdge
  simp [gateCheckComplete old new h]

theorem environmentContinuumSecondLawEq_ungated (old new : ThermodynamicState)
    (h : gateCheck old new = false) :
    environmentContinuumSecondLawEq old new := by
  unfold environmentContinuumSecondLawEq environmentSheafOnEdge
  simp [h]

theorem environmentContinuum_chemSecondLaw_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    chemSecondLaw b.transition :=
  chemSecondLaw_from_physical b hSL

theorem physicalSecondLaw_discharges_environment_entropy (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    assemblageEntropyDrop b.transition ≤
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val :=
  chem_entropy_bound_from_physical b hSL

theorem environmentContinuum_refinementLandauer (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    b.transition.dissipatedWork ≥
      b.transition.bath.bathTemp.val * log 2 :=
  refinementLandauerBound b hSL

-- ================================================================
-- SECTION 6: Conservation bridge (zero new axioms)
-- ================================================================

theorem environmentContinuum_linear_conservation_zero {n : ℕ} (w : LinearConservationWitness n) :
    linearWitnessClosed w (fun _ => 0) :=
  linearConservation_zero_delta w

theorem environmentContinuum_admissibleConserved_from_physical (b : PhysicalChemBridge)
    (w : LinearConservationWitness 2)
    (hDelta : conservedCompositionDelta ⟨b.transition, fun _ => 0, fun _ => 0⟩ = fun _ => 0)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleConservedTransition w ⟨b.transition, fun _ => 0, fun _ => 0⟩ :=
  interact_admissibleConserved_from_physical b w hDelta hSL

-- ================================================================
-- SECTION 7: Honesty fence (physics_green false — not measured env pins)
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def chemEnvironmentContinuumPhysicsGreen : Bool := false

theorem chemEnvironmentContinuumPhysicsGreenFalse :
    chemEnvironmentContinuumPhysicsGreen = false := rfl

/-- Production wiring stays open (CAT-00 lift only). -/
def environmentContinuumProductionWired : Bool := false

theorem environmentContinuumProductionWiredFalse :
    environmentContinuumProductionWired = false := rfl

/-- Catalog witness: meso chemistry environment continuum module present. -/
theorem environmentContinuumModuleWitness : True := trivial

end UMST.Chem.Environment.EnvironmentContinuum
