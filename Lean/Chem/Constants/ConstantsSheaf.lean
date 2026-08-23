-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/Constants/ConstantsSheaf.lean

  Meso/acting chemistry — T, P, μ as **Interact-graph sheaf sections** on admissible edges,
  with Gibbs–Duhem interdependence constraining coupled section variations.

  Mirrors `Haskell/UMST/Chem/Constants/ConstantsSheaf.hs` and
  `Coq/Chem/Constants/ConstantsSheaf.v` on `umst-formal/meso_acting`.
  Anchored in `Chem.SecondLaw` via `LandauerLaw.physicalSecondLaw`; adds **zero**
  Lean `axiom` declarations.

  v14: T, P, μ are sheaf sections on Interact-graph edges — not floating scalar pins.
  Ambient convention values are named *sections*, not SI pins.
  `physics_green` stays false — thermo witnesses remain Unwired.
-/

import Chem.Constants.TemperatureGraph
import Chem.KleisliInteract
import Chem.SecondLaw
import Chem.Conservation
import LandauerLaw

open Real UMST UMST.LandauerLaw UMST.Chem.KleisliInteract UMST.Chem.SecondLaw UMST.Chem.Conservation
open UMST.Chem.Constants.TemperatureGraph

namespace UMST.Chem.Constants.ConstantsSheaf

-- ================================================================
-- SECTION 1: Interact-graph carrier (design scaffold — four slots)
-- ================================================================

/-- Vertex field `P : GraphVertex → ℝ` (Coq `pressure_graph_field`). -/
abbrev PressureGraphField := InteractGraphVertex → ℝ

/-- Vertex field `μ : GraphVertex → ℝ` (Coq `chemical_potential_graph_field`). -/
abbrev ChemicalPotentialGraphField := InteractGraphVertex → ℝ

/-- Interdependent T, P, μ fields on the Interact graph (Coq `constants_sheaf`). -/
structure MesoConstantsSheaf where
  sheaf_temperature : TemperatureGraphField
  sheaf_pressure : PressureGraphField
  sheaf_chemical_potential : ChemicalPotentialGraphField

/-- Every vertex temperature is strictly positive. -/
def temperatureFieldPositive (T : TemperatureGraphField) : Prop :=
  ∀ v, 0 < T v

/-- Every vertex pressure is strictly positive. -/
def pressureFieldPositive (P : PressureGraphField) : Prop :=
  ∀ v, 0 < P v

/-- Coupled sections are interdependent when T and P are positive on every vertex. -/
def constantsSheafSectionsInterdependent (S : MesoConstantsSheaf) : Prop :=
  ∀ v, 0 < S.sheaf_temperature v ∧ 0 < S.sheaf_pressure v

/-- Ambient / standard convention vertices are named *sections*, not SI pins. -/
def standardPressureGraphVertex : InteractGraphVertex := .Ca

def referencePotentialGraphVertex : InteractGraphVertex := .Si

def ambientTemperatureSection (S : MesoConstantsSheaf) : ℝ :=
  S.sheaf_temperature ambientGraphVertex

def standardPressureSection (S : MesoConstantsSheaf) : ℝ :=
  S.sheaf_pressure standardPressureGraphVertex

def referenceChemicalPotentialSection (S : MesoConstantsSheaf) : ℝ :=
  S.sheaf_chemical_potential referencePotentialGraphVertex

/-- Admissible one-step edge in the Interact graph (HS `InteractGraphEdge`). -/
abbrev InteractGraphEdge := ThermodynamicState × ThermodynamicState

-- ================================================================
-- SECTION 2: Conjugate witnesses (finite difference on meso carrier)
-- ================================================================

/-- Specific volume witness (m³/kg) — mechanical conjugate carrier for P. -/
def specificVolumeWitness (s : ThermodynamicState) : ℚ :=
  1 / s.density

/-- Gibbs free energy density witness (J/m³) for μ = ∂G/∂n sections. -/
def gibbsWitness (s : ThermodynamicState) : ℚ :=
  s.density * s.freeEnergy

/-- Composition extent witness (meso hydration proxy for species amount n). -/
def compositionWitness (s : ThermodynamicState) : ℚ :=
  s.hydration

/-- Pressure section P = −∂U/∂V ≈ −ΔU/ΔV; refuses ∂V ≈ 0. -/
def pressureSheafSection (old new : ThermodynamicState) : Option ℚ :=
  let dU := internalEnergyWitness new - internalEnergyWitness old
  let dV := specificVolumeWitness new - specificVolumeWitness old
  if dV = 0 then none else some (-(dU / dV))

/-- Chemical potential section μ = ∂G/∂n ≈ ΔG/Δn; refuses ∂n ≈ 0. -/
def chemicalPotentialSheafSection (old new : ThermodynamicState) : Option ℚ :=
  let dG := gibbsWitness new - gibbsWitness old
  let dn := compositionWitness new - compositionWitness old
  if dn = 0 then none else some (dG / dn)

/-- Temperature section on an edge: alias of the temperature sheaf section. -/
abbrev temperatureSectionOnEdge := temperatureSheafSection

/-- Coupled T, P, μ sheaf sections on an admissible Interact-graph edge. -/
def constantsSheafOnEdge (old new : ThermodynamicState) : Option (ℚ × ℚ × ℚ) :=
  if gateCheck old new then
    match temperatureSheafSection old new with
    | none => none
    | some t =>
      match pressureSheafSection old new with
      | none => none
      | some p =>
        match chemicalPotentialSheafSection old new with
        | none => none
        | some mu => some (t, p, mu)
  else none

/-- Well-typed edge: inadmissible, or optional positive T and finite P, μ. -/
def constantsSheafWellTyped (old new : ThermodynamicState) : Prop :=
  gateCheck old new = false ∨
    match constantsSheafOnEdge old new with
    | none => True
    | some (t, _, _) => 0 < t

/-- Gibbs–Duhem balance on scalar variations (Coq `gibbs_duhem_balance`). -/
def gibbsDuhemBalance
    (entropy volume deltaTemperature deltaPressure deltaMu : ℚ) : Prop :=
  deltaMu = (-entropy) * deltaTemperature + volume * deltaPressure

/-- Gibbs–Duhem finite-difference: ΔG ≈ P ΔV + μ Δn − T ΔS on coupled sections. -/
def gibbsDuhemInterdependenceEq (old new : ThermodynamicState) : Prop :=
  match constantsSheafOnEdge old new with
  | none => True
  | some (t, p, mu) =>
    let dG := gibbsWitness new - gibbsWitness old
    let dV := specificVolumeWitness new - specificVolumeWitness old
    let dN := compositionWitness new - compositionWitness old
    let dS := entropyWitness new - entropyWitness old
    dG = p * dV + mu * dN - t * dS

-- ================================================================
-- SECTION 3: Gibbs–Duhem composition interdependence (Coq dot_list mirror)
-- ================================================================

/-- Dot product of two rational lists (Coq `dot_list`). -/
def dotList (xs ys : List ℚ) : ℚ :=
  match xs, ys with
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs', y :: ys' => x * y + dotList xs' ys'

/-- At constant T,P: ∑ xᵢ dμᵢ = 0 on normalized composition fractions. -/
def gibbsDuhemInterdependence (fractions variations : List ℚ) : Prop :=
  dotList fractions variations = 0

theorem dotList_zero_map (xs : List ℚ) :
    dotList xs (List.map (fun _ => (0 : ℚ)) xs) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    simp only [dotList, List.map]
    rw [ih]
    ring

theorem gibbsDuhemInterdependence_zero (fractions : List ℚ) :
    gibbsDuhemInterdependence fractions (List.map (fun _ => (0 : ℚ)) fractions) := by
  unfold gibbsDuhemInterdependence
  exact dotList_zero_map fractions

-- ================================================================
-- SECTION 4: Vertex-field Landauer bridge (Coq mirror — zero new axioms)
-- ================================================================

noncomputable def landauerFloorAtSheaf (S : MesoConstantsSheaf) (v : InteractGraphVertex) : ℝ :=
  landauerFloorAt S.sheaf_temperature v

noncomputable def measurementFloorAtSheaf
    (S : MesoConstantsSheaf) (v : InteractGraphVertex) (miBits : ℝ) : ℝ :=
  measurementFloorAt S.sheaf_temperature v miBits

theorem landauerFloorAtSheaf_pos (S : MesoConstantsSheaf) (v : InteractGraphVertex)
    (hT : 0 < S.sheaf_temperature v) : 0 < landauerFloorAtSheaf S v := by
  unfold landauerFloorAtSheaf
  exact landauerFloorAt_pos S.sheaf_temperature v hT

theorem measurementFloorAtSheaf_zero (S : MesoConstantsSheaf) (v : InteractGraphVertex) :
    measurementFloorAtSheaf S v 0 = 0 := by
  unfold measurementFloorAtSheaf
  exact measurementFloorAt_zero S.sheaf_temperature v

theorem measurementFloorAtSheaf_scale (S : MesoConstantsSheaf) (v : InteractGraphVertex)
    (k : ℝ) :
    measurementFloorAtSheaf S v k = k * landauerFloorAtSheaf S v := by
  unfold measurementFloorAtSheaf landauerFloorAtSheaf
  exact measurementFloorAt_scale S.sheaf_temperature v k

-- ================================================================
-- SECTION 5: Edge conjugate + physicalSecondLaw bridge
-- ================================================================

theorem gibbsDuhemInterdependenceEq_ungated (old new : ThermodynamicState)
    (h : gateCheck old new = false) :
    gibbsDuhemInterdependenceEq old new := by
  unfold gibbsDuhemInterdependenceEq constantsSheafOnEdge
  simp [h]

theorem constantsSheafOnEdge_admissible (old new : ThermodynamicState)
    (h : admissibleStep old new) :
    constantsSheafOnEdge old new =
      (if gateCheck old new then
        match temperatureSheafSection old new with
        | none => none
        | some t =>
          match pressureSheafSection old new with
          | none => none
          | some p =>
            match chemicalPotentialSheafSection old new with
            | none => none
            | some mu => some (t, p, mu)
      else none) := by
  unfold constantsSheafOnEdge
  simp [gateCheckComplete old new h]

theorem chemSecondLaw_uses_sheaf_temperature {n : ℕ} (t : ThermochemicalTransition n)
    (h : chemSecondLaw t) :
    assemblageEntropyDrop t ≤ t.dissipatedWork / t.bath.bathTemp.val :=
  h.2

theorem constantsSheaf_chemSecondLaw_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    chemSecondLaw b.transition :=
  chemSecondLaw_from_physical b hSL

theorem physicalSecondLaw_discharges_constantsSheaf_entropy (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    assemblageEntropyDrop b.transition ≤
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val :=
  chem_entropy_bound_from_physical b hSL

theorem constantsSheaf_refinementLandauer (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    b.transition.dissipatedWork ≥
      b.transition.bath.bathTemp.val * log 2 :=
  refinementLandauerBound b hSL

-- ================================================================
-- SECTION 6: Conservation bridge (zero new axioms)
-- ================================================================

theorem constantsSheaf_linear_conservation_zero {n : ℕ} (w : LinearConservationWitness n) :
    linearWitnessClosed w (fun _ => 0) :=
  linearConservation_zero_delta w

theorem constantsSheaf_admissibleConserved_from_physical (b : PhysicalChemBridge)
    (w : LinearConservationWitness 2)
    (hDelta : conservedCompositionDelta ⟨b.transition, fun _ => 0, fun _ => 0⟩ = fun _ => 0)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleConservedTransition w ⟨b.transition, fun _ => 0, fun _ => 0⟩ :=
  interact_admissibleConserved_from_physical b w hDelta hSL

-- ================================================================
-- SECTION 7: Honesty fence (physics_green false — not measured pins)
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def chemConstantsSheafPhysicsGreen : Bool := false

theorem chemConstantsSheafPhysicsGreenFalse :
    chemConstantsSheafPhysicsGreen = false := rfl

/-- Production wiring stays open (CAT-00 lift only). -/
def constantsSheafProductionWired : Bool := false

theorem constantsSheafProductionWiredFalse :
    constantsSheafProductionWired = false := rfl

/-- Catalog witness: meso chemistry constants sheaf module present. -/
theorem constantsSheafModuleWitness : True := trivial

end UMST.Chem.Constants.ConstantsSheaf
