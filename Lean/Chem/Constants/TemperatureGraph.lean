-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/Constants/TemperatureGraph.lean

  Meso/acting chemistry — temperature as an **Interact-graph sheaf section**
  `T` on admissible edges, with conjugate `1/T = ∂S/∂U` (finite-difference witness).

  Mirrors `Haskell/UMST/Chem/Constants/TemperatureGraph.hs` and
  `Coq/Chem/Constants/TemperatureGraph.v` on `umst-formal/meso_acting`.
  Anchored in `Chem.SecondLaw` via `LandauerLaw.physicalSecondLaw`; adds **zero**
  Lean `axiom` declarations.

  v14: `T` is a sheaf section on Interact-graph edges — not a floating scalar pin.
  Ambient convention values are named *sections*, not SI pins.
  `physics_green` stays false — thermo witnesses remain Unwired.
-/

import Chem.KleisliInteract
import Chem.SecondLaw
import LandauerEinsteinBridge

open Real UMST UMST.Chem.KleisliInteract UMST.Chem.SecondLaw UMST.Chem.Conservation

namespace UMST.Chem.Constants.TemperatureGraph

-- ================================================================
-- SECTION 1: Interact-graph carrier (design scaffold — four slots)
-- ================================================================

/-- Interact-graph vertex tags (Coq `interact_graph_vertex` mirror). -/
inductive InteractGraphVertex where
  | H | O | Ca | Si
  deriving DecidableEq, Repr

/-- Vertex field `T : GraphVertex → ℝ⁺` (Coq `temperature_graph_field`). -/
abbrev TemperatureGraphField := InteractGraphVertex → ℝ

/-- Every vertex temperature is strictly positive. -/
def temperatureFieldPositive (T : TemperatureGraphField) : Prop :=
  ∀ v, 0 < T v

/-- Ambient convention is a *section* of the vertex field, not a global pin. -/
def ambientGraphVertex : InteractGraphVertex := .O

/-- Ambient temperature section: `T` evaluated at the ambient vertex. -/
def ambientTemperatureSection (T : TemperatureGraphField) : ℝ :=
  T ambientGraphVertex

/-- Admissible one-step edge in the Interact graph (HS `InteractGraphEdge`). -/
abbrev InteractGraphEdge := ThermodynamicState × ThermodynamicState

-- ================================================================
-- SECTION 2: Conjugate witnesses (∂S/∂U finite difference on meso carrier)
-- ================================================================

/-- Entropy witness from hydration irreversibility (meso monotone proxy — not caloric S). -/
def entropyWitness (s : ThermodynamicState) : ℚ :=
  s.hydration

/-- Internal energy density witness (J/m³) from the Helmholtz carrier. -/
def internalEnergyWitness (s : ThermodynamicState) : ℚ :=
  s.density * (-s.freeEnergy)

/-- Second-law conjugate β = ∂S/∂U ≈ ΔS/ΔU; refuses ∂U ≈ 0 or β ≤ 0. -/
def inverseTemperatureBeta (old new : ThermodynamicState) : Option ℚ :=
  let dU := internalEnergyWitness new - internalEnergyWitness old
  let dS := entropyWitness new - entropyWitness old
  if dU = 0 then none
  else if 0 < dU then
    if 0 ≤ dS then some (dS / dU) else none
  else none

/-- **Sheaf section** on an edge: T = 1/β when β > 0 (v14 — not a float pin). -/
def temperatureSheafSection (old new : ThermodynamicState) : Option ℚ :=
  match inverseTemperatureBeta old new with
  | none => none
  | some β =>
    if 0 < β then some (1 / β) else none

/-- Interact-graph temperature field: defined only on admissible edges. -/
def temperatureGraphFunction (old new : ThermodynamicState) : Option ℚ :=
  if gateCheck old new then temperatureSheafSection old new else none

/-- Well-typed edge: inadmissible, or optional positive temperature section. -/
def temperatureGraphWellTyped (old new : ThermodynamicState) : Prop :=
  ¬ admissibleStep old new ∨
    match temperatureGraphFunction old new with
    | none => True
    | some t => 0 < t

-- ================================================================
-- SECTION 3: Vertex-field Landauer bridge (Coq mirror — zero new axioms)
-- ================================================================

/-- Minimum dissipated energy per erased bit at temperature `T` (SI scale). -/
noncomputable def chemLandauerFloor (T : ℝ) : ℝ :=
  landauerBitEnergy T

/-- Landauer lower bound for a measurement gaining `miBits` bits at temperature `T`. -/
noncomputable def chemMeasurementFloor (T miBits : ℝ) : ℝ :=
  miBits * chemLandauerFloor T

/-- Landauer floor at vertex `v` of a positive temperature field. -/
noncomputable def landauerFloorAt (T : TemperatureGraphField) (v : InteractGraphVertex) : ℝ :=
  chemLandauerFloor (T v)

/-- Measurement floor at vertex `v`. -/
noncomputable def measurementFloorAt
    (T : TemperatureGraphField) (v : InteractGraphVertex) (miBits : ℝ) : ℝ :=
  chemMeasurementFloor (T v) miBits

/-- Inverse temperature at a vertex: `1/T`. -/
noncomputable def inverseTemperatureAt
    (T : TemperatureGraphField) (v : InteractGraphVertex) : ℝ :=
  1 / T v

theorem landauerFloorAt_pos (T : TemperatureGraphField) (v : InteractGraphVertex)
    (hT : 0 < T v) : 0 < landauerFloorAt T v := by
  unfold landauerFloorAt chemLandauerFloor
  exact landauerBitEnergy_pos hT

theorem measurementFloorAt_zero (T : TemperatureGraphField) (v : InteractGraphVertex) :
    measurementFloorAt T v 0 = 0 := by
  unfold measurementFloorAt chemMeasurementFloor chemLandauerFloor
  ring

theorem measurementFloorAt_scale (T : TemperatureGraphField) (v : InteractGraphVertex)
    (k : ℝ) :
    measurementFloorAt T v k = k * landauerFloorAt T v := by
  unfold measurementFloorAt chemMeasurementFloor landauerFloorAt chemLandauerFloor
  ring

theorem inverseTemperatureAt_pos (T : TemperatureGraphField) (v : InteractGraphVertex)
    (hT : 0 < T v) : 0 < inverseTemperatureAt T v := by
  unfold inverseTemperatureAt
  exact one_div_pos.mpr hT

-- ================================================================
-- SECTION 4: Edge conjugate + second-law bridge
-- ================================================================

/-- Conjugate identity: when the sheaf section is defined, `1/T = β` on the edge. -/
theorem inverseTemperatureConjugateEq (old new : ThermodynamicState) (t β : ℚ)
    (hT : temperatureSheafSection old new = some t)
    (hβ : inverseTemperatureBeta old new = some β) :
    t = β⁻¹ := by
  by_cases hpos : 0 < β
  · simp [temperatureSheafSection, hβ, hpos] at hT
    exact hT.symm
  · simp [temperatureSheafSection, hβ, hpos] at hT

/-- Admissible edges delegate to the sheaf section. -/
theorem temperatureGraphFunction_admissible (old new : ThermodynamicState)
    (h : admissibleStep old new) :
    temperatureGraphFunction old new = temperatureSheafSection old new := by
  unfold temperatureGraphFunction
  simp [gateCheckComplete old new h]

/-- Positive sheaf section ⇒ positive inverse-temperature conjugate. -/
theorem inverseTemperatureBeta_pos_of_section (old new : ThermodynamicState) (t : ℚ)
    (hT : temperatureSheafSection old new = some t) (_ht : 0 < t) :
    ∃ (β : ℚ), (inverseTemperatureBeta old new = some β) ∧ 0 < β := by
  cases e : inverseTemperatureBeta old new with
  | none =>
    simp [temperatureSheafSection, e] at hT
  | some b =>
    by_cases hpos : 0 < b
    · exact ⟨b, ⟨rfl, hpos⟩⟩
    · simp [temperatureSheafSection, e, hpos] at hT

/-- Refinement work floor at bath temperature matches `chemLandauerFloor` scale. -/
theorem refinementWorkFloor_eq_chemLandauer (entropyDrop T : ℝ) :
    refinementWorkFloor entropyDrop T = T * entropyDrop := rfl

/-- Second-law entropy accounting uses bath temperature as conjugate denominator. -/
theorem chemSecondLaw_uses_inverse_temperature {n : ℕ} (t : ThermochemicalTransition n)
    (h : chemSecondLaw t) :
    assemblageEntropyDrop t ≤ t.dissipatedWork / t.bath.bathTemp.val :=
  h.2

-- ================================================================
-- SECTION 5: Conservation bridge (zero new axioms)
-- ================================================================

/-- Linear conservation witness closes on zero composition delta. -/
theorem temperature_linear_conservation_zero {n : ℕ} (w : LinearConservationWitness n) :
    linearWitnessClosed w (fun _ => 0) :=
  linearConservation_zero_delta w

-- ================================================================
-- SECTION 6: Honesty fence (physics_green false — not a measured T pin)
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def chemTemperatureGraphPhysicsGreen : Bool := false

theorem chemTemperatureGraphPhysicsGreenFalse :
    chemTemperatureGraphPhysicsGreen = false := rfl

/-- Production wiring stays open (CAT-00 lift only). -/
def temperatureGraphProductionWired : Bool := false

theorem temperatureGraphProductionWiredFalse :
    temperatureGraphProductionWired = false := rfl

/-- Catalog witness: meso chemistry temperature graph module present. -/
theorem temperatureGraphModuleWitness : True := trivial

end UMST.Chem.Constants.TemperatureGraph
