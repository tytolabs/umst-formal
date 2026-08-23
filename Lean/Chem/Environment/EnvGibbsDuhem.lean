-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/Environment/EnvGibbsDuhem.lean

  Meso/acting chemistry — Env coordinates (T, P, μ, …) covary on the Env sheaf
  (Gibbs–Duhem / Maxwell / Debye), not independent floats. Gibbs–Duhem probe on
  `EnvironmentContinuum` + `EnvSampleSections`, reusing `ConstantsSheaf` interdependence.

  Mirrors `Coq/Chem/Environment/EnvGibbsDuhem.v` on `umst-formal/meso_acting`.
  Imports `EnvironmentContinuum`, `EnvSampleSections`, `ConstantsSheaf`; adds **zero**
  Lean `axiom` declarations.

  v15: Env coordinates covary via sheaf interdependence — not independent float pins.
  `physics_green` stays false — thermo witnesses remain Unwired.
-/

import Chem.Environment.EnvironmentContinuum
import Chem.Environment.EnvSampleSections
import Chem.Constants.ConstantsSheaf

open Real UMST UMST.Chem.KleisliInteract
open UMST.Chem.Environment.EnvironmentContinuum
open UMST.Chem.Environment.EnvSampleSections
open UMST.Chem.Constants.TemperatureGraph

namespace UMST.Chem.Environment.EnvGibbsDuhem

-- ================================================================
-- SECTION 1: Gibbs–Duhem legs (T, P, μ — not independent float pins)
-- ================================================================

/-- Named Gibbs–Duhem coordinate legs on the Env sheaf. -/
inductive EnvGibbsDuhemLeg where
  | Temperature
  | Pressure
  | ChemicalPotential

def envGibbsDuhemLegTags : List EnvGibbsDuhemLeg :=
  [EnvGibbsDuhemLeg.Temperature,
   EnvGibbsDuhemLeg.Pressure,
   EnvGibbsDuhemLeg.ChemicalPotential]

def envGibbsDuhemLegCardinality : ℕ := 3

theorem envGibbsDuhemLegTemperaturePressureDistinct :
    EnvGibbsDuhemLeg.Temperature ≠ EnvGibbsDuhemLeg.Pressure := by
  rintro h; cases h

theorem envGibbsDuhemLegTemperatureMuDistinct :
    EnvGibbsDuhemLeg.Temperature ≠ EnvGibbsDuhemLeg.ChemicalPotential := by
  rintro h; cases h

theorem envGibbsDuhemLegPressureMuDistinct :
    EnvGibbsDuhemLeg.Pressure ≠ EnvGibbsDuhemLeg.ChemicalPotential := by
  rintro h; cases h

-- ================================================================
-- SECTION 2: Debye square legs (T, I, ε_r → κ⁻¹ — not magic prefactor)
-- ================================================================

/-- Debye-square coordinate legs (temperature, ionic strength, permittivity). -/
inductive EnvDebyeSquareLeg where
  | DebyeTemperature
  | DebyeIonicStrength
  | DebyePermittivity

def envDebyeSquareLegTags : List EnvDebyeSquareLeg :=
  [EnvDebyeSquareLeg.DebyeTemperature,
   EnvDebyeSquareLeg.DebyeIonicStrength,
   EnvDebyeSquareLeg.DebyePermittivity]

def envDebyeSquareLegCardinality : ℕ := 3

theorem envDebyeLegTemperatureIonicDistinct :
    EnvDebyeSquareLeg.DebyeTemperature ≠ EnvDebyeSquareLeg.DebyeIonicStrength := by
  rintro h; cases h

theorem envDebyeLegTemperaturePermittivityDistinct :
    EnvDebyeSquareLeg.DebyeTemperature ≠ EnvDebyeSquareLeg.DebyePermittivity := by
  rintro h; cases h

theorem envDebyeLegIonicPermittivityDistinct :
    EnvDebyeSquareLeg.DebyeIonicStrength ≠ EnvDebyeSquareLeg.DebyePermittivity := by
  rintro h; cases h

-- ================================================================
-- SECTION 3: Maxwell commute scaffold (mixed partials of G(T,P,n) — not pins)
-- ================================================================

/-- Maxwell relation scaffold: (∂S/∂P)_T = (∂V/∂T)_P on coupled Env sections. -/
def envMaxwellCommuteBalance (partialSAtConstantP partialVAtConstantT : ℝ) : Prop :=
  partialSAtConstantP = partialVAtConstantT

theorem envMaxwellCommuteZero : envMaxwellCommuteBalance 0 0 := rfl

-- ================================================================
-- SECTION 4: Gibbs–Duhem differential on Env thermo sections (not float bag)
-- ================================================================

structure EnvGibbsDuhemDifferential where
  entropy : ℚ
  volume : ℚ
  deltaTemperature : ℚ
  deltaPressure : ℚ
  deltaMu : ℚ

def envGibbsDuhemDifferentialHolds (d : EnvGibbsDuhemDifferential) : Prop :=
  UMST.Chem.Constants.ConstantsSheaf.gibbsDuhemBalance d.entropy d.volume
    d.deltaTemperature d.deltaPressure d.deltaMu

def envGibbsDuhemZeroDifferential : EnvGibbsDuhemDifferential :=
  { entropy := 0
    volume := 0
    deltaTemperature := 0
    deltaPressure := 0
    deltaMu := 0 }

theorem envGibbsDuhemZeroDifferentialHolds :
    envGibbsDuhemDifferentialHolds envGibbsDuhemZeroDifferential := by
  unfold envGibbsDuhemDifferentialHolds envGibbsDuhemZeroDifferential
    UMST.Chem.Constants.ConstantsSheaf.gibbsDuhemBalance
  ring

-- ================================================================
-- SECTION 5: Env thermo coordinate sections (graph functions — not bare pins)
-- ================================================================

def envThermoCoordinateSection (E : MesoEnvironmentSheaf) (v : InteractGraphVertex) : ℝ :=
  E.sheaf_thermo_continuum v

def envNeighborCouplingSection (E : MesoEnvironmentSheaf) (v : InteractGraphVertex) : ℝ :=
  E.sheaf_neighbor_coupling v

def envThermoAtVacuum (E : MesoEnvironmentSheaf) : ℝ :=
  envThermoCoordinateSection E vacuumGraphVertex

def envThermoAtContained (E : MesoEnvironmentSheaf) : ℝ :=
  envThermoCoordinateSection E containedGraphVertex

def envThermoAtMessy (E : MesoEnvironmentSheaf) : ℝ :=
  envThermoCoordinateSection E messyGraphVertex

def envCoordinatesSectionsDistinctOnFixture : Prop :=
  (envSampleSectionsTriple envSampleFixtureSheaf).ess_vacuum ≠
    (envSampleSectionsTriple envSampleFixtureSheaf).ess_messy

theorem envCoordinatesSectionsDistinctOnFixtureHolds :
    envCoordinatesSectionsDistinctOnFixture :=
  envSampleSectionsFixtureTripleDistinct

def refuseIndependentEnvFloatBag : Prop :=
  ∃ E : MesoEnvironmentSheaf, vacuumSampleSection E ≠ messySampleSection E

theorem refuseIndependentEnvFloatBagHolds : refuseIndependentEnvFloatBag :=
  ⟨envSampleFixtureSheaf, by
    have h := envSampleSectionsFixtureTripleDistinct
    dsimp [vacuumSampleSection, messySampleSection, envSampleFixtureSheaf,
      witnessEnvironmentSheaf, vacuumGraphVertex, messyGraphVertex] at h ⊢
    exact h⟩

theorem envGibbsDuhemFixtureThermoSectionsPositive (v : InteractGraphVertex) :
    0 < envThermoCoordinateSection envSampleFixtureSheaf v := by
  dsimp [envThermoCoordinateSection, envSampleFixtureSheaf, witnessEnvironmentSheaf]
  cases v <;> norm_num

-- ================================================================
-- SECTION 6: Composition-weighted interdependence (reuse ConstantsSheaf pattern)
-- ================================================================

def envGibbsDuhemInterdependence (fractions coordinateVariations : List ℚ) : Prop :=
  UMST.Chem.Constants.ConstantsSheaf.gibbsDuhemInterdependence fractions coordinateVariations

def envDebyeSquareInterdependence (legs legVariations : List ℚ) : Prop :=
  envCompositionInterdependence legs legVariations

theorem envGibbsDuhemZeroCoordinateVariation (fractions : List ℚ) :
    envGibbsDuhemInterdependence fractions (List.map (fun _ => (0 : ℚ)) fractions) := by
  unfold envGibbsDuhemInterdependence
  exact UMST.Chem.Constants.ConstantsSheaf.gibbsDuhemInterdependence_zero fractions

theorem envDebyeSquareZeroVariation (legs : List ℚ) :
    envDebyeSquareInterdependence legs (List.map (fun _ => (0 : ℚ)) legs) := by
  unfold envDebyeSquareInterdependence
  exact envCompositionZeroVariation legs

theorem envGibbsDuhemMatchesConstantsPattern (fractions : List ℚ) :
    envGibbsDuhemInterdependence fractions (List.map (fun _ => (0 : ℚ)) fractions) ∧
      UMST.Chem.Constants.ConstantsSheaf.gibbsDuhemInterdependence fractions
        (List.map (fun _ => (0 : ℚ)) fractions) :=
  ⟨envGibbsDuhemZeroCoordinateVariation fractions,
   UMST.Chem.Constants.ConstantsSheaf.gibbsDuhemInterdependence_zero fractions⟩

theorem envDebyeMatchesCompositionPattern (legs : List ℚ) :
    envDebyeSquareInterdependence legs (List.map (fun _ => (0 : ℚ)) legs) ∧
      envCompositionInterdependence legs (List.map (fun _ => (0 : ℚ)) legs) :=
  ⟨envDebyeSquareZeroVariation legs, envCompositionZeroVariation legs⟩

-- ================================================================
-- SECTION 7: Env sheaf + sample sections coupled interdependence witness
-- ================================================================

def envGibbsDuhemFixtureFractions : List ℚ := [1, 0, 0, 0]

def envDebyeSquareFixtureLegs : List ℚ := [1, 0, 0]

def envGibbsDuhemCoupledSections (E : MesoEnvironmentSheaf) : Prop :=
  envSampleSectionsWellTyped E ∧
    thermoContinuumFieldPositive E.sheaf_thermo_continuum ∧
      envGibbsDuhemInterdependence envGibbsDuhemFixtureFractions
        (List.map (fun _ => (0 : ℚ)) envGibbsDuhemFixtureFractions) ∧
        envDebyeSquareInterdependence envDebyeSquareFixtureLegs
          (List.map (fun _ => (0 : ℚ)) envDebyeSquareFixtureLegs)

theorem envGibbsDuhemFixtureCoupled :
    envGibbsDuhemCoupledSections envSampleFixtureSheaf := by
  refine ⟨envSampleSectionsFixtureWellTyped, ?_, ?_, ?_⟩
  · intro v; dsimp [thermoContinuumFieldPositive, envSampleFixtureSheaf, witnessEnvironmentSheaf]
    norm_num
  · exact envGibbsDuhemZeroCoordinateVariation envGibbsDuhemFixtureFractions
  · exact envDebyeSquareZeroVariation envDebyeSquareFixtureLegs

theorem envGibbsDuhemFixtureSampleTripleDistinct :
    (envSampleSectionsTriple envSampleFixtureSheaf).ess_vacuum ≠
      (envSampleSectionsTriple envSampleFixtureSheaf).ess_messy :=
  envSampleSectionsFixtureTripleDistinct

-- ================================================================
-- SECTION 8: Honesty fence (physics_green false — not measured env pins)
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def chemEnvGibbsDuhemPhysicsGreen : Bool := false

theorem chemEnvGibbsDuhemPhysicsGreenFalse :
    chemEnvGibbsDuhemPhysicsGreen = false := rfl

/-- Production wiring stays open (CAT-00 lift only). -/
def envGibbsDuhemProductionWired : Bool := false

theorem envGibbsDuhemProductionWiredFalse :
    envGibbsDuhemProductionWired = false := rfl

/-- Catalog witness: meso chemistry env Gibbs–Duhem module present. -/
theorem envGibbsDuhemModuleWitness : True := trivial

end UMST.Chem.Environment.EnvGibbsDuhem
