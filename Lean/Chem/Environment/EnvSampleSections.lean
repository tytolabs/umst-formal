-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/Environment/EnvSampleSections.lean

  Meso/acting chemistry — named Env sample sections (probe layer).
  Vacuum / contained / messy are **named sample sections** of one Env sheaf on the
  Interact graph — a simultaneous triple, not XOR worlds and not a third axiom.
  Sample-probe layer on `EnvironmentContinuum`.

  Mirrors `Haskell/UMST/Chem/Environment/EnvSampleSections.hs` and
  `Coq/Chem/Environment/EnvSampleSections.v` on `umst-formal/meso_acting`.
  Imports `EnvironmentContinuum` only; adds **zero** Lean `axiom` declarations.

  v15: vacuum/contained/messy are three named sample sections of one Env sheaf, not XOR.
  `physics_green` stays false — thermo witnesses remain Unwired.
-/

import Chem.Environment.EnvironmentContinuum

open Real UMST UMST.Chem.KleisliInteract
open UMST.Chem.Environment.EnvironmentContinuum

namespace UMST.Chem.Environment.EnvSampleSections

-- ================================================================
-- SECTION 1: Regime tags (named sections — not XOR regime selection)
-- ================================================================

/-- Named environment section regime tags (vacuum | contained | messy). -/
inductive EnvironmentSectionRegime where
  | VacuumSection
  | ContainedSection
  | MessySection

def environmentSectionRegimeTags : List EnvironmentSectionRegime :=
  [EnvironmentSectionRegime.VacuumSection,
   EnvironmentSectionRegime.ContainedSection,
   EnvironmentSectionRegime.MessySection]

def environmentRegimeCardinality : ℕ := environmentSectionRegimeTags.length

theorem environmentRegimeCardinality_eq : environmentRegimeCardinality = 3 := rfl

-- ================================================================
-- SECTION 2: Named sample probes (vacuum | contained | messy — not XOR)
-- ================================================================

def vacuumSampleProbe (E : MesoEnvironmentSheaf) : ℝ :=
  vacuumSampleSection E

def containedSampleProbe (E : MesoEnvironmentSheaf) : ℝ :=
  containedSampleSection E

def messySampleProbe (E : MesoEnvironmentSheaf) : ℝ :=
  messySampleSection E

def sampleSectionAtRegime (r : EnvironmentSectionRegime) (E : MesoEnvironmentSheaf) : ℝ :=
  match r with
  | EnvironmentSectionRegime.VacuumSection => vacuumSampleProbe E
  | EnvironmentSectionRegime.ContainedSection => containedSampleProbe E
  | EnvironmentSectionRegime.MessySection => messySampleProbe E

def vacuumThermoSampleProbe (E : MesoEnvironmentSheaf) : ℝ :=
  vacuumThermoContinuumSection E

def containedThermoSampleProbe (E : MesoEnvironmentSheaf) : ℝ :=
  containedThermoContinuumSection E

def messyThermoSampleProbe (E : MesoEnvironmentSheaf) : ℝ :=
  messyThermoContinuumSection E

-- ================================================================
-- SECTION 3: Simultaneous triple on one Env sheaf (not XOR sample-space pick)
-- ================================================================

structure EnvSampleSectionBundle where
  ess_vacuum : ℝ
  ess_contained : ℝ
  ess_messy : ℝ

def envSampleSectionsTriple (E : MesoEnvironmentSheaf) : EnvSampleSectionBundle :=
  { ess_vacuum := vacuumSampleProbe E
    ess_contained := containedSampleProbe E
    ess_messy := messySampleProbe E }

theorem envSampleSectionsTriple_components (E : MesoEnvironmentSheaf) :
    (envSampleSectionsTriple E).ess_vacuum = vacuumSampleProbe E ∧
    (envSampleSectionsTriple E).ess_contained = containedSampleProbe E ∧
    (envSampleSectionsTriple E).ess_messy = messySampleProbe E :=
  ⟨rfl, rfl, rfl⟩

theorem envSampleSectionsRegimeVacuumContainedDistinct :
    EnvironmentSectionRegime.VacuumSection ≠ EnvironmentSectionRegime.ContainedSection := by
  rintro h; cases h

theorem envSampleSectionsRegimeVacuumMessyDistinct :
    EnvironmentSectionRegime.VacuumSection ≠ EnvironmentSectionRegime.MessySection := by
  rintro h; cases h

theorem envSampleSectionsRegimeContainedMessyDistinct :
    EnvironmentSectionRegime.ContainedSection ≠ EnvironmentSectionRegime.MessySection := by
  rintro h; cases h

def envSampleSectionsWellTyped (E : MesoEnvironmentSheaf) : Prop :=
  0 < vacuumSampleProbe E ∧
  0 < containedSampleProbe E ∧
  0 < messySampleProbe E ∧
  thermoContinuumFieldPositive E.sheaf_thermo_continuum

theorem envSampleSectionsNamedNotXor : envSampleSectionsNotXor :=
  envSampleSectionsNotXorHolds

def envSampleSectionsRegimeDistinct : Prop :=
  EnvironmentSectionRegime.VacuumSection ≠ EnvironmentSectionRegime.ContainedSection ∧
  EnvironmentSectionRegime.VacuumSection ≠ EnvironmentSectionRegime.MessySection ∧
  EnvironmentSectionRegime.ContainedSection ≠ EnvironmentSectionRegime.MessySection

theorem envSampleSectionsRegimeDistinctHolds : envSampleSectionsRegimeDistinct :=
  ⟨envSampleSectionsRegimeVacuumContainedDistinct,
   envSampleSectionsRegimeVacuumMessyDistinct,
   envSampleSectionsRegimeContainedMessyDistinct⟩

theorem sampleSectionAtRegimeMatchesTriple (E : MesoEnvironmentSheaf) :
    sampleSectionAtRegime EnvironmentSectionRegime.VacuumSection E =
      (envSampleSectionsTriple E).ess_vacuum ∧
    sampleSectionAtRegime EnvironmentSectionRegime.ContainedSection E =
      (envSampleSectionsTriple E).ess_contained ∧
    sampleSectionAtRegime EnvironmentSectionRegime.MessySection E =
      (envSampleSectionsTriple E).ess_messy :=
  ⟨rfl, rfl, rfl⟩

-- ================================================================
-- SECTION 4: Edge sample probes (reuse continuum sheaf on admissible edges)
-- ================================================================

/-- Named environment sample sections on an edge — simultaneous triple, not XOR. -/
abbrev EnvironmentSampleSections := ℚ × ℚ × ℚ

def vacuumSampleSectionOnEdge (old new : ThermodynamicState) : Option ℚ :=
  vacuumSectionOnEdge old new

def containedSampleSectionOnEdge (old new : ThermodynamicState) : Option ℚ :=
  containedSectionOnEdge old new

def messySampleSectionOnEdge (old new : ThermodynamicState) : Option ℚ :=
  messySectionOnEdge old new

def sampleSectionOnEdge (r : EnvironmentSectionRegime) (old new : ThermodynamicState) : Option ℚ :=
  match r with
  | EnvironmentSectionRegime.VacuumSection => vacuumSampleSectionOnEdge old new
  | EnvironmentSectionRegime.ContainedSection => containedSampleSectionOnEdge old new
  | EnvironmentSectionRegime.MessySection => messySampleSectionOnEdge old new

def envSampleSectionsOnEdge (old new : ThermodynamicState) : Option EnvironmentSampleSections :=
  environmentSheafOnEdge old new

def envSampleSectionsWellTypedOnEdge (old new : ThermodynamicState) : Prop :=
  gateCheck old new = false ∨
    match envSampleSectionsOnEdge old new with
    | none => True
    | some (v, c, m) => 0 ≤ v ∧ 0 ≤ c ∧ 0 ≤ m

theorem envSampleSectionsNamedNotXorOnEdge :
    environmentRegimeCardinality = 3 := environmentSectionsNamedNotXor

theorem envSampleSectionsOnEdge_ungated (old new : ThermodynamicState)
    (h : gateCheck old new = false) :
    envSampleSectionsOnEdge old new = none := by
  unfold envSampleSectionsOnEdge
  exact environmentSheafOnEdge_ungated old new h

theorem envSampleSectionsOnEdge_admissible (old new : ThermodynamicState)
    (_ : admissibleStep old new) :
    envSampleSectionsOnEdge old new = environmentSheafOnEdge old new := rfl

-- ================================================================
-- SECTION 5: Fixture sheaf — simultaneous named sample triple on one Env sheaf
-- ================================================================

noncomputable def envSampleFixtureSheaf : MesoEnvironmentSheaf :=
  witnessEnvironmentSheaf

theorem envSampleSectionsFixtureWellTyped : envSampleSectionsWellTyped envSampleFixtureSheaf := by
  dsimp [envSampleSectionsWellTyped, envSampleFixtureSheaf, witnessEnvironmentSheaf,
    vacuumSampleProbe, containedSampleProbe, messySampleProbe,
    vacuumSampleSection, containedSampleSection, messySampleSection,
    vacuumGraphVertex, containedGraphVertex, messyGraphVertex,
    thermoContinuumFieldPositive]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals norm_num

theorem envSampleSectionsFixtureTripleDistinct :
    (envSampleSectionsTriple envSampleFixtureSheaf).ess_vacuum ≠
      (envSampleSectionsTriple envSampleFixtureSheaf).ess_messy := by
  dsimp [envSampleSectionsTriple, envSampleFixtureSheaf, witnessEnvironmentSheaf,
    vacuumSampleProbe, messySampleProbe, vacuumSampleSection, messySampleSection,
    vacuumGraphVertex, messyGraphVertex]
  norm_num

theorem envSampleSectionsFixtureWitness :
    envSampleSectionsWellTyped envSampleFixtureSheaf ∧ vacuumDoesNotCloseMessy :=
  ⟨envSampleSectionsFixtureWellTyped, vacuumDoesNotCloseMessyHolds⟩

-- ================================================================
-- SECTION 6: Honesty fence (physics_green false — not measured env pins)
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def chemEnvSampleSectionsPhysicsGreen : Bool := false

theorem chemEnvSampleSectionsPhysicsGreenFalse :
    chemEnvSampleSectionsPhysicsGreen = false := rfl

/-- Production wiring stays open (CAT-00 lift only). -/
def envSampleSectionsProductionWired : Bool := false

theorem envSampleSectionsProductionWiredFalse :
    envSampleSectionsProductionWired = false := rfl

/-- Catalog witness: meso chemistry env sample sections module present. -/
theorem envSampleSectionsModuleWitness : True := trivial

end UMST.Chem.Environment.EnvSampleSections
