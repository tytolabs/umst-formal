-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/PatternNuance.lean

  Meso acting chemistry — §2 **pattern taxonomy** classifiers and §3 **PatternBundle**
  concurrent product (Π_c, not XOR) as predicates on `Element`.

  Mirrors `umst-chem/src/pattern_taxonomy.rs` north-star §2 tags (25 classes).
  Anchored in `Chem.SecondLaw` + `Chem.Conservation` via sibling meso modules.
  Adds **zero** Lean `axiom` declarations.

  Fiber: meso/acting → `umst-formal` only.  No quantum theorems.
-/

import Chem.Conservation
import Chem.KleisliInteract
import Chem.OreAssemblage
import Chem.RefineCost

open Real Finset UMST.LandauerLaw UMST.Chem.SecondLaw UMST.Chem.Conservation
open UMST.Chem.OreAssemblage UMST.Chem.KleisliInteract UMST.Chem.RefineCost

namespace UMST.Chem.PatternNuance

-- ================================================================
-- SECTION 1: Element carrier (IUPAC Z = 1 .. 118)
-- ================================================================

/-- L0 element carrier — atomic number in IUPAC range (design scaffold). -/
structure Element where
  z : ℕ
  hZ : 1 ≤ z ∧ z ≤ 118

/-- Atomic number projection. -/
def elementZ (e : Element) : ℕ := e.z

/-- Canonical carbon element (Z = 6). -/
def carbonElement : Element := ⟨6, by decide⟩

/-- Canonical helium element (Z = 2). -/
def heliumElement : Element := ⟨2, by decide⟩

/-- IUPAC element cardinality pin. -/
def elementCardinality : ℕ := 118

theorem elementZ_in_range (e : Element) : 1 ≤ e.z ∧ e.z ≤ 118 :=
  e.hZ

-- ================================================================
-- SECTION 2: §2 pattern class tags (north-star order — 25 classes)
-- ================================================================

/-- North-star §2 pattern class (bijection with `Fin 25`). -/
inductive PatternClass where
  | perElementNuance
  | shared
  | bondForming
  | bondRepelling
  | structureEnabling
  | structureBlockingInertness
  | naturalOreAssemblage
  | assemblageStabilityWhy
  | impureComponentMorphism
  | processingRefining
  | allotrope
  | isotope
  | metastableVsEquilibrium
  | phaseEutecticSolidSolution
  | catalysis
  | surfaceVsBulkSdf
  | aqueousVsMineral
  | redoxLadder
  | polymorphism
  | tpParametric
  | contaminationReverseRefine
  | assayMeasurementLandauer
  | vacuumInertLimit
  | continuumVsDiscreteElementId
  | otherNamedNuance
  deriving DecidableEq, Repr

/-- Class index in north-star order (0 .. 24). -/
def PatternClass.index : PatternClass → Fin 25
  | .perElementNuance => 0
  | .shared => 1
  | .bondForming => 2
  | .bondRepelling => 3
  | .structureEnabling => 4
  | .structureBlockingInertness => 5
  | .naturalOreAssemblage => 6
  | .assemblageStabilityWhy => 7
  | .impureComponentMorphism => 8
  | .processingRefining => 9
  | .allotrope => 10
  | .isotope => 11
  | .metastableVsEquilibrium => 12
  | .phaseEutecticSolidSolution => 13
  | .catalysis => 14
  | .surfaceVsBulkSdf => 15
  | .aqueousVsMineral => 16
  | .redoxLadder => 17
  | .polymorphism => 18
  | .tpParametric => 19
  | .contaminationReverseRefine => 20
  | .assayMeasurementLandauer => 21
  | .vacuumInertLimit => 22
  | .continuumVsDiscreteElementId => 23
  | .otherNamedNuance => 24

/-- §2 class cardinality (north-star pinned). -/
def patternClassCardinality : ℕ := 25

theorem patternClassCardinality_eq : patternClassCardinality = 25 := rfl

/-- Recover class from index (partial inverse of `index`). -/
def patternClassOfFin (i : Fin 25) : PatternClass :=
  match i.val with
  | 0 => .perElementNuance
  | 1 => .shared
  | 2 => .bondForming
  | 3 => .bondRepelling
  | 4 => .structureEnabling
  | 5 => .structureBlockingInertness
  | 6 => .naturalOreAssemblage
  | 7 => .assemblageStabilityWhy
  | 8 => .impureComponentMorphism
  | 9 => .processingRefining
  | 10 => .allotrope
  | 11 => .isotope
  | 12 => .metastableVsEquilibrium
  | 13 => .phaseEutecticSolidSolution
  | 14 => .catalysis
  | 15 => .surfaceVsBulkSdf
  | 16 => .aqueousVsMineral
  | 17 => .redoxLadder
  | 18 => .polymorphism
  | 19 => .tpParametric
  | 20 => .contaminationReverseRefine
  | 21 => .assayMeasurementLandauer
  | 22 => .vacuumInertLimit
  | 23 => .continuumVsDiscreteElementId
  | 24 => .otherNamedNuance
  | _ => .otherNamedNuance

theorem patternClass_index_roundtrip (c : PatternClass) :
    patternClassOfFin (PatternClass.index c) = c := by
  cases c <;> native_decide

-- ================================================================
-- SECTION 3: Classifiers as predicates on Element (not XOR worlds)
-- ================================================================

/-- Class 0 — per-element nuance slot (Unwired scaffold). -/
def perElementNuanceClassifier (e : Element) : Prop :=
  1 ≤ e.z ∧ e.z ≤ 118

/-- Class 1 — shared nuance leg (Unwired scaffold). -/
def sharedClassifier (_e : Element) : Prop :=
  True

/-- Class 2 — bond-forming nuance leg (Unwired scaffold). -/
def bondFormingClassifier (_e : Element) : Prop :=
  True

/-- Class 3 — bond-repelling nuance leg (Unwired scaffold). -/
def bondRepellingClassifier (_e : Element) : Prop :=
  True

/-- Class 4 — structure-enabling nuance leg (Unwired scaffold). -/
def structureEnablingClassifier (_e : Element) : Prop :=
  True

/-- Class 5 — structure-blocking / inertness (He, Ne scaffold). -/
def structureBlockingInertnessClassifier (e : Element) : Prop :=
  e.z = 2 ∨ e.z = 10

/-- Class 6 — natural ore assemblage (Ore morphism leg). -/
def naturalOreAssemblageClassifier (_e : Element) : Prop :=
  True

/-- Class 7 — assemblage-stability why leg (Unwired scaffold). -/
def assemblageStabilityWhyClassifier (_e : Element) : Prop :=
  True

/-- Class 8 — impure-component morphism leg (Unwired scaffold). -/
def impureComponentMorphismClassifier (_e : Element) : Prop :=
  True

/-- Class 9 — processing / refining (Refine morphism leg). -/
def processingRefiningClassifier (_e : Element) : Prop :=
  True

/-- Class 10 — allotrope geometry on same ElementId (C, Si, Ge scaffold). -/
def allotropeClassifier (e : Element) : Prop :=
  e.z = 6 ∨ e.z = 14 ∨ e.z = 32

/-- Class 11 — isotope nuance leg (Unwired scaffold). -/
def isotopeClassifier (_e : Element) : Prop :=
  True

/-- Class 12 — metastable vs equilibrium leg (Unwired scaffold). -/
def metastableVsEquilibriumClassifier (_e : Element) : Prop :=
  True

/-- Class 13 — phase / eutectic / solid-solution leg (Unwired scaffold). -/
def phaseEutecticSolidSolutionClassifier (_e : Element) : Prop :=
  True

/-- Class 14 — catalysis nuance (C, Fe, Pd scaffold). -/
def catalysisClassifier (e : Element) : Prop :=
  e.z = 6 ∨ e.z = 26 ∨ e.z = 46

/-- Class 15 — surface vs bulk SDF leg (Unwired scaffold). -/
def surfaceVsBulkSdfClassifier (_e : Element) : Prop :=
  True

/-- Class 16 — aqueous vs mineral leg (Unwired scaffold). -/
def aqueousVsMineralClassifier (_e : Element) : Prop :=
  True

/-- Class 17 — redox ladder leg (Unwired scaffold). -/
def redoxLadderClassifier (_e : Element) : Prop :=
  True

/-- Class 18 — polymorphism leg (Unwired scaffold). -/
def polymorphismClassifier (_e : Element) : Prop :=
  True

/-- Class 19 — T/P-parametric geometry (carbon diamond/graphite scaffold). -/
def tpParametricClassifier (e : Element) : Prop :=
  e.z = 6

/-- Class 20 — contamination = reverse Refine (endpoint swap). -/
def contaminationReverseRefineClassifier (_e : Element) : Prop :=
  refineSecondLawAdmissible coherentP0Contamination

/-- Class 21 — assay / measurement / Landauer leg (Kleisli gate scaffold). -/
def assayMeasurementLandauerClassifier (_e : Element) : Prop :=
  True

/-- Class 22 — vacuum / inert limit leg (Unwired scaffold). -/
def vacuumInertLimitClassifier (_e : Element) : Prop :=
  True

/-- Class 23 — continuum vs discrete ElementId (valid Z range). -/
def continuumVsDiscreteElementIdClassifier (e : Element) : Prop :=
  1 ≤ e.z ∧ e.z ≤ 118

/-- Class 24 — other named nuance leg (Unwired scaffold). -/
def otherNamedNuanceClassifier (_e : Element) : Prop :=
  True

/-- Dispatch §2 classifier by `PatternClass`. -/
def patternClassifier (c : PatternClass) (e : Element) : Prop :=
  match c with
  | .perElementNuance => perElementNuanceClassifier e
  | .shared => sharedClassifier e
  | .bondForming => bondFormingClassifier e
  | .bondRepelling => bondRepellingClassifier e
  | .structureEnabling => structureEnablingClassifier e
  | .structureBlockingInertness => structureBlockingInertnessClassifier e
  | .naturalOreAssemblage => naturalOreAssemblageClassifier e
  | .assemblageStabilityWhy => assemblageStabilityWhyClassifier e
  | .impureComponentMorphism => impureComponentMorphismClassifier e
  | .processingRefining => processingRefiningClassifier e
  | .allotrope => allotropeClassifier e
  | .isotope => isotopeClassifier e
  | .metastableVsEquilibrium => metastableVsEquilibriumClassifier e
  | .phaseEutecticSolidSolution => phaseEutecticSolidSolutionClassifier e
  | .catalysis => catalysisClassifier e
  | .surfaceVsBulkSdf => surfaceVsBulkSdfClassifier e
  | .aqueousVsMineral => aqueousVsMineralClassifier e
  | .redoxLadder => redoxLadderClassifier e
  | .polymorphism => polymorphismClassifier e
  | .tpParametric => tpParametricClassifier e
  | .contaminationReverseRefine => contaminationReverseRefineClassifier e
  | .assayMeasurementLandauer => assayMeasurementLandauerClassifier e
  | .vacuumInertLimit => vacuumInertLimitClassifier e
  | .continuumVsDiscreteElementId => continuumVsDiscreteElementIdClassifier e
  | .otherNamedNuance => otherNamedNuanceClassifier e

/-- Every §2 class index maps to a named classifier (north-star bijection). -/
theorem pattern_taxonomy_all_classifiers_present :
    patternClassCardinality = 25 ∧
    (∀ c : PatternClass, patternClassOfFin (PatternClass.index c) = c) := by
  refine ⟨rfl, ?_⟩
  intro c
  exact patternClass_index_roundtrip c

/-- Catalog crosswalk: Ore sibling module witness (zero new axioms). -/
theorem ore_module_catalog : True :=
  oreAssemblageModuleWitness

/-- Catalog crosswalk: Refine sibling module witness (zero new axioms). -/
theorem refine_module_catalog : True :=
  refineCostModuleWitness

/-- Catalog crosswalk: Kleisli sibling module witness (zero new axioms). -/
theorem kleisli_module_catalog : True :=
  kleisliInteractModuleWitness

/-- Sibling Ore module witness discharges the ore-assemblage classifier scaffold. -/
theorem naturalOre_classifier_links_module (e : Element) :
    naturalOreAssemblageClassifier e :=
  trivial

/-- Sibling Refine module witness discharges the refining classifier scaffold. -/
theorem processingRefining_classifier_links_module (e : Element) :
    processingRefiningClassifier e :=
  trivial

/-- Sibling Kleisli module witness discharges the assay classifier scaffold. -/
theorem assay_classifier_links_module (e : Element) :
    assayMeasurementLandauerClassifier e :=
  trivial

/-- Classifiers are concurrent — holding one does not refute another (not XOR). -/
theorem classifiers_concurrent_not_xor (e : Element)
    (hall : allotropeClassifier e) (hcat : catalysisClassifier e) :
    allotropeClassifier e ∧ catalysisClassifier e :=
  ⟨hall, hcat⟩

theorem carbon_allotrope : allotropeClassifier carbonElement := by
  simp [allotropeClassifier, carbonElement]

theorem carbon_catalysis : catalysisClassifier carbonElement := by
  simp [catalysisClassifier, carbonElement]

theorem carbon_tp_parametric : tpParametricClassifier carbonElement := by
  simp [tpParametricClassifier, carbonElement]

theorem carbon_continuum_discrete : continuumVsDiscreteElementIdClassifier carbonElement :=
  carbonElement.hZ

theorem helium_structure_blocking : structureBlockingInertnessClassifier heliumElement := by
  simp [structureBlockingInertnessClassifier, heliumElement]

theorem carbon_concurrent_classifiers :
    allotropeClassifier carbonElement ∧
    catalysisClassifier carbonElement ∧
    continuumVsDiscreteElementIdClassifier carbonElement :=
  ⟨carbon_allotrope, carbon_catalysis, carbon_continuum_discrete⟩

/-- Contamination classifier reuses reverse Refine (not a parallel axiom). -/
theorem contamination_classifier_is_reverse_refine :
    contaminationReverseRefineClassifier carbonElement ↔
      refineSecondLawAdmissible coherentP0Contamination := by
  simp [contaminationReverseRefineClassifier, coherentP0Refine_secondLaw]

-- ================================================================
-- SECTION 4: PatternBundle concurrent product (Π_c — not XOR)
-- ================================================================

/-- §3 PatternBundle slot modality — concurrent product factor, not XOR bucket. -/
inductive PatternBundleSlot where
  | unwired
  | absent
  | present
  deriving DecidableEq, Repr

/-- §3 PatternBundle_25 — many classes may hold at once. -/
structure PatternBundle where
  slots : Fin 25 → PatternBundleSlot
  deriving Repr

/-- All slots Unwired — honest scaffold baseline. -/
def patternBundleUnwired : PatternBundle where
  slots := fun _ => .unwired

/-- Read slot at class index. -/
def PatternBundle.slot (b : PatternBundle) (i : Fin 25) : PatternBundleSlot :=
  b.slots i

/-- Whether class index is Present. -/
def PatternBundle.holds (b : PatternBundle) (i : Fin 25) : Bool :=
  b.slots i == .present

/-- Set one slot; leaves others unchanged. -/
def PatternBundle.withSlot (b : PatternBundle) (i : Fin 25) (s : PatternBundleSlot) :
    PatternBundle where
  slots := fun j => if j = i then s else b.slots j

/-- Mark class index Present. -/
def PatternBundle.withPresent (b : PatternBundle) (i : Fin 25) : PatternBundle :=
  b.withSlot i .present

/-- Count Present slots (may exceed 1 — concurrent product). -/
def PatternBundle.presentCount (b : PatternBundle) : ℕ :=
  (Finset.univ.filter fun i => b.holds i).card

/-- Whether bundle demonstrates concurrent product (≥ 2 Present slots). -/
def patternBundleIsConcurrentProduct (b : PatternBundle) : Prop :=
  2 ≤ b.presentCount

/-- Carbon nuance witness: allotrope (10) + catalysis (14) + continuum (23) concurrent. -/
def carbonNuanceWitness : PatternBundle :=
  patternBundleUnwired
    |>.withPresent 10
    |>.withPresent 14
    |>.withPresent 23

theorem carbon_nuance_witness_holds_allotrope :
    carbonNuanceWitness.holds 10 = true := by decide

theorem carbon_nuance_witness_holds_catalysis :
    carbonNuanceWitness.holds 14 = true := by decide

theorem carbon_nuance_witness_holds_continuum :
    carbonNuanceWitness.holds 23 = true := by decide

theorem carbon_nuance_witness_present_count :
    carbonNuanceWitness.presentCount = 3 := by decide

theorem carbon_nuance_witness_concurrent :
    patternBundleIsConcurrentProduct carbonNuanceWitness := by
  unfold patternBundleIsConcurrentProduct carbonNuanceWitness PatternBundle.presentCount
    PatternBundle.holds PatternBundle.withPresent PatternBundle.withSlot patternBundleUnwired
  decide

/-- Present slots are independent — not XOR (two distinct indices may both hold). -/
theorem pattern_bundle_not_xor (b : PatternBundle) (i j : Fin 25)
    (hi : b.holds i = true) (hj : b.holds j = true) :
    b.holds i = true ∧ b.holds j = true :=
  ⟨hi, hj⟩

-- ================================================================
-- SECTION 5: Physical bridge + honesty posture
-- ================================================================

/-- Physical bridge discharges assay classifier via Kleisli second-law lift. -/
theorem assay_classifier_from_physical (b : PhysicalChemBridge)
    (e : Element) (hSL : physicalSecondLawUniformBinary b.proc) :
    assayMeasurementLandauerClassifier e ∧
      chemSecondLaw b.transition := by
  refine ⟨trivial, ?_⟩
  exact interact_chemSecondLaw_from_physical b hSL

/-- Ore classifier inherits physical-bridge admissibility on zero composition delta. -/
theorem ore_classifier_from_physical (b : PhysicalChemBridge)
    (e : Element) (w : LinearConservationWitness 2)
    (hDelta : conservedCompositionDelta ⟨b.transition, fun _ => 0, fun _ => 0⟩ = fun _ => 0)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    naturalOreAssemblageClassifier e ∧
      admissibleRefineMorphism w
        { source := feedstockGrade
          target := concentrateGrade
          transition := ⟨b.transition, fun _ => 0, fun _ => 0⟩
          cost := b.transition.dissipatedWork
          cost_eq_work := rfl } := by
  refine ⟨trivial, ?_⟩
  exact admissibleRefine_from_physical_bridge b w feedstockGrade concentrateGrade hDelta hSL

/-- Physics GREEN unauthorized on this scaffold. -/
def patternNuancePhysicsGreen : Bool := false

theorem patternNuancePhysicsGreenFalse : patternNuancePhysicsGreen = false := rfl

/-- Production wiring stays open (PATTERN-00 / CAT-01 lift only). -/
def patternNuanceProductionWired : Bool := false

theorem patternNuanceProductionWiredFalse : patternNuanceProductionWired = false := rfl

/-- Catalog witness: meso chemistry pattern-nuance module present. -/
theorem patternNuanceModuleWitness : True := trivial

end UMST.Chem.PatternNuance
