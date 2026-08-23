-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/ConvexHull.lean

  Meso acting chemistry — Gibbs **convex hull** / **common-tangent** phase coexistence
  as a **corollary** of `LandauerLaw.physicalSecondLaw` via `Chem.SecondLaw` +
  `Chem.Conservation`.  CALPHAD-style G(T,P,x) equilibrium is a second-law
  **presentation** — **not** a 26th thermodynamic axiom.

  Adds **zero** Lean `axiom` declarations.

  Fiber: meso/acting → `umst-formal` only.  No quantum theorems.
-/

import Chem.Conservation
import Chem.SecondLaw

open Real Finset UMST.LandauerLaw UMST.Chem.SecondLaw UMST.Chem.Conservation

namespace UMST.Chem.ConvexHull

-- ================================================================
-- SECTION 1: Gibbs surface + common-tangent carriers (acting meso)
-- ================================================================

/-- A point on a Gibbs energy curve G(x) at fixed (T,P) — design scaffold [J/mol]. -/
structure GibbsSurfacePoint where
  /-- Mole fraction of component A ∈ [0, 1]. -/
  compositionA : ℝ
  /-- Gibbs energy at this composition — presentation scalar, not measured G. -/
  gibbsJPerMol : ℝ

/-- Whether composition lies in the closed unit interval. -/
def compositionInUnitInterval (p : GibbsSurfacePoint) : Prop :=
  0 ≤ p.compositionA ∧ p.compositionA ≤ 1

/-- Common-tangent witness: line y = slope · x + intercept on G-x diagram. -/
structure CommonTangentWitness where
  /-- Tangent slope dG/dx on the coexistence line. -/
  slope : ℝ
  /-- Intercept at x = 0. -/
  intercept : ℝ

/-- Evaluate tangent line at composition `x`. -/
def CommonTangentWitness.valueAt (w : CommonTangentWitness) (x : ℝ) : ℝ :=
  w.slope * x + w.intercept

/-- Whether both phase points lie on this tangent within `eps` [J/mol]. -/
def bothPhasesOnTangent (w : CommonTangentWitness) (α β : GibbsSurfacePoint) (eps : ℝ) :
    Prop :=
  |α.gibbsJPerMol - w.valueAt α.compositionA| ≤ eps ∧
  |β.gibbsJPerMol - w.valueAt β.compositionA| ≤ eps

-- ================================================================
-- SECTION 2: Presentation kinds (convex hull vs common tangent vs refuse)
-- ================================================================

/-- Presentation kind — convex hull vs common tangent vs refused thermo axiom. -/
inductive GibbsPresentationKind where
  | ConvexHullPresentation
  | CommonTangentPresentation
  | ThermoAxiomMintRefuse
  deriving DecidableEq, Repr

/-- Authorized second-law presentations (not thermo axiom mint). -/
def isSecondLawPresentation (k : GibbsPresentationKind) : Prop :=
  k = GibbsPresentationKind.ConvexHullPresentation ∨
    k = GibbsPresentationKind.CommonTangentPresentation

theorem convexHullPresentation_is_secondLaw_presentation :
    isSecondLawPresentation GibbsPresentationKind.ConvexHullPresentation :=
  Or.inl rfl

theorem commonTangentPresentation_is_secondLaw_presentation :
    isSecondLawPresentation GibbsPresentationKind.CommonTangentPresentation :=
  Or.inr rfl

theorem thermoAxiomMint_is_not_secondLaw_presentation :
    ¬ isSecondLawPresentation GibbsPresentationKind.ThermoAxiomMintRefuse := by
  intro h
  rcases h with h1 | h2
  · cases h1
  · cases h2

/-- Convex hull presentation is distinct from thermo axiom mint. -/
theorem convexHull_not_thermo_axiom_mint :
    GibbsPresentationKind.ConvexHullPresentation ≠ GibbsPresentationKind.ThermoAxiomMintRefuse :=
  by decide

/-- Common-tangent presentation is distinct from thermo axiom mint. -/
theorem commonTangent_not_thermo_axiom_mint :
    GibbsPresentationKind.CommonTangentPresentation ≠ GibbsPresentationKind.ThermoAxiomMintRefuse :=
  by decide

-- ================================================================
-- SECTION 3: Convex-hull equilibrium scaffold (second law + conservation)
-- ================================================================

/-- Convex-hull equilibrium bundle: conserved transition + presentation kind. -/
structure ConvexHullEquilibrium (n : ℕ) where
  transition : ConservedChemTransition n
  presentation : GibbsPresentationKind
  presentation_is_second_law : isSecondLawPresentation presentation

/-- Second-law admissibility on the thermochemical leg. -/
def convexHullSecondLawAdmissible {n : ℕ} (h : ConvexHullEquilibrium n) : Prop :=
  chemSecondLaw h.transition.thermo

/-- Linear conservation preserved on the thermochemical leg. -/
def convexHullLinearConservationPreserved {n : ℕ} (w : LinearConservationWitness n)
    (h : ConvexHullEquilibrium n) : Prop :=
  linearConservationPreserved w h.transition

/-- Full admissibility: second law + linear conservation witness. -/
def admissibleConvexHullEquilibrium {n : ℕ} (w : LinearConservationWitness n)
    (h : ConvexHullEquilibrium n) : Prop :=
  admissibleConservedTransition w h.transition

/-- Common-tangent coexistence witness on a binary G-x diagram. -/
structure CommonTangentCoexistence where
  tangent : CommonTangentWitness
  alpha : GibbsSurfacePoint
  beta : GibbsSurfacePoint
  eps : ℝ
  eps_nonneg : 0 ≤ eps
  alpha_in_unit : compositionInUnitInterval alpha
  beta_in_unit : compositionInUnitInterval beta
  onTangent : bothPhasesOnTangent tangent alpha beta eps

/-- Common-tangent coexistence bundled with convex-hull equilibrium. -/
structure CommonTangentEquilibrium (n : ℕ) extends ConvexHullEquilibrium n where
  coexistence : CommonTangentCoexistence
  presentation_eq : toConvexHullEquilibrium.presentation =
    GibbsPresentationKind.CommonTangentPresentation

-- ================================================================
-- SECTION 4: physicalSecondLaw bridge (corollary — zero new axioms)
-- ================================================================

/-- `physicalSecondLaw` discharges chemical second law on bridged assemblages. -/
theorem convexHull_chemSecondLaw_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    chemSecondLaw b.transition :=
  chemSecondLaw_from_physical b hSL

/-- Entropy accounting corollary from `physicalSecondLaw`. -/
theorem convexHull_entropy_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    assemblageEntropyDrop b.transition ≤
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val :=
  chem_entropy_bound_from_physical b hSL

/-- Landauer refinement floor corollary from `physicalSecondLaw`. -/
theorem convexHull_refinementLandauer (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    b.transition.dissipatedWork ≥
      b.transition.bath.bathTemp.val * log 2 :=
  refinementLandauerBound b hSL

/-- Physical bridge yields admissible convex-hull equilibrium at zero composition delta. -/
theorem admissibleConvexHull_from_physical_bridge (b : PhysicalChemBridge)
    (w : LinearConservationWitness 2)
    (hDelta : conservedCompositionDelta ⟨b.transition, fun _ => 0, fun _ => 0⟩ = fun _ => 0)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleConvexHullEquilibrium w
      { transition := ⟨b.transition, fun _ => 0, fun _ => 0⟩
        presentation := GibbsPresentationKind.ConvexHullPresentation
        presentation_is_second_law := convexHullPresentation_is_secondLaw_presentation } :=
  admissible_from_physical_bridge b w hDelta hSL

/-- Physical bridge discharges convex-hull second-law admissibility. -/
theorem convexHullSecondLaw_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    convexHullSecondLawAdmissible
      { transition := ⟨b.transition, fun _ => 0, fun _ => 0⟩
        presentation := GibbsPresentationKind.ConvexHullPresentation
        presentation_is_second_law := convexHullPresentation_is_secondLaw_presentation } :=
  chemSecondLaw_from_physical b hSL

/-- Physical bridge discharges common-tangent second-law admissibility. -/
theorem commonTangentSecondLaw_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    convexHullSecondLawAdmissible
      { transition := ⟨b.transition, fun _ => 0, fun _ => 0⟩
        presentation := GibbsPresentationKind.CommonTangentPresentation
        presentation_is_second_law := commonTangentPresentation_is_secondLaw_presentation } :=
  chemSecondLaw_from_physical b hSL

/-- Admissible convex-hull equilibrium satisfies the chemical second law. -/
theorem admissibleConvexHull_secondLaw {n : ℕ} (w : LinearConservationWitness n)
    (h : ConvexHullEquilibrium n) (hadm : admissibleConvexHullEquilibrium w h) :
    convexHullSecondLawAdmissible h :=
  hadm.1

/-- Admissible convex-hull equilibrium satisfies linear conservation. -/
theorem admissibleConvexHull_linearConservation {n : ℕ} (w : LinearConservationWitness n)
    (h : ConvexHullEquilibrium n) (hadm : admissibleConvexHullEquilibrium w h) :
    convexHullLinearConservationPreserved w h :=
  hadm.2

-- ================================================================
-- SECTION 5: Canonical fixtures (0 sorry — catalog witnesses)
-- ================================================================

/-- Canonical binary common-tangent fixture (mirrors `gibbs_convex_hull.rs`). -/
noncomputable def canonicalBinaryCommonTangent : CommonTangentWitness :=
  { slope := -0.5, intercept := 1.0 }

noncomputable def canonicalBinaryAlpha : GibbsSurfacePoint :=
  { compositionA := 0.2
    gibbsJPerMol := canonicalBinaryCommonTangent.valueAt 0.2 }

noncomputable def canonicalBinaryBeta : GibbsSurfacePoint :=
  { compositionA := 0.8
    gibbsJPerMol := canonicalBinaryCommonTangent.valueAt 0.8 }

theorem canonicalBinaryAlpha_in_unit : compositionInUnitInterval canonicalBinaryAlpha := by
  unfold compositionInUnitInterval canonicalBinaryAlpha
  constructor <;> norm_num

theorem canonicalBinaryBeta_in_unit : compositionInUnitInterval canonicalBinaryBeta := by
  unfold compositionInUnitInterval canonicalBinaryBeta
  constructor <;> norm_num

theorem canonicalBinaryCommonTangent_onTangent :
    bothPhasesOnTangent canonicalBinaryCommonTangent canonicalBinaryAlpha
      canonicalBinaryBeta 0 := by
  unfold bothPhasesOnTangent
  constructor <;> dsimp [canonicalBinaryAlpha, canonicalBinaryBeta,
    canonicalBinaryCommonTangent, CommonTangentWitness.valueAt] <;> ring_nf <;> simp

noncomputable def canonicalBinaryCommonTangentCoexistence : CommonTangentCoexistence where
  tangent := canonicalBinaryCommonTangent
  alpha := canonicalBinaryAlpha
  beta := canonicalBinaryBeta
  eps := 0
  eps_nonneg := le_rfl
  alpha_in_unit := canonicalBinaryAlpha_in_unit
  beta_in_unit := canonicalBinaryBeta_in_unit
  onTangent := canonicalBinaryCommonTangent_onTangent

/-- Coherent P0 convex-hull equilibrium at zero cost (catalog witness). -/
noncomputable def coherentP0ConvexHullEquilibrium : ConvexHullEquilibrium 2 where
  transition :=
    { thermo := coherentP0Transition
      priorComp := fun _ => 0
      postComp := fun _ => 0 }
  presentation := GibbsPresentationKind.ConvexHullPresentation
  presentation_is_second_law := convexHullPresentation_is_secondLaw_presentation

theorem coherentP0ConvexHull_secondLaw :
    convexHullSecondLawAdmissible coherentP0ConvexHullEquilibrium :=
  coherentP0_chemSecondLaw

/-- Coherent P0 common-tangent equilibrium at zero cost. -/
noncomputable def coherentP0CommonTangentEquilibrium : CommonTangentEquilibrium 2 where
  toConvexHullEquilibrium :=
    { transition :=
        { thermo := coherentP0Transition
          priorComp := fun _ => 0
          postComp := fun _ => 0 }
      presentation := GibbsPresentationKind.CommonTangentPresentation
      presentation_is_second_law := commonTangentPresentation_is_secondLaw_presentation }
  coexistence := canonicalBinaryCommonTangentCoexistence
  presentation_eq := rfl

theorem coherentP0CommonTangent_secondLaw :
    convexHullSecondLawAdmissible coherentP0CommonTangentEquilibrium.toConvexHullEquilibrium :=
  coherentP0_chemSecondLaw

-- ================================================================
-- SECTION 6: Honesty fence (physics_green false — not measured G pins)
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def convexHullPhysicsGreen : Bool := false

theorem convexHullPhysicsGreenFalse : convexHullPhysicsGreen = false := rfl

/-- Production wiring stays open (CHEM-MATH-GIBBS-CONVEX-HULL lift only). -/
def convexHullProductionWired : Bool := false

theorem convexHullProductionWiredFalse : convexHullProductionWired = false := rfl

/-- Catalog witness: meso chemistry convex-hull module present. -/
theorem convexHullModuleWitness : True := trivial

end UMST.Chem.ConvexHull
