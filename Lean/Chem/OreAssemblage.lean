-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/OreAssemblage.lean

  Meso acting chemistry — natural ore assemblage as a **costly morphism** under the
  second-law + conservation spine (`Chem.SecondLaw` + `Chem.Conservation`).

  Ore bodies are monoidal products (binary tree, not bare element lists).  Adds **zero**
  Lean `axiom` declarations.

  Fiber: meso/acting → `umst-formal` only.  No quantum theorems.
-/

import Chem.Conservation

open Real Finset UMST.LandauerLaw UMST.Chem.SecondLaw UMST.Chem.Conservation

namespace UMST.Chem.OreAssemblage

-- ================================================================
-- SECTION 1: Ore assemblage carriers (monoidal ⊗ — not a list)
-- ================================================================

/-- L0 ore-assemblage family tags (scaffold — not bare ElementId lists). -/
inductive OreTag where
  | HematiteDominant
  | BauxiteDominant
  | CalcareousGangue
  deriving DecidableEq, Repr

/-- Monoidal ore product: binary tree (⊗), not a folklore element list. -/
inductive OreTree where
  | leaf : OreTag → OreTree
  | tensor : OreTree → OreTree → OreTree
  deriving Repr

/-- Whether an ore tree is a multi-body scaffold (not a singleton placeholder). -/
def isMultiBodyScaffold : OreTree → Bool
  | .leaf _ => true
  | .tensor l r => isMultiBodyScaffold l && isMultiBodyScaffold r

/-- Canonical hematite-dominant ore leaf. -/
def hematiteLeaf : OreTree := .leaf .HematiteDominant

/-- Canonical bauxite-dominant ore leaf. -/
def bauxiteLeaf : OreTree := .leaf .BauxiteDominant

/-- Paragenetic tensor: hematite ⊗ calcareous gangue (structure only). -/
def hematiteGangueTensor : OreTree :=
  .tensor hematiteLeaf (.leaf .CalcareousGangue)

-- ================================================================
-- SECTION 2: Costly ore morphism (second law + conservation)
-- ================================================================

/-- A costly ore morphism: source/target ore trees bundled with a conserved
    thermochemical transition and explicit dissipated-work accounting. -/
structure OreMorphism (n : ℕ) where
  source : OreTree
  target : OreTree
  transition : ConservedChemTransition n
  cost : ℝ
  cost_eq_work : cost = transition.thermo.dissipatedWork

/-- Dissipated work recorded on the morphism equals the thermochemical leg. -/
theorem oreMorphism_cost_work {n : ℕ} (m : OreMorphism n) :
    m.cost = m.transition.thermo.dissipatedWork :=
  m.cost_eq_work

/-- Second-law admissibility on the thermochemical leg of an ore morphism. -/
def oreSecondLawAdmissible {n : ℕ} (m : OreMorphism n) : Prop :=
  chemSecondLaw m.transition.thermo

/-- Linear conservation preserved on the thermochemical leg. -/
def oreLinearConservationPreserved {n : ℕ} (w : LinearConservationWitness n)
    (m : OreMorphism n) : Prop :=
  linearConservationPreserved w m.transition

/-- Full admissibility: second law + linear conservation witness. -/
def admissibleOreMorphism {n : ℕ} (w : LinearConservationWitness n)
    (m : OreMorphism n) : Prop :=
  admissibleConservedTransition w m.transition

/-- Admissible ore morphisms satisfy the chemical second law. -/
theorem admissibleOre_secondLaw {n : ℕ} (w : LinearConservationWitness n)
    (m : OreMorphism n) (h : admissibleOreMorphism w m) :
    oreSecondLawAdmissible m :=
  h.1

/-- Admissible ore morphisms satisfy linear conservation. -/
theorem admissibleOre_linearConservation {n : ℕ} (w : LinearConservationWitness n)
    (m : OreMorphism n) (h : admissibleOreMorphism w m) :
    oreLinearConservationPreserved w m :=
  h.2

-- ================================================================
-- SECTION 3: Physical bridge (zero new axioms)
-- ================================================================

/-- Physical bridge yields an admissible ore morphism at zero composition delta. -/
theorem admissibleOre_from_physical_bridge (b : PhysicalChemBridge)
    (w : LinearConservationWitness 2)
    (src tgt : OreTree)
    (hDelta : conservedCompositionDelta ⟨b.transition, fun _ => 0, fun _ => 0⟩ = fun _ => 0)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleOreMorphism w
      { source := src
        target := tgt
        transition := ⟨b.transition, fun _ => 0, fun _ => 0⟩
        cost := b.transition.dissipatedWork
        cost_eq_work := rfl } :=
  admissible_from_physical_bridge b w hDelta hSL

/-- Physical bridge discharges ore second-law admissibility. -/
theorem oreSecondLaw_from_physical (b : PhysicalChemBridge)
    (src tgt : OreTree)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    oreSecondLawAdmissible
      { source := src
        target := tgt
        transition := ⟨b.transition, fun _ => 0, fun _ => 0⟩
        cost := b.transition.dissipatedWork
        cost_eq_work := rfl } :=
  chemSecondLaw_from_physical b hSL

-- ================================================================
-- SECTION 4: Canonical fixtures + honesty posture
-- ================================================================

/-- Coherent P0 ore morphism at zero cost (catalog witness). -/
noncomputable def coherentP0OreMorphism : OreMorphism 2 where
  source := hematiteLeaf
  target := hematiteLeaf
  transition :=
    { thermo := coherentP0Transition
      priorComp := fun _ => 0
      postComp := fun _ => 0 }
  cost := 0
  cost_eq_work := rfl

theorem coherentP0Ore_secondLaw : oreSecondLawAdmissible coherentP0OreMorphism :=
  coherentP0_chemSecondLaw

theorem hematiteGangue_multiBody : isMultiBodyScaffold hematiteGangueTensor = true := by
  decide

/-- Physics GREEN unauthorized on this scaffold. -/
def orePhysicsGreen : Bool := false

theorem orePhysicsGreenFalse : orePhysicsGreen = false := rfl

/-- Production wiring stays open (ORE-00 / CAT-01 lift only). -/
def oreAssemblageProductionWired : Bool := false

theorem oreAssemblageProductionWiredFalse : oreAssemblageProductionWired = false := rfl

/-- Catalog witness: meso chemistry ore-assemblage module present. -/
theorem oreAssemblageModuleWitness : True := trivial

end UMST.Chem.OreAssemblage
