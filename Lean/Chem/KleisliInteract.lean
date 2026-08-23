-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/KleisliInteract.lean

  Meso acting chemistry — Kleisli @Interact@ morphism laws over cement `ThermodynamicState`.
  Mirrors `Haskell/UMST/Chem/Kleisli.hs` and `Agda/Chem/KleisliInteract.agda` on
  `umst-formal/meso_acting`: identity / associativity / unit coherence, graded gate admissibility.

  Anchored in `LandauerLaw.physicalSecondLaw` via `Chem.SecondLaw` + `Chem.Conservation`.
  Adds **zero** Lean `axiom` declarations.
-/

import Chem.Conservation
import Compat.Constitutional
import LandauerLaw

open Real Finset UMST UMST.LandauerLaw UMST.Chem.SecondLaw UMST.Chem.Conservation

namespace UMST.Chem.KleisliInteract

-- ================================================================
-- SECTION 1: Carriers + gate admissibility (meso acting layer)
-- ================================================================

/-- Kleisli arrow over thermodynamic states (meso acting carrier). -/
abbrev KleisliArrow := UMST.KleisliArrow

/-- Single-step gate admissibility (lifts `gateCheck` / Agda `Admissible`). -/
def admissibleStep (old new : ThermodynamicState) : Prop :=
  Admissible old new

/-- Well-typed at a witness pair: successful output implies admissible step. -/
def wellTypedAt (f : KleisliArrow) (s s' : ThermodynamicState) : Prop :=
  f s = some s' ∧ admissibleStep s s'

/-- Gate-checked Kleisli arrow from a state proposal. -/
abbrev makeGateArrow := UMST.makeGateArrow

/-- Every successful `makeGateArrow` step is admissible. -/
theorem gateArrowWellTyped (propose : ThermodynamicState → ThermodynamicState) :
    WellTyped (makeGateArrow propose) :=
  UMST.gateArrowWellTyped propose

-- ================================================================
-- SECTION 2: Kleisli algebra (identity / compose / fold)
-- ================================================================

/-- Kleisli identity (refuse ill-typed identity-cost propagation). -/
def interactIdentity : KleisliArrow := fun s => some s

/-- Kleisli composition. -/
abbrev kleisliCompose := UMST.kleisliCompose

/-- Fold a non-empty Kleisli chain. -/
abbrev kleisliFold := UMST.kleisliFold

-- ================================================================
-- SECTION 3: Laws (identity / assoc / coherence)
-- ================================================================

/-- Pointwise associativity (Agda `kleisli-compose-assoc`). -/
theorem kleisliComposeAssocAt (f g h : KleisliArrow) (s : ThermodynamicState) :
    kleisliCompose (kleisliCompose f g) h s = kleisliCompose f (kleisliCompose g h) s := by
  simpa using congrArg (fun k => k s) (UMST.kleisliComposeAssoc f g h)

/-- Global associativity. -/
theorem kleisliComposeAssoc (f g h : KleisliArrow) :
    kleisliCompose (kleisliCompose f g) h = kleisliCompose f (kleisliCompose g h) :=
  UMST.kleisliComposeAssoc f g h

/-- Left unit law at a state. -/
theorem kleisliLeftUnitAt (f : KleisliArrow) (s : ThermodynamicState) :
    kleisliCompose interactIdentity f s = f s := by
  simpa [interactIdentity] using congrArg (fun k => k s) (UMST.kleisliLeftUnit f)

/-- Left unit law. -/
theorem kleisliLeftUnit (f : KleisliArrow) :
    kleisliCompose interactIdentity f = f := by
  funext s; exact kleisliLeftUnitAt f s

/-- Right unit law at a state. -/
theorem kleisliRightUnitAt (f : KleisliArrow) (s : ThermodynamicState) :
    kleisliCompose f interactIdentity s = f s := by
  simpa [interactIdentity] using congrArg (fun k => k s) (UMST.kleisliRightUnit f)

/-- Right unit law. -/
theorem kleisliRightUnit (f : KleisliArrow) :
    kleisliCompose f interactIdentity = f := by
  funext s; exact kleisliRightUnitAt f s

/-- Composition preserves admissibility when both legs succeed admissibly. -/
theorem kleisliComposeWellTypedAt (f g : KleisliArrow) (hf : WellTyped f) (hg : WellTyped g)
    (s s' s'' : ThermodynamicState) (hfs : f s = some s') (hcs : kleisliCompose f g s = some s'') :
    admissibleStep s s' ∧ admissibleStep s' s'' := by
  refine ⟨hf s s' hfs, ?_⟩
  have hg' : g s' = some s'' := by
    simpa [UMST.kleisliCompose, hfs] using hcs
  exact hg s' s'' hg'

/-- Left and right units agree on endpoints when both compose (Coq coherence). -/
theorem kleisliCoherenceUnits (f : KleisliArrow) (s g h : ThermodynamicState)
    (hleft : kleisliCompose interactIdentity f s = some g)
    (hright : kleisliCompose f interactIdentity s = some h) :
    g = h := by
  have hfl : f s = some g := by
    unfold kleisliCompose interactIdentity at hleft
    simpa using hleft
  simpa [UMST.kleisliCompose, interactIdentity, hfl] using hright

/-- Graded composition preserves well-typing. -/
theorem kleisliComposeWellTypedN (m n : ℕ) (f g : KleisliArrow)
    (hf : WellTypedN m f) (hg : WellTypedN n g) :
    WellTypedN (m + n) (kleisliCompose f g) :=
  UMST.kleisliComposeWellTypedN m n f g hf hg

/-- Fold of well-typed arrows is graded well-typed. -/
theorem kleisliFoldWellTypedN (arrows : List KleisliArrow) (hall : AllWellTyped arrows) :
    WellTypedN arrows.length (kleisliFold arrows) :=
  UMST.kleisliFoldWellTypedN arrows hall

-- ================================================================
-- SECTION 4: Meso acting bridge (second law + conservation spine)
-- ================================================================

/-- `physicalSecondLaw` discharges chemical second-law admissibility on bridged erasures. -/
theorem interact_chemSecondLaw_from_physical (b : PhysicalChemBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    chemSecondLaw b.transition :=
  chemSecondLaw_from_physical b hSL

/-- Physically bridged transition satisfies conserved admissibility at zero composition delta. -/
theorem interact_admissibleConserved_from_physical (b : PhysicalChemBridge)
    (w : LinearConservationWitness 2)
    (hDelta : conservedCompositionDelta ⟨b.transition, fun _ => 0, fun _ => 0⟩ = fun _ => 0)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleConservedTransition w ⟨b.transition, fun _ => 0, fun _ => 0⟩ :=
  admissible_from_physical_bridge b w hDelta hSL

/-- Physics GREEN unauthorized on this scaffold. -/
def chemPhysicsGreen : Bool := false

theorem chemPhysicsGreenFalse : chemPhysicsGreen = false := rfl

/-- Production wiring stays open (CAT-00 lift only). -/
def kleisliInteractProductionWired : Bool := false

theorem kleisliInteractProductionWiredFalse : kleisliInteractProductionWired = false := rfl

/-- Catalog witness: meso chemistry Kleisli Interact module present. -/
theorem kleisliInteractModuleWitness : True := trivial

end UMST.Chem.KleisliInteract
