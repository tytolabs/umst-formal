/-
  UMST-Formal: FiberedActivation.lean

  Fiber-bundle view of the `Activation` map.

  For each engine e, the "fiber" is the set of materials that activate e.
  Key results: fiber non-emptiness, universality of Strength/Rheology,
  activation has ≥ 2 engines per material, fiber covering, characteristic
  engines.
-/

import Activation

namespace UMST.FiberedActivation

open UMST MaterialClass Engine

-- ================================================================
-- SECTION 1: Engine Fibers
-- ================================================================

/-- The fiber of materials that activate engine e. -/
def engineFiber (e : Engine) (M : MaterialClass) : Prop :=
  e ∈ₑ activation M

-- ================================================================
-- SECTION 2: Fiber Non-Emptiness
-- ================================================================

/-- Every engine is activated by at least one material. -/
theorem engineFiber_nonempty (e : Engine) : ∃ M, engineFiber e M := by
  cases e with
  | Hydration        => exact ⟨OPC, rfl⟩
  | AlkaliActivation => exact ⟨Geopolymer, rfl⟩
  | Carbonation      => exact ⟨Lime, rfl⟩
  | MoistureSorption => exact ⟨Earth, rfl⟩
  | Strength         => exact ⟨OPC, rfl⟩
  | Rheology         => exact ⟨OPC, rfl⟩
  | Thermal          => exact ⟨OPC, rfl⟩
  | Transport        => exact ⟨RAC, rfl⟩

-- ================================================================
-- SECTION 3: Universal Engines
-- ================================================================

/-- Strength is activated by every material class. -/
theorem strength_universal (M : MaterialClass) : engineFiber Strength M := by
  cases M <;> rfl

/-- Rheology is activated by every material class. -/
theorem rheology_universal (M : MaterialClass) : engineFiber Rheology M := by
  cases M <;> rfl

-- ================================================================
-- SECTION 4: Activation Cardinality (≥ 2 engines per material)
-- ================================================================

/-- Every material activates at least Strength AND Rheology. -/
theorem activation_at_least_two (M : MaterialClass) :
    engineFiber Strength M ∧ engineFiber Rheology M := by
  exact ⟨strength_universal M, rheology_universal M⟩

-- ================================================================
-- SECTION 5: Fiber Covering
-- ================================================================

/-- Every material is in the fiber of some engine. -/
theorem fiber_covers (M : MaterialClass) : ∃ e, engineFiber e M :=
  activationTotal M

-- ================================================================
-- SECTION 6: Characteristic Engines
-- ================================================================

/-- Hydration is characteristic for OPC / RAC (not active in Lime / Earth). -/
theorem hydration_not_lime : ¬ engineFiber Hydration Lime :=
  lime_no_hydration

theorem hydration_not_earth : ¬ engineFiber Hydration Earth :=
  earth_no_hydration

/-- Transport is characteristic for RAC (not active in OPC). -/
theorem transport_not_opc : ¬ engineFiber Transport OPC :=
  opc_no_transport

end UMST.FiberedActivation
