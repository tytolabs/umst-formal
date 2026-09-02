-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

/-
  UMST-Formal meso/acting — EgoffHarnessAdversarial
  Adversarial drift refusal: sole axiom count = 1; physics_green false; EGOFF_SIDECAR_MODEL pin.
  Zero sorry. Not wired in umst-chem lib.rs.
-/
namespace UMST.Chem.Constants.EgoffHarnessAdversarial

def soleAxiomCount : Nat := 1
theorem sole_axiom_count_eq_one : soleAxiomCount = 1 := rfl
def physicsGreen : Bool := false
def sidecarModelPin : String := "EGOFF_SIDECAR_MODEL"
def harnessDriftForbidden : Bool := true

theorem refuse_second_axiom : soleAxiomCount ≠ 2 := by decide

end UMST.Chem.Constants.EgoffHarnessAdversarial
