/-
  UMST-Formal: Economic/PhysicsConstrainedAI.lean

  **Propose → gate:** any proposal functor composed with `makeGateArrow` is `WellTyped`.
  “Sandbox” = arbitrary `propose`; “output” = gate-mediated arrow only.
-/

import Constitutional

namespace UMST.Economics

open UMST

/-- Gated pipeline is 1-step well-typed (constitutional Kleisli). -/
theorem physicsConstrained_gate_wellTyped (propose : ThermodynamicState → ThermodynamicState) :
    WellTyped (makeGateArrow propose) :=
  gateArrowWellTyped propose

end UMST.Economics
