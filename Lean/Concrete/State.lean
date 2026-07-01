/-
  UMST.Concrete.State — cementitious (OPC) thermodynamic state.
-/

import Core.State

namespace UMST.Concrete

/-- Portland-cement material state: ρ, ψ, α, fc (all ℚ). -/
structure ConcreteState where
  density     : ℚ
  freeEnergy  : ℚ
  hydration   : ℚ
  strength    : ℚ
  deriving Repr

instance : UMST.Core.ThermodynamicSystem ℚ ConcreteState where
  density s    := s.density
  freeEnergy s := s.freeEnergy

end UMST.Concrete
