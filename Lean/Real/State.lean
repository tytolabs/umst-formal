/-
  UMST.Real.State — continuous ℝ thermodynamic scaffold (quantum cartridge analogue).
-/
import Core.State

namespace UMST.Real

/-- Continuous thermodynamic state: density and free energy over `ℝ`. -/
structure RealThermodynamicState where
  density    : ℝ
  freeEnergy : ℝ

noncomputable instance : UMST.Core.ThermodynamicSystem ℝ RealThermodynamicState where
  density s    := s.density
  freeEnergy s := s.freeEnergy

end UMST.Real
