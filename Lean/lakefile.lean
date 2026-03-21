import Lake
open Lake DSL

package «umst-formal» where
  -- Package name is provided by the quoted identifier above.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

/-
  Module registration.  Core six Lean roots mirror the corresponding Agda modules 1:1.  A seventh root,
  `LandauerEinsteinBridge`, is the SI Landauer-scale + `E = mc²` mass equivalent
  (Mathlib `log 2` bounds).  Each module is separately checkable:
    lake build UMST.Gate                        -- core admissibility predicate + AdmissibleN
    lake build UMST.Helmholtz                   -- concrete free-energy model + SDF
    lake build UMST.Constitutional              -- Kleisli machinery (graded, no admissibleTrans)
    lake build UMST.Naturality                  -- natural transformation + material class
    lake build UMST.Activation                  -- engine activation profiles (sheaf section)
    lake build UMST.DIBKleisli                  -- Discovery-Invention-Build monad
    lake build UMST.LandauerEinsteinBridge      -- SI + 300 K mass-equivalent brackets
    lake build UMST.GraphProperties             -- mass non-transitivity, DAG properties
    lake build UMST.Powers                      -- Powers gel-space ratio model + witness
    lake build UMST.Convergence                 -- hydration convergence + Lyapunov
    lake build UMST.GaloisGate                  -- Galois connection for gate conditions
    lake build UMST.EnrichedAdmissibility       -- Lawvere metric + order decomposition
    lake build UMST.LandauerLaw                 -- T_LandauerLaw: Landauer bound (axiom: physicalSecondLaw)
    lake build UMST.InfoTheory                  -- joint Shannon entropy + mutual information (finite)
-/
lean_lib «UMST» where
  roots := #[`Gate, `Helmholtz, `Constitutional, `Naturality, `Activation, `DIBKleisli,
    `LandauerEinsteinBridge, `GraphProperties, `Powers, `Convergence,
    `GaloisGate, `EnrichedAdmissibility, `LandauerLaw, `InfoTheory,
    `EndConditions, `MeasurementCost, `LandauerExtension, `FiberedActivation, `MonoidalState]
  srcDir := "."
