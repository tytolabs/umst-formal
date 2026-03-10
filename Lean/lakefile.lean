import Lake
open Lake DSL

package «umst-formal» where
  name := "umst-formal"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

/-
  Module registration.  All six Lean 4 modules mirror the corresponding
  Agda modules 1:1.  Each module is separately checkable:
    lake build UMST.Gate           -- core admissibility predicate
    lake build UMST.Helmholtz      -- concrete free-energy model + SDF
    lake build UMST.Constitutional -- Kleisli machinery + Subject Reduction
    lake build UMST.Naturality     -- natural transformation + material class
    lake build UMST.Activation     -- engine activation profiles (sheaf section)
    lake build UMST.DIBKleisli     -- Discovery-Invention-Build monad
-/
lean_lib «UMST» where
  roots := #[`Gate, `Helmholtz, `Constitutional, `Naturality, `Activation, `DIBKleisli]
  srcDir := "."
