/-
  UMST-Formal: Economic/KleisliAdmissibilityComposition.lean

  Re-export graded Kleisli safety as the Economic-layer **composition** API (no duplication).
-/

import Constitutional

namespace UMST.Economics

open UMST

/-- Graded composition of well-typed Kleisli arrows (m + n steps). -/
theorem econ_kleisliComposeWellTypedN (m n : ℕ) (f g : KleisliArrow)
    (hf : WellTypedN m f) (hg : WellTypedN n g) :
    WellTypedN (m + n) (kleisliCompose f g) :=
  kleisliComposeWellTypedN m n f g hf hg

/-- Fold of a list of 1-step well-typed arrows is `WellTypedN (length)` . -/
theorem econ_kleisliFoldWellTypedN (arrows : List KleisliArrow) (hall : AllWellTyped arrows) :
    WellTypedN arrows.length (kleisliFold arrows) :=
  kleisliFoldWellTypedN arrows hall

end UMST.Economics
