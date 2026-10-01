-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/KleisliInherit.lean

  Meso acting Urge — §17.3 Kleisli inheritance layer.
  `kleisli_compose_preserves_admissibility` and monad laws are inherited from
  `Compat.Constitutional`; Urge does not re-prove the admissibility monad.

  Anchored in `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Excitement selection is imported — no second argmin in this crate.
  Adds **zero** Lean `axiom` declarations.
-/

import Compat.Constitutional
import Excitement
import LandauerLaw
import Urge.AdmitKleisli

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.AdmitKleisli

namespace UMST.Urge.KleisliInherit

-- ================================================================
-- SECTION 1: Carriers (inherit from Constitutional / AdmitKleisli)
-- ================================================================

/-- Kleisli arrow over thermodynamic states (meso Urge carrier). -/
abbrev InheritArrow := KleisliArrow

/-- Kleisli identity on admitted history head states. -/
abbrev inheritIdentity := admitIdentity

/-- Kleisli composition (inherited bind). -/
abbrev inheritCompose := kleisliCompose

/-- Fold a non-empty Kleisli chain (inherited). -/
abbrev inheritFold := kleisliFold

-- ================================================================
-- SECTION 2: §17.3 compose-preserves-admissibility (inherited — not re-proved)
-- ================================================================

/-- Rust/blueprint name: graded Kleisli composition preserves gate admissibility. -/
theorem kleisli_compose_preserves_admissibility (m n : ℕ) (f g : InheritArrow)
    (hf : WellTypedN m f) (hg : WellTypedN n g) :
    WellTypedN (m + n) (inheritCompose f g) :=
  UMST.kleisliComposeWellTypedN m n f g hf hg

/-- Single-step compose preserves admissibility (2-step graded witness). -/
theorem kleisli_compose_preserves_admissibility_step (f g : InheritArrow)
    (hf : WellTyped f) (hg : WellTyped g) :
    WellTypedN 2 (inheritCompose f g) :=
  kleisliComposeWellTyped f g hf hg

/-- Fold of well-typed arrows preserves graded admissibility. -/
theorem kleisli_fold_preserves_admissibility (arrows : List InheritArrow)
    (hall : AllWellTyped arrows) :
    WellTypedN arrows.length (inheritFold arrows) :=
  kleisliFoldWellTypedN arrows hall

/-- Pointwise compose preservation at successful witnesses. -/
theorem kleisli_compose_preserves_admissibility_at (f g : InheritArrow)
    (hf : WellTyped f) (hg : WellTyped g)
    (s s' s'' : ThermodynamicState) (hfs : f s = some s') (hcs : inheritCompose f g s = some s'') :
    Admissible s s' ∧ Admissible s' s'' := by
  refine ⟨(hf s s' hfs), ?_⟩
  have hg' : g s' = some s'' := by
    simpa [inheritCompose, UMST.kleisliCompose, hfs] using hcs
  exact hg s' s'' hg'

-- ================================================================
-- SECTION 3: Monad laws (inherited — cite only, do not re-derive)
-- ================================================================

/-- Associativity (inherited from `Compat.Constitutional`). -/
theorem kleisli_associativity_inherited (f g h : InheritArrow) :
    inheritCompose (inheritCompose f g) h = inheritCompose f (inheritCompose g h) :=
  UMST.kleisliComposeAssoc f g h

/-- Left unit (inherited). -/
theorem kleisli_left_unit_inherited (f : InheritArrow) :
    inheritCompose inheritIdentity f = f :=
  UMST.kleisliLeftUnit f

/-- Right unit (inherited). -/
theorem kleisli_right_unit_inherited (f : InheritArrow) :
    inheritCompose f inheritIdentity = f :=
  UMST.kleisliRightUnit f

/-- Rust parity probe: associativity inherited, not re-proved here. -/
def kleisli_associativity_probe_holds : Bool := true

end UMST.Urge.KleisliInherit
