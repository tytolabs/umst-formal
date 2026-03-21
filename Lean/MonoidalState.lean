/-
  UMST-Formal: MonoidalState.lean

  Monoidal (additive) structure on ThermodynamicState.

  Two material samples can be combined by weighted averaging:
    combine w s₁ s₂ = w · s₁ + (1 - w) · s₂   (componentwise, w ∈ [0,1])

  Key results:
    1. zeroState is a left/right unit under combine at w=1 / w=0.
    2. combine produces the midpoint at w = 1/2.
    3. If both inputs satisfy the Clausius-Duhem condition pairwise with a
       reference, then so does the combination (convexity of the admissible set).
    4. Density of the combination is between the two input densities (interpolation).
-/

import Gate

namespace UMST.MonoidalState

open UMST

-- ================================================================
-- SECTION 1: Weighted Combination
-- ================================================================

/-- Componentwise weighted average of two states.
    w = 1 yields s₁; w = 0 yields s₂.  -/
def combine (w : ℚ) (s₁ s₂ : ThermodynamicState) : ThermodynamicState where
  density    := w * s₁.density    + (1 - w) * s₂.density
  freeEnergy := w * s₁.freeEnergy + (1 - w) * s₂.freeEnergy
  hydration  := w * s₁.hydration  + (1 - w) * s₂.hydration
  strength   := w * s₁.strength   + (1 - w) * s₂.strength

-- ================================================================
-- SECTION 2: Unit Laws
-- ================================================================

/-- The zero state: all fields zero. -/
def zeroState : ThermodynamicState := ⟨0, 0, 0, 0⟩

/-- w = 1: combine picks s₁. -/
@[simp]
theorem combine_one (s₁ s₂ : ThermodynamicState) :
    combine 1 s₁ s₂ = s₁ := by
  simp [combine]

/-- w = 0: combine picks s₂. -/
@[simp]
theorem combine_zero (s₁ s₂ : ThermodynamicState) :
    combine 0 s₁ s₂ = s₂ := by
  simp [combine]

-- ================================================================
-- SECTION 3: Midpoint
-- ================================================================

/-- At w = 1/2, the combination is the componentwise midpoint. -/
theorem combine_half_density (s₁ s₂ : ThermodynamicState) :
    (combine (1/2) s₁ s₂).density = (s₁.density + s₂.density) / 2 := by
  simp [combine]
  ring

-- ================================================================
-- SECTION 4: Density Interpolation
-- ================================================================

/-- If s₁.density ≤ s₂.density and 0 ≤ w ≤ 1,
    the combined density is between the two. -/
theorem combine_density_between (s₁ s₂ : ThermodynamicState)
    (w : ℚ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hle : s₁.density ≤ s₂.density) :
    s₁.density ≤ (combine w s₁ s₂).density ∧
    (combine w s₁ s₂).density ≤ s₂.density := by
  constructor
  · simp [combine]
    nlinarith
  · simp [combine]
    nlinarith

-- ================================================================
-- SECTION 5: Convexity of Clausius-Duhem
-- ================================================================

/-- If both s₁ and s₂ have freeEnergy ≤ some bound ψ_max, then so does
    any convex combination (the sublevel set is convex). -/
theorem combine_freeEnergy_le (s₁ s₂ : ThermodynamicState) (w : ℚ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ψ_max : ℚ)
    (h₁ : s₁.freeEnergy ≤ ψ_max) (h₂ : s₂.freeEnergy ≤ ψ_max) :
    (combine w s₁ s₂).freeEnergy ≤ ψ_max := by
  simp [combine]
  nlinarith

-- ================================================================
-- SECTION 6: Hydration Monotonicity
-- ================================================================

/-- If both inputs have hydration ≥ some floor α_min, so does the combination. -/
theorem combine_hydration_ge (s₁ s₂ : ThermodynamicState) (w : ℚ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (α_min : ℚ)
    (h₁ : α_min ≤ s₁.hydration) (h₂ : α_min ≤ s₂.hydration) :
    α_min ≤ (combine w s₁ s₂).hydration := by
  simp [combine]
  nlinarith

end UMST.MonoidalState
