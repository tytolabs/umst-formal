/-
  UMST-Formal: EnrichedAdmissibility.lean
  Lean 4 — Enriched category structure of the admissibility relation.

  The admissibility relation has both:
  - A METRIC component (mass conservation: |ρ' - ρ| ≤ δMass)
  - An ORDER component (Clausius-Duhem, hydration, strength: each ≤)

  In categorical terms, the admissibility relation defines a category enriched
  over the Lawvere metric quantale ([0,∞], ≥, +). The mass component gives the
  "distance" between states; the order components give the "direction".

  This file formalises:
  1. The mass distance function (a pseudometric on states).
  2. The triangle inequality (justifying AdmissibleN composition).
  3. The order components are separately a preorder.
  4. The relationship between AdmissibleN and the metric + order structure.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.GaloisConnection
import Gate

namespace UMST

-- ================================================================
-- SECTION 1: Mass Pseudometric
-- ================================================================

/-- The mass distance between two states: |ρ' - ρ| (in ℚ). -/
def massDist (s₁ s₂ : ThermodynamicState) : ℚ :=
  |s₂.density - s₁.density|

/-- Mass distance is non-negative. -/
theorem massDist_nonneg (s₁ s₂ : ThermodynamicState) : 0 ≤ massDist s₁ s₂ :=
  abs_nonneg _

/-- Mass distance is zero for identical states. -/
theorem massDist_self (s : ThermodynamicState) : massDist s s = 0 := by
  simp [massDist, sub_self]

/-- Mass distance is symmetric. -/
theorem massDist_comm (s₁ s₂ : ThermodynamicState) :
    massDist s₁ s₂ = massDist s₂ s₁ := by
  simp [massDist, abs_sub_comm]

/-- **Triangle inequality** for mass distance.
    This is the key property that makes AdmissibleN composable. -/
theorem massDist_triangle (s₁ s₂ s₃ : ThermodynamicState) :
    massDist s₁ s₃ ≤ massDist s₁ s₂ + massDist s₂ s₃ := by
  unfold massDist
  have eq : s₃.density - s₁.density =
      (s₃.density - s₂.density) + (s₂.density - s₁.density) := by ring
  have htri := abs_add (s₃.density - s₂.density) (s₂.density - s₁.density)
  rw [eq]
  exact le_trans htri (le_of_eq (add_comm _ _))

/-- Mass condition is equivalent to mass distance being within tolerance. -/
theorem massCond_iff_massDist (old new : ThermodynamicState) :
    MassCond old new ↔ massDist old new ≤ δMass := by
  rfl

-- ================================================================
-- SECTION 2: Order Preorder (3 Conditions)
-- ================================================================

/-- The three order conditions together form a preorder on states. -/
structure OrderAdmissible (s₁ s₂ : ThermodynamicState) : Prop where
  clausiusDuhem : s₂.freeEnergy ≤ s₁.freeEnergy
  hydrationMono : s₁.hydration  ≤ s₂.hydration
  strengthMono  : s₁.strength   ≤ s₂.strength

/-- OrderAdmissible is reflexive. -/
theorem orderAdmissible_refl (s : ThermodynamicState) : OrderAdmissible s s :=
  ⟨le_refl _, le_refl _, le_refl _⟩

/-- OrderAdmissible is transitive (a preorder). -/
theorem orderAdmissible_trans {s₁ s₂ s₃ : ThermodynamicState}
    (h₁₂ : OrderAdmissible s₁ s₂) (h₂₃ : OrderAdmissible s₂ s₃) :
    OrderAdmissible s₁ s₃ :=
  ⟨le_trans h₂₃.clausiusDuhem h₁₂.clausiusDuhem,
   le_trans h₁₂.hydrationMono h₂₃.hydrationMono,
   le_trans h₁₂.strengthMono  h₂₃.strengthMono⟩

-- ================================================================
-- SECTION 3: Decomposition of AdmissibleN
-- ================================================================

/-- AdmissibleN decomposes into a metric component and an order component. -/
theorem admissibleN_decomp {n : ℕ} {old new : ThermodynamicState}
    (h : AdmissibleN n old new) :
    massDist old new ≤ (n : ℚ) * δMass ∧ OrderAdmissible old new :=
  ⟨h.massDensity, ⟨h.clausiusDuhem, h.hydrationMono, h.strengthMono⟩⟩

/-- Reconstruct AdmissibleN from its metric and order components. -/
theorem admissibleN_of_decomp {n : ℕ} {old new : ThermodynamicState}
    (hm : massDist old new ≤ (n : ℚ) * δMass)
    (ho : OrderAdmissible old new) :
    AdmissibleN n old new :=
  ⟨hm, ho.clausiusDuhem, ho.hydrationMono, ho.strengthMono⟩

/-- The order component of an admissible transition holds independently of n. -/
theorem admissibleN_order {n : ℕ} {s s' : ThermodynamicState}
    (h : AdmissibleN n s s') : OrderAdmissible s s' :=
  (admissibleN_decomp h).2

/-- Increasing the step budget preserves admissibility. -/
theorem admissibleN_mono {m n : ℕ} (hmn : m ≤ n)
    {old new : ThermodynamicState} (h : AdmissibleN m old new) :
    AdmissibleN n old new := by
  constructor
  · calc massDist old new ≤ (m : ℚ) * δMass := h.massDensity
      _ ≤ (n : ℚ) * δMass := by
            apply mul_le_mul_of_nonneg_right _ (by norm_num [δMass])
            exact_mod_cast hmn
  · exact h.clausiusDuhem
  · exact h.hydrationMono
  · exact h.strengthMono

-- ================================================================
-- SECTION 4: Lawvere Metric Interpretation
-- ================================================================

/-- The mass distance defines a Lawvere (generalised) metric on states.
    In a Lawvere metric space, composition corresponds to triangle inequality.
    The admissibleN_compose theorem (Gate.lean) is the composition law. -/
theorem lawvere_composition {m n : ℕ} {s s' s'' : ThermodynamicState}
    (hm : massDist s s'  ≤ (m : ℚ) * δMass)
    (hn : massDist s' s'' ≤ (n : ℚ) * δMass) :
    massDist s s'' ≤ ((m + n : ℕ) : ℚ) * δMass := by
  have cast_eq : ((m + n : ℕ) : ℚ) * δMass = (m : ℚ) * δMass + (n : ℚ) * δMass := by
    push_cast; ring
  rw [cast_eq]
  exact le_trans (massDist_triangle s s' s'') (add_le_add hm hn)

end UMST
