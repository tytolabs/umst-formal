-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: Coordination/AgentColimit.lean

  Agents as observation maps on a world, and the gluing of two agents (H-COLIMIT-1, W-30).

  An agent observes a world `W` through a map `a : W → α`. Agent `c` *knows* agent `a` when `c`'s
  observation determines `a`'s: equal `c`-readings give equal `a`-readings. Knowing is a preorder; its
  arrows run from the agent that knows more to the agent it knows.

  The glued agent observes the pair `w ↦ (a w, b w)`. It knows `a` and `b`, and every agent that knows
  both knows it (`glue_universal`, `knows_glue_iff`): the glued agent is the join of `a` and `b` in the
  information order, the colimit of the discrete diagram {a, b} in the thin category of agents ordered by
  "is known by". On partitions of the world the same statement reads: the kernel of the glued map is the
  meet of the two kernels (`ker_glue`, Mathlib's `Setoid` lattice; `ker_glue_iff` pointwise).

  Every map out of the world also factors: `c` knows `a` exactly when `a = f ∘ c` for some `f`
  (`knows_iff_factors`), so the knowledge preorder is the thin reflection of the coslice under `W`, in
  which the glued agent with its two projections is the product.

  The pushout of the span `a ← (common knowledge) → b` in `FintypeCat`, with the Gács–Körner common part
  as its apex, is the follow-up cell FORMAL-AGENT-PUSHOUT-FINTYPECAT. The coordination saving on
  `SecondLaw (.erase _) (.transformation _ _)` (erasing the glued record costs I(A:B) less than erasing
  the two records apart) is the cell FORMAL-COORDINATION-SAVING.
  No `axiom`, no `sorry`.
-/

import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Function.Basic

namespace UMST.Coordination

universe u v w x

variable {W : Type u} {α : Type v} {β : Type w} {γ : Type x}

/-- Agent `c` knows agent `a`: `c`'s observation of the world determines `a`'s. -/
def Knows (c : W → γ) (a : W → α) : Prop :=
  ∀ w w', c w = c w' → a w = a w'

/-- The glued agent observes both readings at once. -/
def glue (a : W → α) (b : W → β) : W → α × β :=
  fun w => (a w, b w)

theorem knows_refl (a : W → α) : Knows a a :=
  fun _ _ h => h

theorem knows_trans {δ : Type*} {c : W → γ} {b : W → β} {a : W → δ}
    (h₁ : Knows c b) (h₂ : Knows b a) : Knows c a :=
  fun w w' h => h₂ w w' (h₁ w w' h)

/-- The glued agent knows the first agent. -/
theorem glue_knows_left (a : W → α) (b : W → β) : Knows (glue a b) a :=
  fun _ _ h => congrArg Prod.fst h

/-- The glued agent knows the second agent. -/
theorem glue_knows_right (a : W → α) (b : W → β) : Knows (glue a b) b :=
  fun _ _ h => congrArg Prod.snd h

/-- Universal property: an agent that knows both agents knows the glued agent. -/
theorem glue_universal {c : W → γ} {a : W → α} {b : W → β}
    (ha : Knows c a) (hb : Knows c b) : Knows c (glue a b) :=
  fun w w' h => Prod.ext (ha w w' h) (hb w w' h)

/-- The glued agent is the join of `a` and `b` in the information order (the colimit of the
    two-object discrete diagram in the thin category of agents): `c` knows it iff `c` knows both. -/
theorem knows_glue_iff (c : W → γ) (a : W → α) (b : W → β) :
    Knows c (glue a b) ↔ Knows c a ∧ Knows c b :=
  ⟨fun h => ⟨knows_trans h (glue_knows_left a b), knows_trans h (glue_knows_right a b)⟩,
   fun h => glue_universal h.1 h.2⟩

/-- A factorisation through `c` makes `c` know `a`. -/
theorem factors_knows (c : W → γ) (a : W → α) (f : γ → α) (hf : ∀ w, a w = f (c w)) :
    Knows c a := by
  intro w w' h
  rw [hf w, hf w', h]

/-- Knowing is factoring: `c` knows `a` iff `a` is `c` followed by a map (a morphism `c → a` of the
    coslice under `W`). -/
theorem knows_iff_factors [Nonempty α] (c : W → γ) (a : W → α) :
    Knows c a ↔ ∃ f : γ → α, ∀ w, a w = f (c w) := by
  classical
  constructor
  · intro h
    refine ⟨fun g => if hg : ∃ w, c w = g then a (Classical.choose hg) else Classical.arbitrary α, ?_⟩
    intro w
    have hw : ∃ w', c w' = c w := ⟨w, rfl⟩
    simp only [hw, dif_pos]
    exact h w (Classical.choose hw) (Classical.choose_spec hw).symm
  · rintro ⟨f, hf⟩ w w' h
    rw [hf w, hf w', h]

/-- `Knows` is the reverse inclusion of kernels: `c` knows `a` iff `ker c ≤ ker a` in `Setoid W`. -/
theorem knows_iff_ker_le (c : W → γ) (a : W → α) :
    Knows c a ↔ Setoid.ker c ≤ Setoid.ker a := by
  rw [Setoid.le_def]
  constructor
  · intro h x y hxy
    exact Setoid.ker_def.mpr (h x y (Setoid.ker_def.mp hxy))
  · intro h x y hxy
    exact Setoid.ker_def.mp (h (Setoid.ker_def.mpr hxy))

/-- The kernel of the glued agent at a pair of worlds: the glued readings agree exactly when both
    readings agree (pointwise form of `ker_glue`, the statement the Coq, Agda and Haskell twins carry). -/
theorem ker_glue_iff (a : W → α) (b : W → β) (x y : W) :
    glue a b x = glue a b y ↔ a x = a y ∧ b x = b y :=
  Prod.ext_iff

/-- The partition of the glued agent is the meet of the two partitions. -/
theorem ker_glue (a : W → α) (b : W → β) :
    Setoid.ker (glue a b) = Setoid.ker a ⊓ Setoid.ker b := by
  ext x y
  rw [Setoid.inf_iff_and, Setoid.ker_def, Setoid.ker_def, Setoid.ker_def]
  exact ker_glue_iff a b x y

end UMST.Coordination
