-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: UnfoldKleisli.lean

  The laws the nested-solve composition of `umst-math` (`solve_combinator.rs`, `Thermo::bind`; cell
  UNFOLD-KLEISLI-COMPOSE) relies on, as instances of the one inequality of `OneInequalitySecondLaw` and the erase case
  of `SecondLaw`. A nested solve returns a refusal or a value with the spend that produced it,
  `Thermo ε α A = Except ε (A × Spend α)`, where a spend pairs the measured energy with the Landauer floor of the bits
  the solve erased.

  * **L1 Kleisli.** `bind` has `unit` as left and right identity and is associative (`unit_bind`, `bind_unit`,
    `bind_assoc`); so is Kleisli composition (`kcomp_assoc`). A refusal of an inner solve is the outer solve's refusal
    (`bind_inner_refusal`), and an outer solve's spend is the sum of its inner spends (`bind_spend`).
  * **L2 Grading.** Spends form a commutative monoid under componentwise addition (`Spend.add_assoc`,
    `Spend.zero_add`, `Spend.add_zero`, `Spend.add_comm`); a spend is honest when its measured energy is at least its
    floor, honesty is closed under addition (`Spend.honest_add`), so the sum of measured energies is at least the sum of
    floors under any nesting (`honest_sum`, `bind_honest`). Honesty is the one inequality with ΔF the floor, W_in the
    measured energy and no information term (`Spend.honest_iff_oneInequality`), and spend addition is the chaining of
    steps (`Spend.toStep_add`), so `honest_add_of_chain` is `oneInequality_chain`. An erasure that obeys the erase case
    of `SecondLaw` posts an honest spend (`landauerSpend_honest`), and nested solves whose spends are such erasures
    post an honest total (`bind_honest_of_secondLaw`).
  * **Error propagation over rational intervals.** Interval addition encloses sums (`Interval.mem_add`); the errors of
    nested solves, each within its tolerance, sum within the summed tolerance (`mem_sum_sym`); an inner error within
    `τ_in`, propagated through a map that is `L`-Lipschitz on that enclosure, and an outer error within `τ_out` leave the
    composite within `τ_out + L τ_in` (`error_chain`).

  Zero `axiom`, zero `sorry`.
-/

import CostOfInformation
import OneInequalitySecondLaw

open Real UMST.LandauerLaw UMST.ProcessFamily UMST.OneInequalitySecondLaw

namespace UMST.UnfoldKleisli

/-- The spend a solve posts: the measured energy and the Landauer floor of the bits it erased. -/
@[ext]
structure Spend (α : Type) where
  measured : α
  floor : α

namespace Spend

section Monoid

variable {α : Type} [AddCommMonoid α]

/-- The empty spend. -/
def zero : Spend α := ⟨0, 0⟩

/-- Spends add componentwise (sequential and parallel composition alike). -/
def add (s t : Spend α) : Spend α := ⟨s.measured + t.measured, s.floor + t.floor⟩

theorem add_assoc (s t u : Spend α) : (s.add t).add u = s.add (t.add u) := by
  ext <;> simp [add, _root_.add_assoc]

theorem zero_add (s : Spend α) : zero.add s = s := by
  ext <;> simp [add, zero]

theorem add_zero (s : Spend α) : s.add zero = s := by
  ext <;> simp [add, zero]

theorem add_comm (s t : Spend α) : s.add t = t.add s := by
  ext <;> simp [add, _root_.add_comm]

end Monoid

section Order

variable {α : Type} [LinearOrderedField α]

/-- A spend is honest when its measured energy is at least its floor. -/
def Honest (s : Spend α) : Prop := s.floor ≤ s.measured

theorem honest_zero : (zero : Spend α).Honest := le_refl _

/-- **L2**: honesty is closed under addition. -/
theorem honest_add {s t : Spend α} (hs : s.Honest) (ht : t.Honest) : (s.add t).Honest :=
  add_le_add hs ht

end Order

/-- A spend at a bath as one step of the one inequality: ΔF the floor, W_in the measured energy, no information. -/
def toStep (b : HeatBath) (s : Spend ℝ) : Step := ⟨b, s.floor, s.measured, 0⟩

/-- Honesty is the one inequality of the spend's step. -/
theorem honest_iff_oneInequality (b : HeatBath) (s : Spend ℝ) : s.Honest ↔ oneInequality (toStep b s) := by
  simp [Honest, oneInequality, toStep]

/-- Spend addition is the chaining of steps at one bath. -/
theorem toStep_add (b : HeatBath) (s t : Spend ℝ) : toStep b (s.add t) = (toStep b s).chain (toStep b t) rfl := by
  simp [toStep, add, Step.chain]

/-- **L2 from the chaining lemma**: honest spends add to an honest spend because admissible steps chain. -/
theorem honest_add_of_chain (b : HeatBath) {s t : Spend ℝ} (hs : s.Honest) (ht : t.Honest) : (s.add t).Honest := by
  rw [honest_iff_oneInequality b, toStep_add]
  exact oneInequality_chain (toStep b s) (toStep b t) rfl ((honest_iff_oneInequality b s).1 hs)
    ((honest_iff_oneInequality b t).1 ht)

end Spend

open Spend

section Kleisli

variable {ε α A B C : Type} [AddCommMonoid α]

/-- A nested solve: a refusal, or a value with the spend that produced it. -/
abbrev Thermo (ε α A : Type) := Except ε (A × Spend α)

/-- The monad unit: a value at no spend. -/
def unit (a : A) : Thermo ε α A := .ok (a, Spend.zero)

/-- Kleisli bind: run the inner solve, then the outer one on its value; a refusal stops the chain, spends add. -/
def bind (m : Thermo ε α A) (f : A → Thermo ε α B) : Thermo ε α B :=
  match m with
  | .error e => .error e
  | .ok (a, s) =>
    match f a with
    | .error e => .error e
    | .ok (b, t) => .ok (b, s.add t)

/-- Kleisli composition of nested solves. -/
def kcomp (f : A → Thermo ε α B) (g : B → Thermo ε α C) : A → Thermo ε α C := fun a => bind (f a) g

/-- **L1** left identity. -/
theorem unit_bind (a : A) (f : A → Thermo ε α B) : bind (unit a) f = f a := by
  rcases h : f a with e | ⟨b, t⟩
  · simp [bind, unit, h]
  · simp [bind, unit, h, Spend.zero_add]

/-- **L1** right identity. -/
theorem bind_unit (m : Thermo ε α A) : bind m unit = m := by
  rcases m with e | ⟨a, s⟩
  · rfl
  · simp [bind, unit, Spend.add_zero]

/-- **L1** associativity. -/
theorem bind_assoc (m : Thermo ε α A) (f : A → Thermo ε α B) (g : B → Thermo ε α C) :
    bind (bind m f) g = bind m (fun a => bind (f a) g) := by
  rcases m with e | ⟨a, s⟩
  · rfl
  · simp only [bind]
    rcases f a with e | ⟨b, t⟩
    · rfl
    · simp only
      rcases g b with e | ⟨c, u⟩
      · rfl
      · simp [Spend.add_assoc]

/-- **L1** Kleisli composition is associative. -/
theorem kcomp_assoc (f : A → Thermo ε α B) (g : B → Thermo ε α C) {D : Type} (h : C → Thermo ε α D) :
    kcomp (kcomp f g) h = kcomp f (kcomp g h) := by
  funext a
  exact bind_assoc (f a) g h

/-- A refusal of an inner solve is the outer solve's refusal. -/
theorem bind_inner_refusal {m : Thermo ε α A} {f : A → Thermo ε α B} {a : A} {s : Spend α} {e : ε}
    (hm : m = .ok (a, s)) (hf : f a = .error e) : bind m f = .error e := by
  subst hm
  simp [bind, hf]

/-- A refused first solve refuses the chain. -/
theorem bind_error (e : ε) (f : A → Thermo ε α B) : bind (.error e) f = .error e := rfl

/-- An outer solve's spend is the sum of its inner spends. -/
theorem bind_spend {m : Thermo ε α A} {f : A → Thermo ε α B} {b : B} {u : Spend α}
    (h : bind m f = .ok (b, u)) : ∃ a s t, m = .ok (a, s) ∧ f a = .ok (b, t) ∧ u = s.add t := by
  rcases m with e | ⟨a, s⟩
  · simp [bind] at h
  · simp only [bind] at h
    rcases hfa : f a with e | ⟨b', t⟩
    · rw [hfa] at h; simp at h
    · rw [hfa] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨a, s, t, rfl, hfa, rfl⟩

end Kleisli

section Grading

variable {ε α A B : Type} [LinearOrderedField α]

/-- Every spend a solve can post is honest. -/
def HonestT (m : Thermo ε α A) : Prop := ∀ a s, m = .ok (a, s) → s.Honest

/-- **L2** under nesting: honest inner solves bind to an honest outer solve. -/
theorem bind_honest {m : Thermo ε α A} {f : A → Thermo ε α B} (hm : HonestT m) (hf : ∀ a, HonestT (f a)) :
    HonestT (bind m f) := by
  intro b u h
  obtain ⟨a, s, t, hma, hfa, rfl⟩ := bind_spend h
  exact honest_add (hm a s hma) (hf a b t hfa)

/-- **L2** for any list of spends: the sum of measured energies is at least the sum of floors. -/
theorem honest_sum (l : List (Spend α)) (h : ∀ s ∈ l, s.Honest) : (l.foldr Spend.add Spend.zero).Honest := by
  induction l with
  | nil => exact honest_zero
  | cons s l ih =>
    exact honest_add (h s (List.mem_cons_self s l)) (ih fun t ht => h t (List.mem_cons_of_mem s ht))

end Grading

section SecondLawBridge

/-- The spend of an erasure of `bits` bits at the bath `b` with work `W`: measured `k_B W`, floor
    `bits · k_B T ln 2`. -/
noncomputable def landauerSpend (b : HeatBath) (W : ℝ) (bits : ℕ) : Spend ℝ :=
  ⟨kB * W, bits * (kB * b.bathTemp.val * log 2)⟩

/-- An erasure obeying the erase case of `SecondLaw` posts an honest spend. -/
theorem landauerSpend_honest (b : HeatBath) (W : ℝ) (bits : ℕ)
    (h : SecondLaw (.erase ⟨b, W⟩)
      (.transformation (uniformDist (2 ^ bits) (pow_pos two_pos bits)) (diracDist (0 : Fin (2 ^ bits))))) :
    (landauerSpend b W bits).Honest :=
  UMST.CostOfInformation.bitErasure_cost b W bits h

/-- Nested solves whose spends are erasures obeying the erase case of `SecondLaw` post an honest total. -/
theorem bind_honest_of_secondLaw {ε A B : Type} (b : HeatBath) (W₁ W₂ : ℝ) (n₁ n₂ : ℕ) (a : A) (y : B)
    (h₁ : SecondLaw (.erase ⟨b, W₁⟩)
      (.transformation (uniformDist (2 ^ n₁) (pow_pos two_pos n₁)) (diracDist (0 : Fin (2 ^ n₁)))))
    (h₂ : SecondLaw (.erase ⟨b, W₂⟩)
      (.transformation (uniformDist (2 ^ n₂) (pow_pos two_pos n₂)) (diracDist (0 : Fin (2 ^ n₂))))) :
    HonestT (bind (Except.ok (a, landauerSpend b W₁ n₁) : Thermo ε ℝ A)
      (fun _ => (Except.ok (y, landauerSpend b W₂ n₂) : Thermo ε ℝ B))) := by
  apply bind_honest
  · intro a' s hs
    simp only [Except.ok.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact landauerSpend_honest b W₁ n₁ h₁
  · intro _ b' t ht
    simp only [Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨-, rfl⟩ := ht
    exact landauerSpend_honest b W₂ n₂ h₂

end SecondLawBridge

section Interval

variable {α : Type} [LinearOrderedField α]

/-- A closed rational interval `[lo, hi]`. -/
structure Interval (α : Type) where
  lo : α
  hi : α

namespace Interval

/-- Membership in an interval. -/
def Mem (I : Interval α) (x : α) : Prop := I.lo ≤ x ∧ x ≤ I.hi

/-- Interval addition. -/
def add (I J : Interval α) : Interval α := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- The symmetric tolerance interval `[-τ, τ]`. -/
def sym (τ : α) : Interval α := ⟨-τ, τ⟩

/-- Interval addition encloses sums. -/
theorem mem_add {I J : Interval α} {x y : α} (hx : I.Mem x) (hy : J.Mem y) : (I.add J).Mem (x + y) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

end Interval

open Interval

/-- **Tolerance chain**: the errors of nested solves, each within its tolerance, sum within the summed tolerance. -/
theorem mem_sum_sym (l : List (α × α)) (h : ∀ p ∈ l, (sym p.2).Mem p.1) :
    (sym (l.map Prod.snd).sum).Mem (l.map Prod.fst).sum := by
  induction l with
  | nil => simp [sym, Mem]
  | cons p l ih =>
    have hp := h p (List.mem_cons_self p l)
    have hl := ih fun q hq => h q (List.mem_cons_of_mem p hq)
    have := mem_add hp hl
    simp only [sym, Mem, Interval.add, List.map_cons, List.sum_cons] at this hp hl ⊢
    constructor <;> linarith [this.1, this.2]

/-- **Error propagation**: an inner error within `τ_in`, a map `L`-Lipschitz on that enclosure and an outer error
    within `τ_out` leave the composite error within `τ_out + L τ_in`. -/
theorem error_chain {L τin τout yStar yHat z : α} {g : α → α} (hin : (sym τin).Mem (yHat - yStar))
    (hlip : ∀ x y, (sym τin).Mem (x - y) → (sym (L * τin)).Mem (g x - g y))
    (hout : (sym τout).Mem (z - g yHat)) : (sym (τout + L * τin)).Mem (z - g yStar) := by
  have h := mem_add hout (hlip yHat yStar hin)
  simp only [sym, Mem, Interval.add] at h ⊢
  constructor <;> linarith [h.1, h.2]

end Interval

end UMST.UnfoldKleisli
