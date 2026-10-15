-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: LearningLoopLaws.lean

  The laws the learning-loop kernel of umst-adk relies on, stated over what the runtime computes
  (umst-adk `outcome.rs`, `steer/learn.rs`, `liquid_ppo_bind.rs`; umst-algebra `ppo_clipped_step.rs`):

  1. The evidence map onto the lattice Unclaimed < Claimed < GuardPassed < Verified < Landed < MeterMoved
     (`outcome.rs::level_of`) is monotone: more evidence never lowers a level (`completeLevel_monotone`,
     `levelOf_monotone`).
  2. Outcome counts under pointwise addition (`OutcomeCounts::combine`) form a commutative monoid, and the fold from
     the identity (`OutcomeCounts::fold`) is a monoid homomorphism from lists under append, so every reordering of
     the rows folds to the same counts (`fold_append`, `fold_perm`).
  3. The Beta(V+1, R+1) posterior mean (V+1)/(V+R+2) (`outcome.rs::posterior`) is a function of the counts alone,
     hence invariant under permutation of the rows, and lies strictly between 0 and 1 (`posterior_perm`,
     `posterior_mean_mem`).
  4. The discrete control barrier h_{k+1} ≥ (1 − γ) h_k (`steer/learn.rs::barrier`, `ExactRatio::kept`) with γ ≤ 1
     keeps h above the geometric floor (1 − γ)^k h_0 and so keeps h ≥ 0 for every step (`barrier_floor`,
     `barrier_forward_invariant`); for 0 < γ < 1 the floor is the geometric collapse of
     `Economic.StochasticBurdenExpectation` and tends to 0 (`barrier_floor_tendsto_zero`).
  5. The clipped multiplicative step (`ppo_clipped_step.rs::clipped_multiplicative_step`) scales each weight by
     1 + c_i with −clip ≤ c_i ≤ clip < 1 and renormalises: the result is a distribution, each unnormalised weight
     moves by at most clip times itself, and each normalised weight stays within the ratio (1 + clip)/(1 − clip) of
     its predecessor (`ppoStep_simplex`, `scaled_move`, `ppoStep_ratio`). The largest-remainder apportionment
     (`quantize_distribution`) moves each unit count by less than one and keeps the total, for every selection of
     exactly the missing units (the largest remainders are one), and the missing units are fewer than the arms
     (`apportion_sum`, `apportion_close`, `apportion_missing_lt`).
  6. A verified evidence bit costs at least k_B T ln 2: a close counts its bits as evidence from the Verified level
     up, and bits paid by an erasure obeying the one predicate `SecondLaw` are an honest spend
     (`countedBits_cost`, `verified_bit_costs_landauer`, through `CostOfInformation.honest_spend_of_secondLaw`).

  The numeric laws (3)–(5) are proved over any linear ordered field, so they hold over ℚ, the field the runtime's
  exact rationals denote. Zero `axiom`, zero `sorry`.
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Economic.StochasticBurdenExpectation
import CostOfInformation

open Filter Topology Real UMST.LandauerLaw UMST.ProcessFamily UMST.Formal.Dignity

namespace UMST.LearningLoop

-- ================================================================
-- 1. The evidence lattice
-- ================================================================

/-- A rung of the evidence lattice (`outcome.rs::OutcomeLevel`). -/
inductive Level where
  | unclaimed | claimed | guardPassed | verified | landed | meterMoved
  deriving DecidableEq, Repr

/-- The rung's height; the lattice order is the order of heights. -/
def Level.rank : Level → ℕ
  | .unclaimed => 0
  | .claimed => 1
  | .guardPassed => 2
  | .verified => 3
  | .landed => 4
  | .meterMoved => 5

/-- What a receipt claims (`outcome.rs::ClaimStatus`). -/
inductive ClaimStatus where
  | open | complete | refused
  deriving DecidableEq, Repr

/-- A rung, or refused (REWORK or REFUSED), which sits outside the lattice (`outcome.rs::Outcome`). -/
inductive Outcome where
  | refused
  | level (l : Level)
  deriving DecidableEq, Repr

/-- The evidence beneath a COMPLETE claim (`outcome.rs::Evidence`, as the set of pieces held). -/
structure Evidence where
  guard : Bool
  verified : Bool
  landed : Bool
  moved : Bool
  deriving DecidableEq, Repr

/-- More evidence: every piece `e` holds, `f` holds too. -/
def Evidence.le (e f : Evidence) : Prop :=
  (e.guard = true → f.guard = true) ∧ (e.verified = true → f.verified = true) ∧
    (e.landed = true → f.landed = true) ∧ (e.moved = true → f.moved = true)

/-- The highest rung a COMPLETE claim's evidence holds: `Verified` subsumes the guard rung, `Landed` needs `Verified`
    beneath it and `MeterMoved` needs `Landed` (`outcome.rs::level_of`). -/
def completeLevel (e : Evidence) : Level :=
  if e.verified then (if e.landed then (if e.moved then .meterMoved else .landed) else .verified)
  else if e.guard then .guardPassed else .claimed

/-- The outcome of a receipt (`outcome.rs::level_of`). -/
def levelOf : ClaimStatus → Evidence → Outcome
  | .refused, _ => .refused
  | .open, _ => .level .unclaimed
  | .complete, e => .level (completeLevel e)

/-- The order on outcomes: refused only below itself, rungs by height. -/
def Outcome.le : Outcome → Outcome → Prop
  | .refused, .refused => True
  | .level a, .level b => a.rank ≤ b.rank
  | _, _ => False

/-- **Law 1**: more evidence never lowers the level of a COMPLETE claim. -/
theorem completeLevel_monotone {e f : Evidence} (h : e.le f) :
    (completeLevel e).rank ≤ (completeLevel f).rank := by
  obtain ⟨g, v, l, m⟩ := e
  obtain ⟨g', v', l', m'⟩ := f
  obtain ⟨hg, hv, hl, hm⟩ := h
  simp only at hg hv hl hm
  cases g <;> cases v <;> cases l <;> cases m <;> cases g' <;> cases v' <;> cases l' <;> cases m' <;>
    simp_all [completeLevel, Level.rank]

/-- **Law 1**, for every claim status: the outcome map is monotone in the evidence. -/
theorem levelOf_monotone (s : ClaimStatus) {e f : Evidence} (h : e.le f) :
    (levelOf s e).le (levelOf s f) := by
  cases s with
  | «open» => exact le_refl 0
  | complete => exact completeLevel_monotone h
  | refused => trivial

-- ================================================================
-- 2. Outcome counts: a commutative monoid, folded by a homomorphism
-- ================================================================

/-- Counts of outcomes by key (`outcome.rs::OutcomeCounts`; an absent key counts zero). -/
abbrev Counts (K : Type*) := K → ℕ

variable {K : Type*}

/-- The identity: every key counts zero. -/
def Counts.zero : Counts K := fun _ => 0

/-- The pointwise sum (`OutcomeCounts::combine`). -/
def Counts.combine (a b : Counts K) : Counts K := fun k => a k + b k

theorem combine_assoc (a b c : Counts K) :
    Counts.combine (Counts.combine a b) c = Counts.combine a (Counts.combine b c) := by
  funext k; simp [Counts.combine, Nat.add_assoc]

theorem combine_comm (a b : Counts K) : Counts.combine a b = Counts.combine b a := by
  funext k; simp [Counts.combine, Nat.add_comm]

theorem zero_combine (a : Counts K) : Counts.combine Counts.zero a = a := by
  funext k; simp [Counts.combine, Counts.zero]

theorem combine_zero (a : Counts K) : Counts.combine a Counts.zero = a := by
  funext k; simp [Counts.combine, Counts.zero]

/-- The fold of many counts from the identity, left to right (`OutcomeCounts::fold`). -/
def Counts.fold (xs : List (Counts K)) : Counts K := xs.foldl Counts.combine Counts.zero

theorem foldl_combine (acc : Counts K) (xs : List (Counts K)) :
    xs.foldl Counts.combine acc = Counts.combine acc (Counts.fold xs) := by
  induction xs generalizing acc with
  | nil => simp [Counts.fold, combine_zero]
  | cons x xs ih =>
    simp only [List.foldl_cons, Counts.fold]
    rw [ih, ih (Counts.combine Counts.zero x), zero_combine, combine_assoc]

theorem fold_nil : Counts.fold ([] : List (Counts K)) = Counts.zero := rfl

theorem fold_cons (x : Counts K) (xs : List (Counts K)) :
    Counts.fold (x :: xs) = Counts.combine x (Counts.fold xs) := by
  simp only [Counts.fold, List.foldl_cons]
  rw [foldl_combine, zero_combine]
  rfl

/-- **Law 2**: the fold is a monoid homomorphism from lists under append. -/
theorem fold_append (xs ys : List (Counts K)) :
    Counts.fold (xs ++ ys) = Counts.combine (Counts.fold xs) (Counts.fold ys) := by
  induction xs with
  | nil => simp [fold_nil, zero_combine]
  | cons x xs ih => rw [List.cons_append, fold_cons, fold_cons, ih, combine_assoc]

/-- **Law 2**: every reordering of the rows folds to the same counts. -/
theorem fold_perm {xs ys : List (Counts K)} (h : xs.Perm ys) : Counts.fold xs = Counts.fold ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [fold_cons, fold_cons, ih]
  | swap x y l =>
    rw [fold_cons, fold_cons, fold_cons, fold_cons, ← combine_assoc, ← combine_assoc, combine_comm y x]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

-- ================================================================
-- 3. The Beta posterior
-- ================================================================

/-- The sum of the counts under some keys. -/
def keySum (keys : List K) (c : Counts K) : ℕ := (keys.map c).sum

/-- The Beta(V+1, R+1) posterior mean as numerator and denominator, V the counts under the verified keys and R under
    the failure keys (`outcome.rs::posterior`: verified_plus + document_admitted against rework + document_refused). -/
def posterior (vKeys rKeys : List K) (c : Counts K) : ℕ × ℕ :=
  (keySum vKeys c + 1, keySum vKeys c + keySum rKeys c + 2)

/-- **Law 3**: the posterior of a lane is the same for every order of its rows. -/
theorem posterior_perm (vKeys rKeys : List K) {xs ys : List (Counts K)} (h : xs.Perm ys) :
    posterior vKeys rKeys (Counts.fold xs) = posterior vKeys rKeys (Counts.fold ys) := by
  rw [fold_perm h]

/-- **Law 3**: the posterior mean (V+1)/(V+R+2) lies strictly between 0 and 1. -/
theorem posterior_mean_mem (vKeys rKeys : List K) (c : Counts K) :
    0 < ((posterior vKeys rKeys c).1 : ℚ) / (posterior vKeys rKeys c).2 ∧
      ((posterior vKeys rKeys c).1 : ℚ) / (posterior vKeys rKeys c).2 < 1 := by
  simp only [posterior]
  have hd : (0 : ℚ) < (keySum vKeys c + keySum rKeys c + 2 : ℕ) := by positivity
  constructor
  · positivity
  · rw [div_lt_one hd]; push_cast; linarith [(Nat.cast_nonneg (keySum rKeys c) : (0 : ℚ) ≤ _)]

-- ================================================================
-- 4. The control barrier
-- ================================================================

section Barrier

variable {α : Type*} [LinearOrderedField α]

/-- One step of the barrier keeps `h ≥ 0`. -/
theorem barrier_step_nonneg {γ x y : α} (hγ : γ ≤ 1) (hx : 0 ≤ x) (hstep : (1 - γ) * x ≤ y) : 0 ≤ y :=
  le_trans (mul_nonneg (sub_nonneg.mpr hγ) hx) hstep

/-- **Law 4**: under the discrete barrier condition `h (k+1) ≥ (1 − γ) h k`, `h` stays above the geometric floor. -/
theorem barrier_floor (h : ℕ → α) {γ : α} (hγ : γ ≤ 1) (hstep : ∀ k, (1 - γ) * h k ≤ h (k + 1)) :
    ∀ k, (1 - γ) ^ k * h 0 ≤ h k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hg : 0 ≤ 1 - γ := sub_nonneg.mpr hγ
    calc (1 - γ) ^ (k + 1) * h 0 = (1 - γ) * ((1 - γ) ^ k * h 0) := by ring
      _ ≤ (1 - γ) * h k := mul_le_mul_of_nonneg_left ih hg
      _ ≤ h (k + 1) := hstep k

/-- **Law 4**: the safe set `h ≥ 0` is forward invariant under the barrier condition. -/
theorem barrier_forward_invariant (h : ℕ → α) {γ : α} (hγ : γ ≤ 1) (hstep : ∀ k, (1 - γ) * h k ≤ h (k + 1))
    (h0 : 0 ≤ h 0) : ∀ k, 0 ≤ h k := fun k =>
  le_trans (mul_nonneg (pow_nonneg (sub_nonneg.mpr hγ) k) h0) (barrier_floor h hγ hstep k)

end Barrier

/-- **Law 4**, composed with `Economic.StochasticBurdenExpectation`: for `0 < γ < 1` the barrier's floor is the
    geometric collapse `(1 + μ)^k` at `μ = −γ`, so it tends to 0 while `h` stays non-negative above it. -/
theorem barrier_floor_tendsto_zero (h0 γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Tendsto (fun k : ℕ => (1 - γ) ^ k * h0) atTop (𝓝 0) := by
  have hg := UMST.Economics.exploration_buffer_geom_tendsto_zero_of_lt_one (-γ) (by linarith) (by linarith)
  have hg' : Tendsto (fun k : ℕ => (1 - γ) ^ k) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg] using hg
  simpa using hg'.mul_const h0

-- ================================================================
-- 5. The clipped multiplicative step and the largest-remainder apportionment
-- ================================================================

section Step

variable {α : Type*} [LinearOrderedField α]

/-- The clamp of the runtime: `lo` below it, `hi` above it, `v` between (`ppo_clipped_step.rs::clamp`). -/
def clamp (lo hi v : α) : α := if v < lo then lo else if hi < v then hi else v

theorem clamp_mem {lo hi : α} (v : α) (hlh : lo ≤ hi) : lo ≤ clamp lo hi v ∧ clamp lo hi v ≤ hi := by
  unfold clamp
  split_ifs with h1 h2
  · exact ⟨le_refl _, hlh⟩
  · exact ⟨hlh, le_refl _⟩
  · exact ⟨not_lt.mp h1, not_lt.mp h2⟩

/-- An arm: its weight and its clamped relative change. -/
abbrev Arm (α : Type*) := α × α

/-- The arm's weight scaled by `1 + c`. -/
def scaledW (a : Arm α) : α := a.1 * (1 + a.2)

def sumW (l : List (Arm α)) : α := (l.map Prod.fst).sum

def sumScaled (l : List (Arm α)) : α := (l.map scaledW).sum

/-- The step: each scaled weight over the sum of the scaled weights. -/
def ppoStep (l : List (Arm α)) : List α := l.map fun a => scaledW a / sumScaled l

/-- Every weight non-negative and every change within the clip. -/
def ArmsOk (clip : α) (l : List (Arm α)) : Prop := ∀ a ∈ l, 0 ≤ a.1 ∧ -clip ≤ a.2 ∧ a.2 ≤ clip

/-- **Law 5**: before renormalisation each weight moves by at most the clip times itself. -/
theorem scaled_move {clip : α} {a : Arm α} (hw : 0 ≤ a.1) (hlo : -clip ≤ a.2) (hhi : a.2 ≤ clip) :
    -(clip * a.1) ≤ scaledW a - a.1 ∧ scaledW a - a.1 ≤ clip * a.1 := by
  unfold scaledW
  constructor <;> nlinarith

theorem sumScaled_mem {clip : α} (l : List (Arm α)) (h : ArmsOk clip l) :
    (1 - clip) * sumW l ≤ sumScaled l ∧ sumScaled l ≤ (1 + clip) * sumW l := by
  induction l with
  | nil => simp [sumW, sumScaled]
  | cons a l ih =>
    have ha := h a (List.mem_cons_self a l)
    have hl : ArmsOk clip l := fun b hb => h b (List.mem_cons_of_mem a hb)
    obtain ⟨ih1, ih2⟩ := ih hl
    simp only [sumW, sumScaled, List.map_cons, List.sum_cons] at ih1 ih2 ⊢
    obtain ⟨hw, hlo, hhi⟩ := ha
    have hm := scaled_move hw hlo hhi
    constructor <;> nlinarith [hm.1, hm.2]

theorem sum_map_div (l : List (Arm α)) (S : α) :
    (l.map fun a => scaledW a / S).sum = sumScaled l / S := by
  induction l with
  | nil => simp [sumScaled]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, sumScaled] at ih ⊢
    rw [ih, add_div]

/-- **Law 5**: the step of a distribution is a distribution: non-negative weights summing to 1. -/
theorem ppoStep_simplex {clip : α} (hclip : clip < 1) (l : List (Arm α)) (h : ArmsOk clip l) (hsum : sumW l = 1) :
    (∀ x ∈ ppoStep l, 0 ≤ x) ∧ (ppoStep l).sum = 1 := by
  have hS : 0 < sumScaled l := by
    have := (sumScaled_mem l h).1; rw [hsum] at this; linarith
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hw, hlo, _⟩ := h a ha
    exact div_nonneg (mul_nonneg hw (by linarith)) hS.le
  · rw [ppoStep, sum_map_div, div_self hS.ne']

/-- **Law 5**: each normalised weight stays within the ratio (1 + clip)/(1 − clip) of its predecessor. -/
theorem ppoStep_ratio {clip : α} (hclip : clip < 1) (l : List (Arm α)) (h : ArmsOk clip l) (hsum : sumW l = 1) :
    ∀ a ∈ l, (1 - clip) * a.1 ≤ (1 + clip) * (scaledW a / sumScaled l) ∧
      (1 - clip) * (scaledW a / sumScaled l) ≤ (1 + clip) * a.1 := by
  intro a ha
  obtain ⟨hS1, hS2⟩ := sumScaled_mem l h
  rw [hsum, mul_one] at hS1 hS2
  have hS : 0 < sumScaled l := by linarith
  obtain ⟨hw, hlo, hhi⟩ := h a ha
  have hm := scaled_move hw hlo hhi
  set v := scaledW a / sumScaled l with hvdef
  have hv : 0 ≤ v := div_nonneg (mul_nonneg hw (by linarith)) hS.le
  have hdef : v * sumScaled l = scaledW a := div_mul_cancel₀ _ hS.ne'
  have hup : v * sumScaled l ≤ v * (1 + clip) := mul_le_mul_of_nonneg_left hS2 hv
  have hdn : v * (1 - clip) ≤ v * sumScaled l := mul_le_mul_of_nonneg_left hS1 hv
  constructor <;> nlinarith [hm.1, hm.2]

end Step

/-- A unit of the apportionment: the scaled weight `x`, its floor `f` and whether it receives one missing unit. -/
abbrev Part (β : Type*) := β × ℕ × Bool

def bump (b : Bool) : ℕ := if b then 1 else 0

/-- The apportioned count: the floor plus the bump. -/
def apportioned {β : Type*} (p : Part β) : ℕ := p.2.1 + bump p.2.2

/-- **Law 5**: the apportioned total is the floors' total plus the bumps. -/
theorem apportion_sum {β : Type*} (l : List (Part β)) :
    (l.map apportioned).sum = (l.map fun p => p.2.1).sum + (l.map fun p => bump p.2.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp only [List.map_cons, List.sum_cons, apportioned] at ih ⊢; rw [ih]; ring

section Apportion

variable {α : Type*} [LinearOrderedField α]

def FloorsOk (l : List (Part α)) : Prop := ∀ p ∈ l, (p.2.1 : α) ≤ p.1 ∧ p.1 < p.2.1 + 1

/-- A bump goes only to an arm with a positive remainder; the largest-remainder order gives one, since the missing
    units are the sum of remainders each below one. -/
def BumpsPositive (l : List (Part α)) : Prop := ∀ p ∈ l, p.2.2 = true → (p.2.1 : α) < p.1

/-- **Law 5**: each apportioned count is within one of its scaled weight: from below for every selection, and
    strictly from above when the bumps go to positive remainders. -/
theorem apportion_close (l : List (Part α)) (h : FloorsOk l) (hpos : BumpsPositive l) :
    ∀ p ∈ l, p.1 - 1 < (apportioned p : α) ∧ (apportioned p : α) < p.1 + 1 := by
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  have hc : (apportioned p : α) = (p.2.1 : α) + (bump p.2.2 : α) := by
    simp only [apportioned, Nat.cast_add]
  rw [hc]
  cases hb : p.2.2
  · have h0 : (bump false : α) = 0 := by simp [bump]
    rw [h0]
    constructor <;> linarith
  · have hlt := hpos p hp hb
    have h1' : (bump true : α) = 1 := by simp [bump]
    rw [h1']
    constructor <;> linarith

/-- **Law 5**: the missing units (the total less the floors) are fewer than the arms, so one unit to each of that
    many distinct arms (the largest remainders) exists. -/
theorem apportion_missing_lt (l : List (Part α)) (h : FloorsOk l) (hne : l ≠ []) :
    (l.map Prod.fst).sum - ((l.map fun p => p.2.1).sum : ℕ) < (l.length : α) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons p l ih =>
    have hp := h p (List.mem_cons_self p l)
    have hl : FloorsOk l := fun q hq => h q (List.mem_cons_of_mem p hq)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rcases l with _ | ⟨q, l'⟩
    · simp; linarith [hp.2]
    · have := ih hl (List.cons_ne_nil q l')
      linarith [hp.2]

end Apportion

-- ================================================================
-- 6. One verified evidence bit costs at least k_B T ln 2
-- ================================================================

/-- The bits a close counts as evidence: its claimed bits from the Verified level up, none below or when refused. -/
def countedBits (s : ClaimStatus) (e : Evidence) (bits : ℕ) : ℕ :=
  match levelOf s e with
  | .level l => if 3 ≤ l.rank then bits else 0
  | .refused => 0

theorem countedBits_le (s : ClaimStatus) (e : Evidence) (bits : ℕ) : countedBits s e bits ≤ bits := by
  unfold countedBits
  split
  · split_ifs <;> omega
  · omega

/-- The bit erasure of `CostOfInformation`: the uniform distribution on 2^bits states to a point, as a prior. -/
noncomputable abbrev bitErasurePrior (bits : ℕ) : Prior :=
  .transformation (uniformDist (2 ^ bits) (pow_pos two_pos bits)) (diracDist (0 : Fin (2 ^ bits)))

/-- **Law 6**: the counted evidence bits of a close paid by an erasure of its bits obeying `SecondLaw` cost at least
    k_B T ln 2 each. -/
theorem countedBits_cost (s : ClaimStatus) (e : Evidence) (b : HeatBath) (W : ℝ) (bits : ℕ)
    (h : SecondLaw (.erase ⟨b, W⟩) (bitErasurePrior bits)) :
    (countedBits s e bits : ℝ) * (kB * b.bathTemp.val * log 2) ≤ kB * W := by
  have hc := UMST.CostOfInformation.bitErasure_cost b W bits h
  have hL : 0 ≤ kB * b.bathTemp.val * log 2 :=
    mul_nonneg (mul_nonneg kB_pos.le b.bathTemp.property.le) (Real.log_nonneg (by norm_num))
  have hle : (countedBits s e bits : ℝ) ≤ bits := by exact_mod_cast countedBits_le s e bits
  nlinarith

/-- **Law 6**: a verified close of at least one evidence bit, paid by an erasure of its bits obeying `SecondLaw`,
    spends honestly (`honest_spend_of_secondLaw`) and pays at least one Landauer bit energy k_B T ln 2. -/
theorem verified_bit_costs_landauer (e : Evidence) (hv : e.verified = true) (b : HeatBath) (W : ℝ) (bits : ℕ)
    (hbits : 1 ≤ bits) (c : DignityClaim) (hb : c.delta_mi_bits = bits) (hE : c.delta_energy_j = kB * W)
    (h : SecondLaw (.erase ⟨b, W⟩) (bitErasurePrior bits)) :
    countedBits .complete e bits = bits ∧ honest_spend b.bathTemp.val c ∧
      landauer_joules_per_bit b.bathTemp.val ≤ c.delta_energy_j := by
  have hcount : countedBits .complete e bits = bits := by
    obtain ⟨g, v, l, m⟩ := e
    simp only at hv
    subst hv
    cases l <;> cases m <;> simp [countedBits, levelOf, completeLevel, Level.rank]
  have hh := UMST.CostOfInformation.honest_spend_of_secondLaw b W bits c hb hE h
  refine ⟨hcount, hh, ?_⟩
  have hL : 0 < landauer_joules_per_bit b.bathTemp.val := landauer_joules_per_bit_pos b.bathTemp.property
  have h1 : (1 : ℝ) ≤ c.delta_mi_bits := by rw [hb]; exact_mod_cast hbits
  unfold honest_spend at hh
  nlinarith

end UMST.LearningLoop
