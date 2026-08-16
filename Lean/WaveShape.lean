SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
/-
  UMST.WaveShape — weighted wave distance over finite deliverable regions (ℚ).
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

namespace UMST.WaveShape

structure Region (D : Type) where
  deliverables : List D
  weight       : D → Nat
  weight_pos   : ∀ d ∈ deliverables, 0 < weight d
  nonempty     : deliverables ≠ []

def totalWeight {D : Type} (R : Region D) : Nat :=
  R.deliverables.foldl (fun acc d => acc + R.weight d) 0

def missingWeightList {D : Type} (weight : D → Nat) (present : D → Bool) : List D → Nat
  | [] => 0
  | d :: tl =>
      if present d then missingWeightList weight present tl
      else weight d + missingWeightList weight present tl

def missingWeight {D : Type} (R : Region D) (present : D → Bool) : Nat :=
  missingWeightList R.weight present R.deliverables

def waveDistance {D : Type} (R : Region D) (present : D → Bool) : ℚ :=
  (missingWeight R present : ℚ) / (totalWeight R : ℚ)


private theorem foldl_add_pos {D : Type} (weight : D → Nat) :
    ∀ (xs : List D) (acc : Nat), 0 < acc → 0 < xs.foldl (fun a d => a + weight d) acc
  | [], acc, hacc => hacc
  | y :: ys, acc, hacc => by
      simp [List.foldl]
      refine foldl_add_pos weight ys (acc + weight y) ?_
      omega

def Completes {D : Type} (p q : D → Bool) : Prop := ∀ d, q d → p d

private theorem totalWeight_pos {D : Type} (R : Region D) : 0 < totalWeight R := by
  cases h : R.deliverables with
  | nil => exact False.elim (Ne.elim R.nonempty h)
  | cons x xs =>
      have hmem : x ∈ R.deliverables := h ▸ List.mem_cons_self x xs
      have hw := R.weight_pos x hmem
      dsimp [totalWeight]
      rw [h]
      simp only [List.foldl, Nat.zero_add]
      exact foldl_add_pos R.weight xs (R.weight x) hw

theorem waveDistance_nonneg {D : Type} (R : Region D) (present : D → Bool) :
    0 ≤ waveDistance R present := by
  unfold waveDistance
  apply div_nonneg (Nat.cast_nonneg _) (le_of_lt (by simpa using totalWeight_pos R))

private theorem missingWeightList_zero_iff_list {D : Type} (weight : D → Nat) (present : D → Bool)
    (L : List D) (hpos : ∀ z ∈ L, 0 < weight z) :
    missingWeightList weight present L = 0 ↔ ∀ y ∈ L, present y := by
  induction L with
  | nil => simp [missingWeightList]
  | cons a as ih =>
    have hpos' : ∀ z ∈ as, 0 < weight z := fun z hz => hpos z (List.mem_cons_of_mem _ hz)
    simp only [missingWeightList]
    constructor
    · intro h y hy
      rcases List.mem_cons.mp hy with (rfl | htl)
      · by_contra hnp
        simp [hnp] at h
        have hw := hpos y (List.mem_cons_self y as)
        omega
      · exact (ih hpos').mp (by
          by_cases hp : present a
          · simpa [hp] using h
          · exfalso
            simp [hp] at h
            have hw := hpos a (List.mem_cons_self a as)
            omega) y htl
    · intro hall
      have ha := hall a (List.mem_cons_self a as)
      simpa [ha, (ih hpos').mpr fun z hz => hall z (List.mem_cons_of_mem _ hz)]

theorem missingWeight_zero_iff {D : Type} (R : Region D) (present : D → Bool) :
    missingWeight R present = 0 ↔ ∀ d ∈ R.deliverables, present d := by
  unfold missingWeight
  simpa using missingWeightList_zero_iff_list R.weight present R.deliverables R.weight_pos

theorem missingWeightList_antimono {D : Type} {p q : D → Bool} (h : Completes p q)
    (weight : D → Nat) : ∀ (tl : List D), missingWeightList weight p tl ≤ missingWeightList weight q tl
  | [] => le_rfl
  | d :: tl => by
      have ih := missingWeightList_antimono h weight tl
      by_cases hp : p d
      · by_cases hq : q d
        · simpa [missingWeightList, hp, hq] using ih
        · show missingWeightList weight p (d :: tl) ≤ missingWeightList weight q (d :: tl)
          have hq' : q d = false := Bool.eq_false_iff.mpr hq
          rw [show missingWeightList weight p (d :: tl) = missingWeightList weight p tl from by
                simp [missingWeightList, hp],
              show missingWeightList weight q (d :: tl) = weight d + missingWeightList weight q tl from by
                simp [missingWeightList, hq']]
          apply le_trans ih
          simpa [Nat.add_comm] using Nat.le_add_right (missingWeightList weight q tl) (weight d)
      · by_cases hq : q d
        · exact absurd (h d hq) hp
        · have hp' : p d = false := Bool.eq_false_iff.mpr hp
          have hq' : q d = false := Bool.eq_false_iff.mpr hq
          simpa [missingWeightList, hp', hq'] using Nat.add_le_add_left ih (weight d)

theorem missingWeight_antimono {D : Type} (R : Region D) {p q : D → Bool}
    (h : Completes p q) : missingWeight R p ≤ missingWeight R q := by
  simpa [missingWeight] using missingWeightList_antimono h R.weight R.deliverables

theorem waveDistance_zero_iff {D : Type} (R : Region D) (present : D → Bool) :
    waveDistance R present = 0 ↔ ∀ d ∈ R.deliverables, present d := by
  unfold waveDistance
  have ht := totalWeight_pos R
  have hpos : 0 < (totalWeight R : ℚ) := Nat.cast_pos.mpr ht
  constructor
  · intro hzero
    rcases (div_eq_zero_iff).mp hzero with hnum | hden
    · exact (missingWeight_zero_iff R present).mp (Nat.cast_eq_zero.mp hnum)
    · exact absurd hden hpos.ne'
  · intro hall
    have hm := (missingWeight_zero_iff R present).mpr hall
    simp [hm, hpos.ne']

theorem waveDistance_antitone {D : Type} (R : Region D) {p q : D → Bool}
    (h : Completes p q) : waveDistance R p ≤ waveDistance R q := by
  unfold waveDistance
  have ht := totalWeight_pos R
  have hpos : 0 < (totalWeight R : ℚ) := Nat.cast_pos.mpr ht
  exact (div_le_div_iff_of_pos_right hpos).mpr (Nat.cast_le.mpr (missingWeight_antimono R h))

theorem waveDistance_triangle {D : Type} (R : Region D) {p q r : D → Bool}
    (hpq : Completes p q) (_hqr : Completes q r) :
    waveDistance R p ≤ waveDistance R q + waveDistance R r := by
  calc
    waveDistance R p ≤ waveDistance R q := waveDistance_antitone R hpq
    _ ≤ waveDistance R q + waveDistance R r := le_add_of_nonneg_right (waveDistance_nonneg R r)

theorem waveDistance_descent_wf {D : Type} (R : Region D) :
    WellFounded (fun a b : D → Bool => waveDistance R a < waveDistance R b) := by
  have ht := totalWeight_pos R
  have hpos : 0 < (totalWeight R : ℚ) := Nat.cast_pos.mpr ht
  refine (measure (fun p => missingWeight R p)).wf.mono ?_
  intro a b hb
  unfold waveDistance at hb
  exact Nat.cast_lt.mp ((div_lt_div_iff_of_pos_right hpos).mp hb)

end UMST.WaveShape
