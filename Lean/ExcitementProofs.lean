SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
/-
  UMST.ExcitementProofs — real theorems (no sorry).
-/
import Excitement
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Prod.Lex

namespace UMST.Excitement

open UMST.Core

theorem select_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) :
    select src [] = Sum.inr Residue.noCandidates := rfl

theorem select_admissible_from_result {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : select src cands = Sum.inl c) :
    Admissible src c.tgt ∧ select src cands ≠ Sum.inr Residue.noCandidates := by
  refine ⟨c.step, ?_⟩
  intro h
  simpa [h] using hsel

theorem select_result_cbf {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (src : S) (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (_hsel : select src cands = Sum.inl c) : c.cbfSafe := c.cbfSafe_holds

theorem select_result_dec {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (src : S) (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (_hsel : select src cands = Sum.inl c) : c.decConserving := c.decConserving_holds

/-- `pickMin` on a pair is commutative when ids differ. -/
theorem pickMin_comm_of_ne_id {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (a b : Cand (K := ℚ) src) (hid : a.id ≠ b.id) :
    pickMin (some a) b = pickMin (some b) a := by
  simp only [pickMin]
  rcases lt_trichotomy (candEnergy (src := src) a) (candEnergy (src := src) b) with h | h | h
  · have nab : ¬ candEnergy (src := src) b < candEnergy (src := src) a := not_lt_of_gt h
    simp [h, nab]
  · have nab : ¬ candEnergy (src := src) a < candEnergy (src := src) b := by simp [h]
    have nba : ¬ candEnergy (src := src) b < candEnergy (src := src) a := by simp [h]
    simp [nab, nba]
    rcases Nat.lt_trichotomy a.id b.id with hidab | heq | hidba
    · have : ¬ b.id < a.id := Nat.not_lt_of_gt hidab
      simp [hidab, this]
    · exact (hid heq).elim
    · have : ¬ a.id < b.id := Nat.not_lt_of_gt hidba
      simp [hidba, this]
  · have nab : ¬ candEnergy (src := src) a < candEnergy (src := src) b := not_lt_of_gt h
    simp [h, nab]

/-- Two-element swap of equal-energy distinct-id tagged candidates. -/
theorem select_swap_equal_energy_distinct_id {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (a b : Cand (K := ℚ) src)
    (_he : candEnergy (src := src) a = candEnergy (src := src) b)
    (hid : a.id ≠ b.id)
    (hta : a.evidenceTagged = true) (htb : b.evidenceTagged = true) :
    select src [a, b] = select src [b, a] := by
  have hcomm := pickMin_comm_of_ne_id (src := src) a b hid
  have hfold_ab :
      List.foldl (pickMin (src := src)) none [a, b] = pickMin (some a) b := by
    simp [List.foldl, pickMin]
  have hfold_ba :
      List.foldl (pickMin (src := src)) none [b, a] = pickMin (some b) a := by
    simp [List.foldl, pickMin]
  have hfilter_ab : ([a, b] : List (Cand (K := ℚ) src)).filter (fun c => c.evidenceTagged) = [a, b] := by
    simp [hta, htb]
  have hfilter_ba : ([b, a] : List (Cand (K := ℚ) src)).filter (fun c => c.evidenceTagged) = [b, a] := by
    simp [hta, htb]
  have hsel_ab :
      select src [a, b] =
        match pickMin (some a) b with
        | none => Sum.inr Residue.allInadmissible
        | some c =>
            if candEnergy (src := src) c < jointFreeEnergy src then Sum.inl c
            else Sum.inr Residue.noStrictImprovement := by
    dsimp [select]
    simp [hta, htb, hfilter_ab, hfold_ab]
    rfl
  have hsel_ba :
      select src [b, a] =
        match pickMin (some b) a with
        | none => Sum.inr Residue.allInadmissible
        | some c =>
            if candEnergy (src := src) c < jointFreeEnergy src then Sum.inl c
            else Sum.inr Residue.noStrictImprovement := by
    dsimp [select]
    simp [hta, htb, hfilter_ba, hfold_ba]
    rfl
  rw [hsel_ab, hsel_ba, hcomm]

/-- Key for lex order: free energy, then id. -/
def candKey {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    {src : S} (c : Cand (K := ℚ) src) : ℚ ×ₗ Nat :=
  toLex (candEnergy (src := src) c, c.id)

/-- Binary lex-min matching `pickMin`, via decidable Lex key order. -/
def minCand {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    {src : S} (a b : Cand (K := ℚ) src) : Cand (K := ℚ) src :=
  if candKey (src := src) b < candKey (src := src) a then b else a

theorem pickMin_eq_lex {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (a b : Cand (K := ℚ) src) :
    pickMin (some a) b = some (minCand (src := src) a b) := by
  simp only [pickMin, minCand, candKey, Prod.Lex.lt_iff]
  rcases lt_trichotomy (candEnergy (src := src) b) (candEnergy (src := src) a) with h | h | h
  · have nab : ¬ candEnergy (src := src) a < candEnergy (src := src) b := not_lt_of_gt h
    simp [h, nab]
  · have nab : ¬ candEnergy (src := src) b < candEnergy (src := src) a := by simp [h]
    have nba : ¬ candEnergy (src := src) a < candEnergy (src := src) b := by simp [h]
    simp [nab, nba, h]
    rcases Nat.lt_trichotomy b.id a.id with hid | heq | hid
    · simp [hid]
    · simp [heq]
    · have : ¬ b.id < a.id := Nat.not_lt_of_gt hid
      simp [this, hid]
  · have nab : ¬ candEnergy (src := src) b < candEnergy (src := src) a := not_lt_of_gt h
    have hne : candEnergy (src := src) b ≠ candEnergy (src := src) a := ne_of_gt h
    simp [h, nab, hne]

theorem minCand_comm_of_ne_id {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (a b : Cand (K := ℚ) src) (hid : a.id ≠ b.id) :
    minCand (src := src) a b = minCand (src := src) b a := by
  have h := pickMin_comm_of_ne_id (src := src) a b hid
  rw [pickMin_eq_lex, pickMin_eq_lex] at h
  exact Option.some.inj h

theorem minCand_assoc {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (a b c : Cand (K := ℚ) src) :
    minCand (src := src) (minCand (src := src) a b) c =
      minCand (src := src) a (minCand (src := src) b c) := by
  simp only [minCand]
  by_cases hba : candKey (src := src) b < candKey (src := src) a
  · by_cases hcb : candKey (src := src) c < candKey (src := src) b
    · by_cases hca : candKey (src := src) c < candKey (src := src) a
      · simp [hba, hcb, hca]
      · exact absurd (lt_trans hcb hba) hca
    · by_cases hca : candKey (src := src) c < candKey (src := src) a
      · have hb : (if candKey (src := src) c < candKey (src := src) b then c else b) = b := by
          simp [hcb]
        simp [hba, hcb, hca, hb]
      · simp [hba, hcb, hca]
  · by_cases hcb : candKey (src := src) c < candKey (src := src) b
    · by_cases hca : candKey (src := src) c < candKey (src := src) a
      · simp [hba, hcb, hca]
      · have hc : (if candKey (src := src) c < candKey (src := src) b then c else b) = c := by
          simp [hcb]
        simp [hba, hcb, hca, hc]
    · by_cases hca : candKey (src := src) c < candKey (src := src) a
      · -- ¬(b < a), ¬(c < b), c < a ⇒ a ≤ b ≤ c and c < a: impossible
        have hab : candKey (src := src) a ≤ candKey (src := src) b := le_of_not_gt hba
        have hbc : candKey (src := src) b ≤ candKey (src := src) c := le_of_not_gt hcb
        exact absurd hca (not_lt_of_ge (le_trans hab hbc))
      · simp [hba, hcb, hca]

theorem pickMin_right_comm_of_ne_id {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (x y : Cand (K := ℚ) src) (hid : x.id ≠ y.id)
    (z : Option (Cand (K := ℚ) src)) :
    pickMin (pickMin z x) y = pickMin (pickMin z y) x := by
  cases z with
  | none =>
    change pickMin (some x) y = pickMin (some y) x
    exact pickMin_comm_of_ne_id (src := src) x y hid
  | some a =>
    simp only [pickMin_eq_lex]
    have h := minCand_assoc (src := src) a x y
    have h' := minCand_assoc (src := src) a y x
    have hc := minCand_comm_of_ne_id (src := src) x y hid
    calc
      some (minCand (src := src) (minCand (src := src) a x) y)
          = some (minCand (src := src) a (minCand (src := src) x y)) := by rw [h]
      _ = some (minCand (src := src) a (minCand (src := src) y x)) := by rw [hc]
      _ = some (minCand (src := src) (minCand (src := src) a y) x) := by rw [← h']

theorem pairwise_id_from_mem {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    {src : S} {l : List (Cand (K := ℚ) src)}
    (h : List.Pairwise (fun a b => a.id ≠ b.id) l) {x y : Cand (K := ℚ) src}
    (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) : x.id ≠ y.id := by
  induction h generalizing x y with
  | nil => cases hx
  | cons ha hl ih =>
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hne rfl).elim
    · exact ha _ hy
    · exact (ha _ hx).symm
    · exact ih hx hy hne

theorem foldl_pickMin_perm {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} {l₁ l₂ : List (Cand (K := ℚ) src)}
    (hperm : List.Perm l₁ l₂)
    (huniq : List.Pairwise (fun a b => a.id ≠ b.id) l₁) :
    List.foldl (pickMin (src := src)) none l₁ =
      List.foldl (pickMin (src := src)) none l₂ := by
  refine hperm.foldl_eq' ?_ none
  intro x hx y hy z
  by_cases hxy : x = y
  · subst hxy; rfl
  · exact pickMin_right_comm_of_ne_id (src := src) x y
      (pairwise_id_from_mem (S := S) (src := src) huniq hx hy hxy) z

/-- Full list-permutation invariance of `select` (liquid-PPO reorder licence). -/
theorem select_perm_invariant {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S)
    (cands1 cands2 : List (Cand (K := ℚ) src))
    (hperm : List.Perm cands1 cands2)
    (huniq : List.Pairwise (fun a b => a.id ≠ b.id) cands1) :
    select src cands1 = select src cands2 := by
  have hempty := hperm.isEmpty_eq
  have hfilt : List.Perm (cands1.filter (·.evidenceTagged)) (cands2.filter (·.evidenceTagged)) :=
    hperm.filter _
  have huniq_f : List.Pairwise (fun a b => a.id ≠ b.id) (cands1.filter (·.evidenceTagged)) :=
    huniq.filter _
  have hfold := foldl_pickMin_perm (src := src) hfilt huniq_f
  have hte := hfilt.isEmpty_eq
  have hany :
      (cands1.any fun c => !c.evidenceTagged) = (cands2.any fun c => !c.evidenceTagged) := by
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hp⟩
      exact ⟨x, (hperm.mem_iff).1 hx, hp⟩
    · rintro ⟨x, hx, hp⟩
      exact ⟨x, (hperm.mem_iff).2 hx, hp⟩
  simp only [select, hempty]
  cases hEmp : cands1.isEmpty with
  | true =>
    have : cands2.isEmpty = true := by simp [← hempty, hEmp]
    simp [hEmp, this]
  | false =>
    have : cands2.isEmpty = false := by simp [← hempty, hEmp]
    simp only [hEmp, this]
    cases hT : (cands1.filter (·.evidenceTagged)).isEmpty with
    | true =>
      have : (cands2.filter (·.evidenceTagged)).isEmpty = true := by simp [← hte, hT]
      simp [hT, this, hany]
    | false =>
      have : (cands2.filter (·.evidenceTagged)).isEmpty = false := by simp [← hte, hT]
      simp [hT, this, hfold]

end UMST.Excitement
