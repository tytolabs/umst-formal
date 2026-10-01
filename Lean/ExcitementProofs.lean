-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
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
  simp [h] at hsel

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

/-- The lexicographic key orders energies: a smaller key has no larger energy. -/
theorem candEnergy_le_of_key_le {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    {src : S} {a b : Cand (K := ℚ) src} (h : candKey (src := src) a ≤ candKey (src := src) b) :
    candEnergy (src := src) a ≤ candEnergy (src := src) b := by
  simp only [candKey, Prod.Lex.le_iff] at h
  rcases h with h | h
  · exact h.le
  · exact h.1.le

/-- One step of the fold keeps a candidate that is the new one or the accumulated one, and no more energetic than
    either. -/
theorem pickMin_spec {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    {src : S} (acc : Option (Cand (K := ℚ) src)) (x : Cand (K := ℚ) src) :
    ∃ r, pickMin acc x = some r ∧ (r = x ∨ acc = some r) ∧
      candEnergy (src := src) r ≤ candEnergy (src := src) x ∧
      ∀ a, acc = some a → candEnergy (src := src) r ≤ candEnergy (src := src) a := by
  cases acc with
  | none => exact ⟨x, rfl, Or.inl rfl, le_rfl, fun a h => by cases h⟩
  | some b =>
    refine ⟨minCand (src := src) b x, pickMin_eq_lex b x, ?_, ?_, ?_⟩
    · unfold minCand; split_ifs <;> simp
    · unfold minCand; split_ifs with h
      · exact le_rfl
      · exact candEnergy_le_of_key_le (le_of_not_gt h)
    · intro a ha
      cases ha
      unfold minCand; split_ifs with h
      · exact candEnergy_le_of_key_le h.le
      · exact le_rfl

/-- The fold's result is a member of the list or the seed, and no more energetic than any member or the seed. -/
theorem foldl_pickMin_spec {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    {src : S} (l : List (Cand (K := ℚ) src)) (acc : Option (Cand (K := ℚ) src)) (m : Cand (K := ℚ) src)
    (h : l.foldl (pickMin (src := src)) acc = some m) :
    (m ∈ l ∨ acc = some m) ∧ (∀ x ∈ l, candEnergy (src := src) m ≤ candEnergy (src := src) x) ∧
      ∀ a, acc = some a → candEnergy (src := src) m ≤ candEnergy (src := src) a := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨Or.inr rfl, (fun x hx => by cases hx), (fun a ha => by cases ha; exact le_rfl)⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨r, hr, hrmem, hrx, hracc⟩ := pickMin_spec (src := src) acc x
    rw [hr] at h
    obtain ⟨hmem, hle, hseed⟩ := ih (some r) h
    have hmr : candEnergy (src := src) m ≤ candEnergy (src := src) r := hseed r rfl
    refine ⟨?_, ?_, ?_⟩
    · rcases hmem with hm | hm
      · exact Or.inl (List.mem_cons_of_mem x hm)
      · cases hm
        rcases hrmem with rfl | hacc
        · exact Or.inl (List.mem_cons_self _ _)
        · exact Or.inr hacc
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_trans hmr hrx
      · exact hle y hy
    · intro a ha
      exact le_trans hmr (hracc a ha)

/-- A returned candidate is the fold's minimum over the evidence-tagged candidates, below the source's free energy. -/
theorem select_inl_spec {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (src : S) (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : select src cands = Sum.inl c) :
    (cands.filter (fun c => c.evidenceTagged)).foldl (pickMin (src := src)) none = some c ∧
      candEnergy (src := src) c < jointFreeEnergy src := by
  unfold select at hsel
  split at hsel
  · cases hsel
  dsimp only at hsel
  split at hsel
  · split at hsel <;> cases hsel
  split at hsel
  · cases hsel
  rename_i m hf
  split at hsel
  · cases hsel
    exact ⟨hf, by assumption⟩
  · cases hsel

/-- **Selection is a minimum**: the selected candidate is an evidence-tagged member of the list and no evidence-tagged
    candidate has lower global free energy. -/
theorem select_minimal {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (src : S) (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : select src cands = Sum.inl c) :
    c ∈ cands ∧ c.evidenceTagged = true ∧
      ∀ c' ∈ cands, c'.evidenceTagged = true → candEnergy (src := src) c ≤ candEnergy (src := src) c' := by
  obtain ⟨hf, -⟩ := select_inl_spec src cands c hsel
  obtain ⟨hmem, hle, -⟩ := foldl_pickMin_spec (src := src) _ none c hf
  have hmem' : c ∈ cands.filter (fun c => c.evidenceTagged) := hmem.resolve_right (by simp)
  refine ⟨(List.mem_filter.1 hmem').1, (List.mem_filter.1 hmem').2, ?_⟩
  intro c' hc' ht
  exact hle c' (List.mem_filter.2 ⟨hc', ht⟩)

/-- **Selection descends**: the selected candidate's global free energy is strictly below the source's. -/
theorem select_descent {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (src : S) (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : select src cands = Sum.inl c) :
    candEnergy (src := src) c < jointFreeEnergy src :=
  (select_inl_spec src cands c hsel).2

end UMST.Excitement
