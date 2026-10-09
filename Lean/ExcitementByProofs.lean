-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST.ExcitementByProofs — the algebra and specification of `selectBy` over any linear order
  (no sorry, no new axiom). The theorems of `ExcitementProofs` are the instance at `candEnergy`
  through `select_eq_selectBy`; `select_minimal_of_selectBy` re-derives one of them as a check.
-/
import ExcitementBy
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Monotone.Basic

namespace UMST.Excitement

open UMST.Core

section Generic

variable {K S : Type} [LinearOrder K] [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] {src : S}

theorem selectBy_empty (obj : Cand (K := ℚ) src → K) (b : Baseline K) :
    selectBy obj b ([] : List (Cand (K := ℚ) src)) = Sum.inr Residue.noCandidates := rfl

theorem selectBy_admissible_from_result (obj : Cand (K := ℚ) src → K) (b : Baseline K)
    (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : selectBy obj b cands = Sum.inl c) :
    Admissible src c.tgt ∧ selectBy obj b cands ≠ Sum.inr Residue.noCandidates := by
  refine ⟨c.step, ?_⟩
  intro h
  rw [h] at hsel
  cases hsel

theorem selectBy_result_cbf (obj : Cand (K := ℚ) src → K) (b : Baseline K)
    (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (_hsel : selectBy obj b cands = Sum.inl c) : c.cbfSafe := c.cbfSafe_holds

theorem selectBy_result_dec (obj : Cand (K := ℚ) src → K) (b : Baseline K)
    (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (_hsel : selectBy obj b cands = Sum.inl c) : c.decConserving := c.decConserving_holds

/-- `pickMinBy` is the lexicographic minimum on `(obj, id)`. -/
theorem pickMinBy_eq_lex (obj : Cand (K := ℚ) src → K) (a b : Cand (K := ℚ) src) :
    pickMinBy obj (some a) b = some (minCandBy obj a b) := by
  simp only [pickMinBy, minCandBy, candKeyBy, Prod.Lex.lt_iff]
  rcases lt_trichotomy (obj b) (obj a) with h | h | h
  · have nab : ¬ obj a < obj b := not_lt_of_gt h
    simp [h, nab]
  · have nab : ¬ obj b < obj a := by simp [h]
    have nba : ¬ obj a < obj b := by simp [h]
    simp [nab, nba, h]
    rcases Nat.lt_trichotomy b.id a.id with hid | heq | hid
    · simp [hid]
    · simp [heq]
    · have : ¬ b.id < a.id := Nat.not_lt_of_gt hid
      simp [this, hid]
  · have nab : ¬ obj b < obj a := not_lt_of_gt h
    have hne : obj b ≠ obj a := ne_of_gt h
    simp [h, nab, hne]

/-- `pickMinBy` on a pair is commutative when ids differ. -/
theorem pickMinBy_comm_of_ne_id (obj : Cand (K := ℚ) src → K) (a b : Cand (K := ℚ) src)
    (hid : a.id ≠ b.id) : pickMinBy obj (some a) b = pickMinBy obj (some b) a := by
  simp only [pickMinBy]
  rcases lt_trichotomy (obj a) (obj b) with h | h | h
  · have nab : ¬ obj b < obj a := not_lt_of_gt h
    simp [h, nab]
  · have nab : ¬ obj a < obj b := by simp [h]
    have nba : ¬ obj b < obj a := by simp [h]
    simp [nab, nba]
    rcases Nat.lt_trichotomy a.id b.id with hidab | heq | hidba
    · have : ¬ b.id < a.id := Nat.not_lt_of_gt hidab
      simp [hidab, this]
    · exact (hid heq).elim
    · have : ¬ a.id < b.id := Nat.not_lt_of_gt hidba
      simp [hidba, this]
  · have nab : ¬ obj a < obj b := not_lt_of_gt h
    simp [h, nab]

theorem minCandBy_comm_of_ne_id (obj : Cand (K := ℚ) src → K) (a b : Cand (K := ℚ) src)
    (hid : a.id ≠ b.id) : minCandBy obj a b = minCandBy obj b a := by
  have h := pickMinBy_comm_of_ne_id obj a b hid
  rw [pickMinBy_eq_lex, pickMinBy_eq_lex] at h
  exact Option.some.inj h

theorem minCandBy_assoc (obj : Cand (K := ℚ) src → K) (a b c : Cand (K := ℚ) src) :
    minCandBy obj (minCandBy obj a b) c = minCandBy obj a (minCandBy obj b c) := by
  simp only [minCandBy]
  by_cases hba : candKeyBy obj b < candKeyBy obj a
  · by_cases hcb : candKeyBy obj c < candKeyBy obj b
    · by_cases hca : candKeyBy obj c < candKeyBy obj a
      · simp [hba, hcb, hca]
      · exact absurd (lt_trans hcb hba) hca
    · by_cases hca : candKeyBy obj c < candKeyBy obj a
      · simp [hba, hcb, hca]
      · simp [hba, hcb, hca]
  · by_cases hcb : candKeyBy obj c < candKeyBy obj b
    · by_cases hca : candKeyBy obj c < candKeyBy obj a
      · simp [hba, hcb, hca]
      · simp [hba, hcb, hca]
    · by_cases hca : candKeyBy obj c < candKeyBy obj a
      · have hab : candKeyBy obj a ≤ candKeyBy obj b := le_of_not_gt hba
        have hbc : candKeyBy obj b ≤ candKeyBy obj c := le_of_not_gt hcb
        exact absurd hca (not_lt_of_ge (le_trans hab hbc))
      · simp [hba, hcb, hca]

theorem pickMinBy_right_comm_of_ne_id (obj : Cand (K := ℚ) src → K) (x y : Cand (K := ℚ) src)
    (hid : x.id ≠ y.id) (z : Option (Cand (K := ℚ) src)) :
    pickMinBy obj (pickMinBy obj z x) y = pickMinBy obj (pickMinBy obj z y) x := by
  cases z with
  | none => exact pickMinBy_comm_of_ne_id obj x y hid
  | some a =>
    simp only [pickMinBy_eq_lex]
    rw [minCandBy_assoc, minCandBy_comm_of_ne_id obj x y hid, ← minCandBy_assoc]

theorem pairwise_id_ne_of_mem {l : List (Cand (K := ℚ) src)}
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

theorem foldl_pickMinBy_perm (obj : Cand (K := ℚ) src → K) {l₁ l₂ : List (Cand (K := ℚ) src)}
    (hperm : List.Perm l₁ l₂) (huniq : List.Pairwise (fun a b => a.id ≠ b.id) l₁) :
    List.foldl (pickMinBy obj) none l₁ = List.foldl (pickMinBy obj) none l₂ := by
  refine hperm.foldl_eq' ?_ none
  intro x hx y hy z
  by_cases hxy : x = y
  · subst hxy; rfl
  · exact pickMinBy_right_comm_of_ne_id obj x y (pairwise_id_ne_of_mem huniq hx hy hxy) z

/-- **Permutation invariance** of `selectBy` under pairwise-distinct ids. -/
theorem selectBy_perm_invariant (obj : Cand (K := ℚ) src → K) (b : Baseline K)
    (cands1 cands2 : List (Cand (K := ℚ) src)) (hperm : List.Perm cands1 cands2)
    (huniq : List.Pairwise (fun a b => a.id ≠ b.id) cands1) :
    selectBy obj b cands1 = selectBy obj b cands2 := by
  have hempty := hperm.isEmpty_eq
  have hfilt : List.Perm (cands1.filter (·.evidenceTagged)) (cands2.filter (·.evidenceTagged)) :=
    hperm.filter _
  have hfold := foldl_pickMinBy_perm obj hfilt (huniq.filter _)
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
  simp only [selectBy, hempty, hte, hany, hfold]

/-- A strictly monotone map of keys leaves the fold step unchanged. -/
theorem pickMinBy_strictMono {K' : Type} [LinearOrder K'] (obj : Cand (K := ℚ) src → K)
    {g : K → K'} (hg : StrictMono g) :
    pickMinBy (g ∘ obj) = pickMinBy obj := by
  funext acc c
  cases acc with
  | none => rfl
  | some b => simp only [pickMinBy, Function.comp, hg.lt_iff_lt]

/-- A strictly monotone map of keys leaves the baseline admission unchanged. -/
theorem Baseline.improves_map_strictMono {K' : Type} [LinearOrder K'] {g : K → K'}
    (hg : StrictMono g) (b : Baseline K) (x : K) :
    (g <$> b).improves (g x) = b.improves x := by
  cases b with
  | incumbent k => simp only [Baseline.map_incumbent, Baseline.improves, hg.lt_iff_lt]
  | «open» => rfl

/-- **Strictly monotone invariance**: re-keying the objective and the baseline by a strictly
    monotone `g` selects the same result. -/
theorem selectBy_strictMono_invariant {K' : Type} [LinearOrder K'] (obj : Cand (K := ℚ) src → K)
    {g : K → K'} (hg : StrictMono g) (b : Baseline K) (cands : List (Cand (K := ℚ) src)) :
    selectBy (g ∘ obj) (g <$> b) cands = selectBy obj b cands := by
  unfold selectBy
  rw [pickMinBy_strictMono obj hg]
  have hb : ∀ c, (g <$> b).improves ((g ∘ obj) c) = b.improves (obj c) :=
    fun c => Baseline.improves_map_strictMono hg b (obj c)
  simp only [hb]

/-- One fold step keeps the new candidate or the accumulated one, with key no larger than either. -/
theorem pickMinBy_spec (obj : Cand (K := ℚ) src → K) (acc : Option (Cand (K := ℚ) src))
    (x : Cand (K := ℚ) src) :
    ∃ r, pickMinBy obj acc x = some r ∧ (r = x ∨ acc = some r) ∧ obj r ≤ obj x ∧
      ∀ a, acc = some a → obj r ≤ obj a := by
  have key_le : ∀ {a b : Cand (K := ℚ) src}, candKeyBy obj a ≤ candKeyBy obj b → obj a ≤ obj b := by
    intro a b h
    simp only [candKeyBy, Prod.Lex.le_iff] at h
    rcases h with h | h
    · exact h.le
    · exact h.1.le
  cases acc with
  | none => exact ⟨x, rfl, Or.inl rfl, le_rfl, fun a h => by cases h⟩
  | some b =>
    refine ⟨minCandBy obj b x, pickMinBy_eq_lex obj b x, ?_, ?_, ?_⟩
    · unfold minCandBy; split_ifs <;> simp
    · unfold minCandBy; split_ifs with h
      · exact le_rfl
      · exact key_le (le_of_not_gt h)
    · intro a ha
      cases ha
      unfold minCandBy; split_ifs with h
      · exact key_le h.le
      · exact le_rfl

/-- The fold's result is a list member or the seed, with key no larger than any member or the seed. -/
theorem foldl_pickMinBy_spec (obj : Cand (K := ℚ) src → K) (l : List (Cand (K := ℚ) src))
    (acc : Option (Cand (K := ℚ) src)) (m : Cand (K := ℚ) src)
    (h : l.foldl (pickMinBy obj) acc = some m) :
    (m ∈ l ∨ acc = some m) ∧ (∀ x ∈ l, obj m ≤ obj x) ∧ ∀ a, acc = some a → obj m ≤ obj a := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨Or.inr rfl, (fun x hx => by cases hx), (fun a ha => by cases ha; exact le_rfl)⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨r, hr, hrmem, hrx, hracc⟩ := pickMinBy_spec obj acc x
    rw [hr] at h
    obtain ⟨hmem, hle, hseed⟩ := ih (some r) h
    have hmr : obj m ≤ obj r := hseed r rfl
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

/-- A returned candidate is the fold's minimum over the tagged candidates and passes the baseline. -/
theorem selectBy_inl_spec (obj : Cand (K := ℚ) src → K) (b : Baseline K)
    (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : selectBy obj b cands = Sum.inl c) :
    (cands.filter (fun c => c.evidenceTagged)).foldl (pickMinBy obj) none = some c ∧
      b.improves (obj c) = true := by
  unfold selectBy at hsel
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

/-- **Membership**: the winner is a member of the evidence-tagged list. -/
theorem selectBy_mem (obj : Cand (K := ℚ) src → K) (b : Baseline K)
    (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : selectBy obj b cands = Sum.inl c) :
    c ∈ cands.filter (fun c => c.evidenceTagged) := by
  obtain ⟨hf, -⟩ := selectBy_inl_spec obj b cands c hsel
  exact ((foldl_pickMinBy_spec obj _ none c hf).1).resolve_right (by simp)

/-- **Minimality**: the winner's key is `≤` every evidence-tagged candidate's key. -/
theorem selectBy_minimal (obj : Cand (K := ℚ) src → K) (b : Baseline K)
    (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : selectBy obj b cands = Sum.inl c) :
    ∀ c' ∈ cands, c'.evidenceTagged = true → obj c ≤ obj c' := by
  obtain ⟨hf, -⟩ := selectBy_inl_spec obj b cands c hsel
  intro c' hc' ht
  exact (foldl_pickMinBy_spec obj _ none c hf).2.1 c' (List.mem_filter.2 ⟨hc', ht⟩)

/-- **Improvement**: under an incumbent `k` the winner's key is strictly below `k`. -/
theorem selectBy_improves_incumbent (obj : Cand (K := ℚ) src → K) (k : K)
    (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : selectBy obj (.incumbent k) cands = Sum.inl c) : obj c < k := by
  have h := (selectBy_inl_spec obj _ cands c hsel).2
  simpa [Baseline.improves] using h

end Generic

/-- `select_minimal` re-derived from the general theorems through `select_eq_selectBy`. -/
theorem select_minimal_of_selectBy {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src)
    (hsel : select src cands = Sum.inl c) :
    c ∈ cands ∧ c.evidenceTagged = true ∧
      (∀ c' ∈ cands, c'.evidenceTagged = true → candEnergy (src := src) c ≤ candEnergy (src := src) c') ∧
      candEnergy (src := src) c < jointFreeEnergy src := by
  rw [select_eq_selectBy] at hsel
  have hm := List.mem_filter.1 (selectBy_mem _ _ cands c hsel)
  exact ⟨hm.1, hm.2, selectBy_minimal _ _ cands c hsel, selectBy_improves_incumbent _ _ cands c hsel⟩

end UMST.Excitement
