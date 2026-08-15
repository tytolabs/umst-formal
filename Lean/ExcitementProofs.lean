/-
  UMST.ExcitementProofs — real theorems (no sorry).
-/
import Excitement
import Mathlib.Data.List.Perm.Basic

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

/-- Full list-permutation invariance of `select` (liquid-PPO reorder licence).
    Hypotheses: candidates are a permutation, and ids are pairwise distinct (E1B tie-break).
    **Open proof obligation (named):** `List.foldl pickMin` must be permutation-invariant on
    the filtered tagged sublist — requires `filter` commuting with `Perm` plus fold/pickMin
    associativity beyond the 2-element swap already proved above. -/
theorem select_perm_invariant {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S)
    (cands1 cands2 : List (Cand (K := ℚ) src))
    (hperm : List.Perm cands1 cands2)
    (_huniq : List.Pairwise (fun a b => a.id ≠ b.id) cands1) :
    select src cands1 = select src cands2 := by
  sorry

end UMST.Excitement
