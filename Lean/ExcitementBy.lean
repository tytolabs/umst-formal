-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST.ExcitementBy — the one selection fold over any linear order.

  `selectBy obj b` folds the evidence-tagged candidates with `pickMinBy obj` (ties broken by `id`)
  and admits the winner against the baseline `b`: `Baseline.incumbent k` requires `obj c < k`,
  `Baseline.open` returns the winner. The existing `select` is the instance at `candEnergy` with
  incumbent `jointFreeEnergy src` (`select_eq_selectBy`), so every caller of `select` keeps its
  behaviour. Rust twin: `umst-algebra/src/select_by.rs` (`SELECT_BY_LEAN_ANCHOR`).
  Specification: `workspace/docs/blueprints/UMST_SELECTION_PROPERTY_EVALUATION.md` §3.1, §5.1.
-/
import Excitement
import Mathlib.Data.Prod.Lex

namespace UMST.Excitement

open UMST.Core

/-- The improvement baseline of a selection: a strict incumbent key, or none. -/
inductive Baseline (K : Type) where
  | incumbent (k : K)
  | «open»
  deriving DecidableEq, Repr

namespace Baseline

/-- Transport a baseline along a map of keys. -/
def map {K K' : Type} (g : K → K') : Baseline K → Baseline K'
  | incumbent k => incumbent (g k)
  | «open» => «open»

instance : Functor Baseline where
  map := Baseline.map

@[simp] theorem map_incumbent {K K' : Type} (g : K → K') (k : K) :
    g <$> (incumbent k : Baseline K) = incumbent (g k) := rfl

@[simp] theorem map_open {K K' : Type} (g : K → K') :
    g <$> («open» : Baseline K) = «open» := rfl

/-- `b.improves x`: the key `x` is admitted against the baseline `b`. -/
def improves {K : Type} [LinearOrder K] : Baseline K → K → Bool
  | incumbent k, x => decide (x < k)
  | «open», _ => true

end Baseline

section Generic

variable {K S : Type} [LinearOrder K] [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] {src : S}

/-- One fold step over the objective `obj`: the lower key wins, ties broken by the lower `id`. -/
def pickMinBy (obj : Cand (K := ℚ) src → K) (acc : Option (Cand (K := ℚ) src))
    (c : Cand (K := ℚ) src) : Option (Cand (K := ℚ) src) :=
  match acc with
  | none => some c
  | some b =>
      if obj c < obj b then some c
      else if obj b < obj c then some b
      else if c.id < b.id then some c else some b

/-- The lexicographic key `(obj c, c.id)` that `pickMinBy` minimises. -/
def candKeyBy (obj : Cand (K := ℚ) src → K) (c : Cand (K := ℚ) src) : K ×ₗ Nat :=
  toLex (obj c, c.id)

/-- Binary lexicographic minimum on `candKeyBy obj`. -/
def minCandBy (obj : Cand (K := ℚ) src → K) (a b : Cand (K := ℚ) src) : Cand (K := ℚ) src :=
  if candKeyBy obj b < candKeyBy obj a then b else a

/-- The one selection fold: evidence filter, `pickMinBy obj` fold, baseline admission. The source
    state is implicit, fixed by the candidate type `Cand src`. -/
def selectBy (obj : Cand (K := ℚ) src → K) (b : Baseline K) (cands : List (Cand (K := ℚ) src)) :
    Cand (K := ℚ) src ⊕ Residue :=
  if cands.isEmpty then Sum.inr Residue.noCandidates
  else
    let tagged := cands.filter (fun c => c.evidenceTagged)
    if tagged.isEmpty then
      if cands.any (fun c => !c.evidenceTagged) then Sum.inr Residue.allInadmissible
      else Sum.inr Residue.untaggedConstant
    else
      match tagged.foldl (pickMinBy obj) none with
      | none => Sum.inr Residue.allInadmissible
      | some c =>
          if b.improves (obj c) then Sum.inl c
          else Sum.inr Residue.noStrictImprovement

end Generic

/-- The existing fold step is `pickMinBy` at `candEnergy`. -/
theorem pickMin_eq_pickMinBy {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} :
    pickMin (src := src) = pickMinBy (candEnergy (src := src)) := by
  funext acc c
  cases acc <;> rfl

/-- **`select` is `selectBy`** at `candEnergy` with the incumbent `jointFreeEnergy src`. -/
theorem select_eq_selectBy {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cs : List (Cand (K := ℚ) src)) :
    select src cs =
      selectBy (candEnergy (src := src)) (.incumbent (jointFreeEnergy src)) cs := by
  unfold select selectBy
  rw [pickMin_eq_pickMinBy]
  simp only [Baseline.improves, decide_eq_true_eq]
  rfl

end UMST.Excitement
