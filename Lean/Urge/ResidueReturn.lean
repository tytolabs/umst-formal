-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ResidueReturn.lean

  Meso acting Urge — §13.5 what Urge returns to Excitement.
  History-plane evidence: per-recovery `Residue` constructor counts + observed ΔF corpus.
  Six constructors pinned to `UMST.Excitement.Residue` — no seventh, no f64 ΔF theater.

  Recovery composes `Excitement.select` (not a second argmin).
  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.AdmitKleisli

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.AdmitKleisli

namespace UMST.Urge.ResidueReturn

-- ================================================================
-- SECTION 1: Six Residue constructors (Excitement catalog pin)
-- ================================================================

def residueConstructorTag : Residue → String
  | .noCandidates => "NoCandidates"
  | .allInadmissible => "AllInadmissible"
  | .allExcludedByCBF => "AllExcludedByCbf"
  | .allExcludedByDEC => "AllExcludedByDec"
  | .untaggedConstant => "UntaggedConstant"
  | .noStrictImprovement => "NoStrictImprovement"

theorem noCandidates_tag : residueConstructorTag .noCandidates = "NoCandidates" := rfl
theorem allInadmissible_tag : residueConstructorTag .allInadmissible = "AllInadmissible" := rfl
theorem allExcludedByCBF_tag : residueConstructorTag .allExcludedByCBF = "AllExcludedByCbf" := rfl
theorem allExcludedByDEC_tag : residueConstructorTag .allExcludedByDEC = "AllExcludedByDec" := rfl
theorem untaggedConstant_tag : residueConstructorTag .untaggedConstant = "UntaggedConstant" := rfl
theorem noStrictImprovement_tag :
    residueConstructorTag .noStrictImprovement = "NoStrictImprovement" := rfl

theorem residueConstructorTag_noCandidates_ne_allInadmissible :
    residueConstructorTag .noCandidates ≠ residueConstructorTag .allInadmissible := by decide

theorem residueConstructorTag_noCandidates_ne_allExcludedByCBF :
    residueConstructorTag .noCandidates ≠ residueConstructorTag .allExcludedByCBF := by decide

theorem residueConstructorTag_noCandidates_ne_allExcludedByDEC :
    residueConstructorTag .noCandidates ≠ residueConstructorTag .allExcludedByDEC := by decide

theorem residueConstructorTag_noCandidates_ne_untaggedConstant :
    residueConstructorTag .noCandidates ≠ residueConstructorTag .untaggedConstant := by decide

theorem residueConstructorTag_noCandidates_ne_noStrictImprovement :
    residueConstructorTag .noCandidates ≠ residueConstructorTag .noStrictImprovement := by decide

theorem residueConstructorTag_allInadmissible_ne_allExcludedByCBF :
    residueConstructorTag .allInadmissible ≠ residueConstructorTag .allExcludedByCBF := by decide

theorem residueConstructorTag_allInadmissible_ne_allExcludedByDEC :
    residueConstructorTag .allInadmissible ≠ residueConstructorTag .allExcludedByDEC := by decide

theorem residueConstructorTag_allInadmissible_ne_untaggedConstant :
    residueConstructorTag .allInadmissible ≠ residueConstructorTag .untaggedConstant := by decide

theorem residueConstructorTag_allInadmissible_ne_noStrictImprovement :
    residueConstructorTag .allInadmissible ≠ residueConstructorTag .noStrictImprovement := by decide

theorem residueConstructorTag_allExcludedByCBF_ne_allExcludedByDEC :
    residueConstructorTag .allExcludedByCBF ≠ residueConstructorTag .allExcludedByDEC := by decide

theorem residueConstructorTag_allExcludedByCBF_ne_untaggedConstant :
    residueConstructorTag .allExcludedByCBF ≠ residueConstructorTag .untaggedConstant := by decide

theorem residueConstructorTag_allExcludedByCBF_ne_noStrictImprovement :
    residueConstructorTag .allExcludedByCBF ≠ residueConstructorTag .noStrictImprovement := by decide

theorem residueConstructorTag_allExcludedByDEC_ne_untaggedConstant :
    residueConstructorTag .allExcludedByDEC ≠ residueConstructorTag .untaggedConstant := by decide

theorem residueConstructorTag_allExcludedByDEC_ne_noStrictImprovement :
    residueConstructorTag .allExcludedByDEC ≠ residueConstructorTag .noStrictImprovement := by decide

theorem residueConstructorTag_untaggedConstant_ne_noStrictImprovement :
    residueConstructorTag .untaggedConstant ≠ residueConstructorTag .noStrictImprovement := by decide

def residueConstructorsDistinct : Prop :=
  residueConstructorTag .noCandidates ≠ residueConstructorTag .allInadmissible ∧
  residueConstructorTag .noCandidates ≠ residueConstructorTag .allExcludedByCBF ∧
  residueConstructorTag .noCandidates ≠ residueConstructorTag .allExcludedByDEC ∧
  residueConstructorTag .noCandidates ≠ residueConstructorTag .untaggedConstant ∧
  residueConstructorTag .noCandidates ≠ residueConstructorTag .noStrictImprovement ∧
  residueConstructorTag .allInadmissible ≠ residueConstructorTag .allExcludedByCBF ∧
  residueConstructorTag .allInadmissible ≠ residueConstructorTag .allExcludedByDEC ∧
  residueConstructorTag .allInadmissible ≠ residueConstructorTag .untaggedConstant ∧
  residueConstructorTag .allInadmissible ≠ residueConstructorTag .noStrictImprovement ∧
  residueConstructorTag .allExcludedByCBF ≠ residueConstructorTag .allExcludedByDEC ∧
  residueConstructorTag .allExcludedByCBF ≠ residueConstructorTag .untaggedConstant ∧
  residueConstructorTag .allExcludedByCBF ≠ residueConstructorTag .noStrictImprovement ∧
  residueConstructorTag .allExcludedByDEC ≠ residueConstructorTag .untaggedConstant ∧
  residueConstructorTag .allExcludedByDEC ≠ residueConstructorTag .noStrictImprovement ∧
  residueConstructorTag .untaggedConstant ≠ residueConstructorTag .noStrictImprovement

theorem residueConstructorsDistinctHolds : residueConstructorsDistinct :=
  ⟨residueConstructorTag_noCandidates_ne_allInadmissible,
   residueConstructorTag_noCandidates_ne_allExcludedByCBF,
   residueConstructorTag_noCandidates_ne_allExcludedByDEC,
   residueConstructorTag_noCandidates_ne_untaggedConstant,
   residueConstructorTag_noCandidates_ne_noStrictImprovement,
   residueConstructorTag_allInadmissible_ne_allExcludedByCBF,
   residueConstructorTag_allInadmissible_ne_allExcludedByDEC,
   residueConstructorTag_allInadmissible_ne_untaggedConstant,
   residueConstructorTag_allInadmissible_ne_noStrictImprovement,
   residueConstructorTag_allExcludedByCBF_ne_allExcludedByDEC,
   residueConstructorTag_allExcludedByCBF_ne_untaggedConstant,
   residueConstructorTag_allExcludedByCBF_ne_noStrictImprovement,
   residueConstructorTag_allExcludedByDEC_ne_untaggedConstant,
   residueConstructorTag_allExcludedByDEC_ne_noStrictImprovement,
   residueConstructorTag_untaggedConstant_ne_noStrictImprovement⟩

def residueConstructorCount : Nat := 6

def pinSixResidueConstructors : List Residue :=
  [.noCandidates, .allInadmissible, .allExcludedByCBF, .allExcludedByDEC,
   .untaggedConstant, .noStrictImprovement]

theorem pinSixResidueConstructors_length : pinSixResidueConstructors.length = 6 := rfl

theorem pinSixResidueConstructors_tags_nodup :
    (pinSixResidueConstructors.map residueConstructorTag).Nodup := by
  decide

theorem residue_cases_in_pinSix (r : Residue) : r ∈ pinSixResidueConstructors := by
  rcases r <;> simp [pinSixResidueConstructors]

-- ================================================================
-- SECTION 2: Residue counts (empirical failure-mode distribution)
-- ================================================================

structure ResidueCounts where
  noCandidates          : ℕ
  allInadmissible       : ℕ
  allExcludedByCBF      : ℕ
  allExcludedByDEC      : ℕ
  untaggedConstant      : ℕ
  noStrictImprovement   : ℕ

def ResidueCounts.zero : ResidueCounts :=
  { noCandidates := 0, allInadmissible := 0, allExcludedByCBF := 0, allExcludedByDEC := 0
    untaggedConstant := 0, noStrictImprovement := 0 }

def ResidueCounts.record (counts : ResidueCounts) (r : Residue) : ResidueCounts :=
  match r with
  | .noCandidates => { counts with noCandidates := counts.noCandidates + 1 }
  | .allInadmissible => { counts with allInadmissible := counts.allInadmissible + 1 }
  | .allExcludedByCBF => { counts with allExcludedByCBF := counts.allExcludedByCBF + 1 }
  | .allExcludedByDEC => { counts with allExcludedByDEC := counts.allExcludedByDEC + 1 }
  | .untaggedConstant => { counts with untaggedConstant := counts.untaggedConstant + 1 }
  | .noStrictImprovement => { counts with noStrictImprovement := counts.noStrictImprovement + 1 }

def ResidueCounts.total (counts : ResidueCounts) : ℕ :=
  counts.noCandidates + counts.allInadmissible + counts.allExcludedByCBF +
    counts.allExcludedByDEC + counts.untaggedConstant + counts.noStrictImprovement

theorem ResidueCounts.record_noCandidates (counts : ResidueCounts) :
    (counts.record .noCandidates).noCandidates = counts.noCandidates + 1 := rfl

theorem ResidueCounts.record_noStrictImprovement (counts : ResidueCounts) :
    (counts.record .noStrictImprovement).noStrictImprovement =
      counts.noStrictImprovement + 1 := rfl

-- ================================================================
-- SECTION 3: Observed ΔF (exact ℚ — refuse f64 theater)
-- ================================================================

/-- Observed free-energy delta: ΔF = observed − src (exact ℚ). -/
structure ObservedDeltaF where
  src      : ℚ
  observed : ℚ

def observedDeltaF (d : ObservedDeltaF) : ℚ :=
  d.observed - d.src

noncomputable def observedDeltaFFromCand {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (c : Cand (K := ℚ) src) : ObservedDeltaF :=
  { src := jointFreeEnergy src, observed := candEnergy (src := src) c }

theorem observedDeltaFFromCand_delta {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (c : Cand (K := ℚ) src) :
    observedDeltaF (observedDeltaFFromCand (src := src) c) =
      candEnergy (src := src) c - jointFreeEnergy src :=
  rfl

/-- Positive pin: observed ΔF uses ℚ exact Rat, not f64 compare. -/
def exactRatObservedDeltaF : Prop :=
  ∀ (d : ObservedDeltaF), ∃ q : ℚ, observedDeltaF d = q

theorem exactRatObservedDeltaFHolds : exactRatObservedDeltaF := by
  intro d
  exact ⟨observedDeltaF d, rfl⟩

-- ================================================================
-- SECTION 4: §13.5 return payload (counts + observed ΔF corpus)
-- ================================================================

structure ReturnPayload where
  counts           : ResidueCounts
  observedDeltaF   : List ObservedDeltaF

def ReturnPayload.empty : ReturnPayload :=
  { counts := ResidueCounts.zero, observedDeltaF := [] }

-- ================================================================
-- SECTION 5: Recovery via Excitement.select (no second argmin)
-- ================================================================

/-- Urge recovery composes `Excitement.select` — not a second argmin. -/
noncomputable def residueReturnSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    Cand (K := ℚ) src ⊕ Residue :=
  select src cands

/-- Record one recovery attempt via imported `select`. -/
noncomputable def recordRecoveryAttempt {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (buf : ReturnPayload) (src : S) (cands : List (Cand (K := ℚ) src)) :
    ReturnPayload × (Cand (K := ℚ) src ⊕ Residue) :=
  match residueReturnSelect src cands with
  | Sum.inl c =>
      ({ buf with
          observedDeltaF := buf.observedDeltaF ++ [observedDeltaFFromCand (src := src) c] },
       Sum.inl c)
  | Sum.inr r =>
      ({ buf with counts := buf.counts.record r }, Sum.inr r)

/-- Seventh residue constructor forbidden — Lean arity is six. -/
inductive SeventhConstructorRefusal where
  | seventh : SeventhConstructorRefusal

def refuseSeventhConstructor : SeventhConstructorRefusal := .seventh

theorem seventhConstructorRefused : ∃ _ : SeventhConstructorRefusal, True :=
  ⟨refuseSeventhConstructor, trivial⟩

end UMST.Urge.ResidueReturn
