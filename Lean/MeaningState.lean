-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: MeaningState.lean

  **HCOM-002 — Categorical semantics** (Human Communication Blueprint §3.2).

  Objects = `MeaningState` (geometric shape bundle + context/timestamp);
  morphisms = `CoreAdmissibleCommunication`; multi-turn dialogue = Kleisli
  composition gated on `SemanticSecondLaw` admissibility.

  L₀ boundary: imports `SemanticSecondLaw` only (no `Gate.lean`).
  Kleisli composition theorem mirrors `Web.lean` / `KleisliAdmissibilityComposition`
  naming parity (`meaning_kleisliComposeWellTyped`).

  Single-axiom discipline: zero new Lean `axiom` declarations.
-/

import SemanticSecondLaw

open Real Finset UMST.LandauerLaw UMST.SemanticSecondLaw UMST.InfoTheory UMST.InfoTheory.JointDist

namespace UMST.MeaningState

-- ================================================================
-- SECTION 1: MeaningState objects (geometric layer scaffold)
-- ================================================================

/-- Shared-dialogue context (speaker / turn indexing — finite scaffold). -/
structure MeaningContext where
  dialogueId : ℕ
  turnIndex : ℕ

/-- **MeaningState**: geometric shape bundle over a finite alphabet, with
    context, timestamp, and semantic thermodynamic legs aligned with
    `CommunicativeTransition`. -/
structure MeaningState (n : ℕ) where
  context : MeaningContext
  timestamp : ℕ
  shapeDist : ProbDist n
  bath : SemanticBath
  understandingWork : ℝ
  consistencyDefect : ℝ

/-- Structural consistency at the object level (no contradictory shapes). -/
def structurallyConsistent {n : ℕ} (ms : MeaningState n) : Prop :=
  ms.consistencyDefect = 0

/-- Advance turn index while preserving dialogue identity. -/
def advanceTurn {n : ℕ} (ms : MeaningState n) : MeaningState n where
  context := { dialogueId := ms.context.dialogueId, turnIndex := ms.context.turnIndex + 1 }
  timestamp := ms.timestamp + 1
  shapeDist := ms.shapeDist
  bath := ms.bath
  understandingWork := ms.understandingWork
  consistencyDefect := ms.consistencyDefect

/-- Lift a `MeaningState` to the `CommunicativeTransition` reporting carrier. -/
def toCommunicativeTransition {n : ℕ} (ms : MeaningState n) : CommunicativeTransition n where
  bath := ms.bath
  prior := ms.shapeDist
  post := ms.shapeDist
  understandingWork := ms.understandingWork
  consistencyDefect := ms.consistencyDefect

/-- Pairwise communicative transition between prior and post meaning states. -/
def communicativeTransitionBetween {n : ℕ} (prior post : MeaningState n) : CommunicativeTransition n where
  bath := post.bath
  prior := prior.shapeDist
  post := post.shapeDist
  understandingWork := post.understandingWork
  consistencyDefect := post.consistencyDefect

-- ================================================================
-- SECTION 2: Core admissible communication (morphisms)
-- ================================================================

/-- **CoreAdmissibleCommunication**: single-step meaning transition preserving
    `semanticSecondLaw` invariants on the declared joint witness. -/
structure CoreAdmissibleCommunication (n m : ℕ) where
  prior : MeaningState n
  post : MeaningState n
  witness : ProposalOutcomeWitness n m
  miThreshold : ℝ

/-- A core communication step is admissible when both endpoints are structurally
    consistent and the induced `CommunicativeTransition` satisfies
    `admissibleSemanticTransition`. -/
def coreAdmissible {n m : ℕ} (c : CoreAdmissibleCommunication n m) : Prop :=
  structurallyConsistent c.prior ∧
  structurallyConsistent c.post ∧
  admissibleSemanticTransition c.miThreshold
    (communicativeTransitionBetween c.prior c.post) c.witness

/-- Alias aligned with blueprint vocabulary. -/
abbrev CoreAdmissible {n m : ℕ} (c : CoreAdmissibleCommunication n m) : Prop :=
  coreAdmissible c

theorem coreAdmissible_semanticSecondLaw {n m : ℕ} (c : CoreAdmissibleCommunication n m)
    (h : coreAdmissible c) :
    semanticSecondLaw c.miThreshold
      (communicativeTransitionBetween c.prior c.post) c.witness :=
  h.2.2

-- ================================================================
-- SECTION 3: Kleisli dialogue composition
-- ================================================================

/-- Kleisli arrow over meaning states (proposal → gated option). -/
def MeaningKleisliArrow (n : ℕ) : Type := MeaningState n → Option (MeaningState n)

/-- Well-typed dialogue arrow: every `some` output forms a `coreAdmissible` step
    from the input, using the supplied witness assignment. -/
def MeaningWellTyped (n m : ℕ) (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m)
    (f : MeaningKleisliArrow n) : Prop :=
  ∀ prior post, f prior = some post →
    coreAdmissible ⟨prior, post, witnessFor prior post, miThreshold⟩

/-- Graded n-step dialogue admissibility (Constitutional / KleisliN parity). -/
inductive MeaningAdmissibleSteps (n m : ℕ) (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m) :
    MeaningState n → MeaningState n → Prop where
  | zero {s} : MeaningAdmissibleSteps n m miThreshold witnessFor s s
  | succ {s s' s''} :
      coreAdmissible ⟨s, s', witnessFor s s', miThreshold⟩ →
      MeaningAdmissibleSteps n m miThreshold witnessFor s' s'' →
      MeaningAdmissibleSteps n m miThreshold witnessFor s s''

/-- Well-typed n-step dialogue arrow (graded Kleisli budget). -/
def MeaningWellTypedN (_steps : ℕ) (n m : ℕ) (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m)
    (f : MeaningKleisliArrow n) : Prop :=
  ∀ prior post, f prior = some post →
    MeaningAdmissibleSteps n m miThreshold witnessFor prior post

/-- Structural gate (decidable): reject posts with positive consistency defect. -/
noncomputable def meaningStructuralGateCheck {n : ℕ} (post : MeaningState n) : Bool :=
  decide (post.consistencyDefect = 0)

theorem meaningStructuralGateCheck_true_iff {n : ℕ} (post : MeaningState n) :
    meaningStructuralGateCheck post = true ↔ structurallyConsistent post := by
  unfold meaningStructuralGateCheck structurallyConsistent
  simp

/-- Proposal functor composed with the structural gate (runtime-fast leg). -/
noncomputable def makeMeaningGateArrow (n : ℕ) (propose : MeaningState n → MeaningState n) :
    MeaningKleisliArrow n :=
  fun prior =>
    let post := propose prior
    if meaningStructuralGateCheck post then some post else none

theorem makeMeaningGateArrowWellTyped {n m : ℕ} (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m)
    (propose : MeaningState n → MeaningState n)
    (hAdm : ∀ prior, coreAdmissible ⟨prior, propose prior, witnessFor prior (propose prior), miThreshold⟩) :
    MeaningWellTyped n m miThreshold witnessFor (makeMeaningGateArrow n propose) := by
  intro prior post h
  simp only [makeMeaningGateArrow] at h
  by_cases hg : meaningStructuralGateCheck (propose prior)
  · simp [hg] at h
    subst h
    exact hAdm prior
  · simp [hg] at h

/-- Back-compat alias (structural gate + per-step admissibility hypothesis). -/
theorem makeMeaningGateArrowWellTyped_structural {n m : ℕ} (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m)
    (propose : MeaningState n → MeaningState n)
    (hAdm : ∀ prior, coreAdmissible ⟨prior, propose prior, witnessFor prior (propose prior), miThreshold⟩) :
    MeaningWellTyped n m miThreshold witnessFor (makeMeaningGateArrow n propose) :=
  makeMeaningGateArrowWellTyped miThreshold witnessFor propose hAdm

noncomputable def meaningKleisliCompose {n : ℕ} (f g : MeaningKleisliArrow n) :
    MeaningKleisliArrow n :=
  fun s =>
    match f s with
    | none => none
    | some s' => g s'

/-- **Kleisli composition preserves graded admissibility** (dialogue subject reduction):
    if each atomic turn is `coreAdmissible`, their Kleisli composite is a 2-step path. -/
theorem meaningKleisliComposeWellTyped (n m : ℕ) (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m)
    (f g : MeaningKleisliArrow n)
    (hf : MeaningWellTyped n m miThreshold witnessFor f)
    (hg : MeaningWellTyped n m miThreshold witnessFor g) :
    ∀ prior post, meaningKleisliCompose f g prior = some post →
      MeaningAdmissibleSteps n m miThreshold witnessFor prior post := by
  intro s s'' hcomp
  simp only [meaningKleisliCompose] at hcomp
  match hfs : f s with
  | none => simp [hfs] at hcomp
  | some s' =>
    simp [hfs] at hcomp
    exact MeaningAdmissibleSteps.succ (hf s s' hfs)
      (MeaningAdmissibleSteps.succ (hg s' s'' hcomp) (MeaningAdmissibleSteps.zero (s := s'')))

/-- Single-step well-typedness yields a graded admissible path. -/
theorem meaningWellTyped_one (n m : ℕ) (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m)
    (f : MeaningKleisliArrow n) (hf : MeaningWellTyped n m miThreshold witnessFor f) :
    MeaningWellTypedN 1 n m miThreshold witnessFor f := by
  intro prior post h
  exact MeaningAdmissibleSteps.succ (hf prior post h) (MeaningAdmissibleSteps.zero (s := post))

/-- Graded Kleisli composition re-export (Economic / Web naming parity). -/
theorem meaning_kleisliComposeWellTyped (n m : ℕ) (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m)
    (f g : MeaningKleisliArrow n)
    (hf : MeaningWellTyped n m miThreshold witnessFor f)
    (hg : MeaningWellTyped n m miThreshold witnessFor g) :
    ∀ prior post, meaningKleisliCompose f g prior = some post →
      MeaningAdmissibleSteps n m miThreshold witnessFor prior post :=
  meaningKleisliComposeWellTyped n m miThreshold witnessFor f g hf hg

-- ================================================================
-- SECTION 4: Canonical fixtures (0 sorry — catalog witnesses)
-- ================================================================

/-- Degenerate P0 meaning state: uniform binary shape, zero defect. -/
noncomputable def consistentP0Meaning : MeaningState 2 where
  context := { dialogueId := 0, turnIndex := 0 }
  timestamp := 0
  shapeDist := uniformBinary
  bath := { bathTemp := ⟨300, by norm_num⟩ }
  understandingWork := 0
  consistencyDefect := 0

theorem consistentP0Meaning_structurallyConsistent :
    structurallyConsistent consistentP0Meaning := rfl

theorem consistentP0Meaning_zero_model_uncertainty_drop :
    modelUncertaintyDrop (communicativeTransitionBetween consistentP0Meaning consistentP0Meaning) = 0 := by
  unfold modelUncertaintyDrop communicativeTransitionBetween consistentP0Meaning
  ring

/-- Identity dialogue arrow (always returns input). -/
def meaningIdentityArrow (n : ℕ) : MeaningKleisliArrow n :=
  fun s => some s

theorem meaningIdentityArrowWellTyped (n m : ℕ) (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m)
    (hId : ∀ s, coreAdmissible ⟨s, s, witnessFor s s, miThreshold⟩) :
    MeaningWellTyped n m miThreshold witnessFor (meaningIdentityArrow n) := by
  intro prior post h
  simp only [meaningIdentityArrow] at h
  cases h
  exact hId prior

/-- Two-step dialogue: identity then identity yields a graded admissible path. -/
theorem meaningKleisliCompose_identity_identity (n m : ℕ) (miThreshold : ℝ)
    (witnessFor : MeaningState n → MeaningState n → ProposalOutcomeWitness n m)
    (hId : ∀ s, coreAdmissible ⟨s, s, witnessFor s s, miThreshold⟩) :
    ∀ s, meaningKleisliCompose (meaningIdentityArrow n) (meaningIdentityArrow n) s = some s →
      MeaningAdmissibleSteps n m miThreshold witnessFor s s := by
  intro s h
  apply meaningKleisliComposeWellTyped n m miThreshold witnessFor
  · exact meaningIdentityArrowWellTyped n m miThreshold witnessFor hId
  · exact meaningIdentityArrowWellTyped n m miThreshold witnessFor hId
  · exact h

/-- Product-witness dialogue step at threshold 0 (MI = 0). -/
theorem consistentP0_coreAdmissible_at_zero :
    coreAdmissible
      ⟨consistentP0Meaning, consistentP0Meaning,
        productWitness uniformBinary uniformBinary, 0⟩ := by
  refine ⟨consistentP0Meaning_structurallyConsistent,
    consistentP0Meaning_structurallyConsistent, ?_⟩
  unfold admissibleSemanticTransition semanticSecondLaw
  refine ⟨rfl, ?_, productWitness_miPreserved_at_zero uniformBinary uniformBinary⟩
  rw [consistentP0Meaning_zero_model_uncertainty_drop]
  unfold communicativeTransitionBetween consistentP0Meaning
  simp only [zero_div, le_refl]

/-- Catalog witness marker: categorical meaning-state module is present. -/
theorem meaning_state_module_witness : True := trivial

end UMST.MeaningState
