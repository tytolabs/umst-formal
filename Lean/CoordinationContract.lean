-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: CoordinationContract.lean

  The contract a coordination runtime honours (umst-ucrs implements it in Rust). Four laws, each stated over the
  Landauer cost of `CoordinationCost` and grounded in the second law through `landauerBitEnergy_pos`:

  * admission: a sync admitted within its budget pays a cost in `[0, budget]`;
  * clock drift: drift never decreases along a trace of nonnegative increments (a fold, any length);
  * Byzantine isolation: the honest credit projection is unchanged by any faulty cohort;
  * wire order: `n` advances move the sequence number by exactly `n`.

  Coq `Coq/CoordinationContract.v`, Agda `Agda/CoordinationContract.agda` and Haskell
  `Haskell/UMST/CoordinationContract.hs` state the same laws; Agda and Coq take the bit energy as a nonnegative
  parameter, which Lean instantiates with `landauerBitEnergy T`.
-/

import CoordinationCost

open Real UMST.CoordinationCost

namespace UMST.CoordinationContract

/-- Landauer cost is nonnegative for a physical temperature and a nonnegative bit count. -/
theorem landauerCostJoules_nonneg {bits T : ℝ} (hT : 0 < T) (hbits : 0 ≤ bits) :
    0 ≤ landauerCostJoules bits T :=
  mul_nonneg (landauerBitEnergy_pos hT).le hbits

/-- Landauer cost adds over disjoint bit counts (the tensor of two syncs costs the sum). -/
theorem landauerCostJoules_add (a b T : ℝ) :
    landauerCostJoules (a + b) T = landauerCostJoules a T + landauerCostJoules b T :=
  coordinationSaving_additive a b T

/-! ## Admission -/

/-- Thermal state of a clock sync: desync energy, budget and temperature. -/
structure ClockThermState where
  desyncEnergyJ : ℝ
  budgetJ : ℝ
  temperatureK : ℝ

/-- A sync of `bits` is admitted when its Landauer cost fits the budget and there is desync to resolve. -/
def admits (s : ClockThermState) (bits : ℝ) : Prop :=
  landauerCostJoules bits s.temperatureK ≤ s.budgetJ ∧ 0 < s.desyncEnergyJ

/-- An admitted sync pays a cost in `[0, budget]`. -/
theorem admitted_cost_bounded (s : ClockThermState) (bits : ℝ)
    (hT : 0 < s.temperatureK) (hbits : 0 ≤ bits) (h : admits s bits) :
    0 ≤ landauerCostJoules bits s.temperatureK ∧ landauerCostJoules bits s.temperatureK ≤ s.budgetJ :=
  ⟨landauerCostJoules_nonneg hT hbits, h.1⟩

/-- Admission needs a nonnegative budget: no sync is admitted against a debt. -/
theorem admitted_budget_nonneg (s : ClockThermState) (bits : ℝ)
    (hT : 0 < s.temperatureK) (hbits : 0 ≤ bits) (h : admits s bits) : 0 ≤ s.budgetJ :=
  (landauerCostJoules_nonneg hT hbits).trans h.1

/-! ## Clock drift -/

/-- Clock state: tick count and accumulated drift energy. -/
structure ClockState where
  tick : ℕ
  drift : ℝ

/-- One step: advance the tick and add a drift increment. -/
def clockStep (c : ClockState) (δ : ℝ) : ClockState :=
  { tick := c.tick + 1, drift := c.drift + δ }

/-- Run a trace of increments (a left fold of `clockStep`). -/
def clockRun (c : ClockState) (δs : List ℝ) : ClockState :=
  δs.foldl clockStep c

/-- Along a trace of nonnegative increments, drift never decreases and the tick advances by the trace length. -/
theorem clockRun_monotone (c : ClockState) (δs : List ℝ) (h : ∀ δ ∈ δs, 0 ≤ δ) :
    c.drift ≤ (clockRun c δs).drift ∧ (clockRun c δs).tick = c.tick + δs.length := by
  induction δs generalizing c with
  | nil => exact ⟨le_refl _, rfl⟩
  | cons δ rest ih =>
    have hδ : 0 ≤ δ := h δ (List.mem_cons_self _ _)
    have hrest : ∀ x ∈ rest, 0 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨hd, ht⟩ := ih (clockStep c δ) hrest
    refine ⟨?_, ?_⟩
    · have : c.drift ≤ (clockStep c δ).drift := by simp [clockStep]; linarith
      exact this.trans hd
    · show (clockRun (clockStep c δ) rest).tick = c.tick + (rest.length + 1)
      rw [ht]; simp [clockStep]; omega

/-! ## Byzantine isolation -/

/-- A participant of a sync mesh: identity, credit and fault flag. -/
structure Participant where
  id : ℕ
  credit : ℝ
  faulty : Bool

/-- The honest credit projection. -/
def honestCredits (ps : List Participant) : List ℝ :=
  (ps.filter (fun p => !p.faulty)).map (·.credit)

/-- A faulty cohort, wherever it joins, leaves the honest projection unchanged. -/
theorem honestCredits_append_faulty (ps fs : List Participant) (h : ∀ p ∈ fs, p.faulty = true) :
    honestCredits (ps ++ fs) = honestCredits ps := by
  have hf : fs.filter (fun p => !p.faulty) = [] :=
    List.filter_eq_nil_iff.mpr (fun p hp => by simp [h p hp])
  simp [honestCredits, List.filter_append, hf]

/-- A purely faulty cohort contributes nothing. -/
theorem honestCredits_faulty_only (fs : List Participant) (h : ∀ p ∈ fs, p.faulty = true) :
    honestCredits fs = [] := by
  simpa [honestCredits] using honestCredits_append_faulty [] fs h

/-! ## Wire order -/

/-- Wire transport stamp: a sequence number. -/
structure WireStamp where
  seq : ℕ

/-- Advance the wire sequence by one. -/
def wireNext (w : WireStamp) : WireStamp :=
  ⟨w.seq + 1⟩

/-- `n` advances move the sequence number by exactly `n`, so the order is strict and gap-free. -/
theorem wireNext_iterate (w : WireStamp) (n : ℕ) : (wireNext^[n] w).seq = w.seq + n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih]; simp [wireNext]; omega

end UMST.CoordinationContract
