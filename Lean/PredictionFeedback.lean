-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: PredictionFeedback.lean

  A turn of the learning loop states a prediction, observes the outcome and acts on what it predicted. The turn is
  an instance of the `measureFeedback` case of the one predicate `UMST.ProcessFamily.SecondLaw`, judged against the
  joint distribution of prediction and outcome:

  * the work the loop extracts by acting on its prediction is at most the free-energy drop plus k_B T times the
    mutual information between prediction and outcome (`turn_work_le`), and at most k_B T times that information
    for a cyclic turn (`turn_cyclic_work_le`); two admissible turns at one bath add (`turn_pair_work_le`);
  * a summary of the receipts carries no more mutual information about the outcome than the receipts, so every work
    admitted against the summary is admitted against the receipts and every work the receipts refuse the summary
    refuses (`summary_admitted_receipts`, `receipts_refused_summary`, for any informations ordered so); for a
    deterministic summary `f` of the receipts the order is the classical data-processing inequality
    `ClassicalDPI.mutualInformation_summary_le`, a theorem (`summary_admitted_receipts_of_summary`): the meter reads
    the receipts, the close-guard reading;
  * over the loop's decisions, the summed error of the gated choices is at most the summed prediction error plus
    the summed gate moves δ (`gated_error_sum_le`, each decision through
    `SeparationBound.accuracy_safety_separation_real`).

  Zero `axiom`, zero `sorry`.
-/

import Process
import SeparationBound
import ClassicalDPI

open Real UMST.LandauerLaw UMST.ProcessFamily UMST.InfoTheory UMST.InfoTheory.JointDist

namespace UMST.PredictionFeedback

/-- One prediction-then-observation turn: the bath, the work the loop extracts by acting on its prediction, the free
    energy change of the system, and the joint distribution of prediction (rows) and outcome (columns). -/
structure Turn where
  bath : HeatBath
  extWork : ℝ
  deltaFreeEnergy : ℝ
  {n m : ℕ}
  joint : JointDist n m

/-- The turn as a process of the family: a measurement with feedback. -/
def Turn.process (t : Turn) : Process := .measureFeedback ⟨t.bath, t.extWork, t.deltaFreeEnergy⟩

/-- A turn is admissible when it obeys the one predicate against its prediction–outcome joint. -/
def Turn.Admissible (t : Turn) : Prop := SecondLaw t.process (.feedback t.joint)

/-- **The turn is a `measureFeedback` instance**: admissibility is the Sagawa–Ueda inequality at the mutual
    information between prediction and outcome. -/
theorem turn_admissible_iff (t : Turn) :
    t.Admissible ↔
      t.extWork ≤ -t.deltaFreeEnergy + kB * t.bath.bathTemp.val * mutualInformation t.joint :=
  Iff.rfl

theorem turn_work_le (t : Turn) (h : t.Admissible) :
    t.extWork ≤ -t.deltaFreeEnergy + kB * t.bath.bathTemp.val * mutualInformation t.joint := h

/-- A cyclic turn (no free-energy change) extracts at most k_B T times the information its prediction carries. -/
theorem turn_cyclic_work_le (t : Turn) (h : t.Admissible) (hF : t.deltaFreeEnergy = 0) :
    t.extWork ≤ kB * t.bath.bathTemp.val * mutualInformation t.joint := by
  have := turn_work_le t h
  rw [hF, neg_zero, zero_add] at this
  exact this

/-- Two admissible turns at one bath: their works add under the summed free-energy drops and informations. -/
theorem turn_pair_work_le (s t : Turn) (hT : s.bath.bathTemp.val = t.bath.bathTemp.val)
    (hs : s.Admissible) (ht : t.Admissible) :
    s.extWork + t.extWork ≤
      -(s.deltaFreeEnergy + t.deltaFreeEnergy) +
        kB * s.bath.bathTemp.val * (mutualInformation s.joint + mutualInformation t.joint) := by
  have h1 := turn_work_le s hs
  have h2 := turn_work_le t ht
  rw [← hT] at h2
  linarith

/-- The same turn judged against another joint (the receipts, or a summary of them). -/
def Turn.against (t : Turn) {n' m' : ℕ} (J : JointDist n' m') : Turn :=
  { bath := t.bath, extWork := t.extWork, deltaFreeEnergy := t.deltaFreeEnergy, joint := J }

/-- **Data-processing corollary**: when a summary carries no more information about the outcome than the receipts,
    every work admitted against the summary is admitted against the receipts. -/
theorem summary_admitted_receipts (t : Turn) {n' m' n'' m'' : ℕ} (summary : JointDist n' m')
    (receipts : JointDist n'' m'') (hDPI : mutualInformation summary ≤ mutualInformation receipts)
    (h : (t.against summary).Admissible) : (t.against receipts).Admissible := by
  have hk : 0 ≤ kB * t.bath.bathTemp.val := mul_nonneg kB_pos.le t.bath.bathTemp.property.le
  have h' : t.extWork ≤ -t.deltaFreeEnergy + kB * t.bath.bathTemp.val * mutualInformation summary := h
  show t.extWork ≤ -t.deltaFreeEnergy + kB * t.bath.bathTemp.val * mutualInformation receipts
  nlinarith [mul_le_mul_of_nonneg_left hDPI hk]

/-- **Data-processing corollary**, contrapositive: a work the receipts refuse, the summary refuses. -/
theorem receipts_refused_summary (t : Turn) {n' m' n'' m'' : ℕ} (summary : JointDist n' m')
    (receipts : JointDist n'' m'') (hDPI : mutualInformation summary ≤ mutualInformation receipts)
    (h : ¬ (t.against receipts).Admissible) : ¬ (t.against summary).Admissible :=
  fun hs => h (summary_admitted_receipts t summary receipts hDPI hs)

/-- A gated decision of the loop: the prediction `p`, the gated choice `g`, the outcome `y` and the gate's move
    bound `δ`. -/
abbrev Decision := ℝ × ℝ × ℝ × ℝ

/-- **Data-processing corollary, discharged**: a work admitted against the summary `f(Y)` of the receipts `Y` is
    admitted against the receipts, the inequality `I(X; f(Y)) ≤ I(X; Y)` being the theorem
    `ClassicalDPI.mutualInformation_summary_le`, not a hypothesis. -/
theorem summary_admitted_receipts_of_summary (t : Turn) {n m k : ℕ} (receipts : JointDist n m) (f : Fin m → Fin k)
    (h : (t.against (UMST.ClassicalDPI.summary receipts f)).Admissible) : (t.against receipts).Admissible :=
  summary_admitted_receipts t _ receipts (UMST.ClassicalDPI.mutualInformation_summary_le receipts f) h

/-- **Separation corollary**, over the loop's decisions: when the gate moves each prediction by at most its `δ`, the
    summed error of the gated choices is at most the summed prediction error plus the summed moves, each decision
    bounded by `SeparationBound.accuracy_safety_separation_real`. -/
theorem gated_error_sum_le (l : List Decision) (h : ∀ q ∈ l, |q.2.1 - q.1| ≤ q.2.2.2) :
    (l.map fun q => |q.2.1 - q.2.2.1|).sum ≤
      (l.map fun q => |q.1 - q.2.2.1|).sum + (l.map fun q => q.2.2.2).sum := by
  induction l with
  | nil => simp
  | cons q l ih =>
    have hq := UMST.accuracy_safety_separation_real q.1 q.2.1 q.2.2.1 q.2.2.2 (h q (List.mem_cons_self q l))
    have hl := ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    simp only [List.map_cons, List.sum_cons]
    linarith

end UMST.PredictionFeedback
