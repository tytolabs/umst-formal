-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/MergeSafe.lean

  Meso acting Urge — §4 / §12 federated history merge safety.
  History merge **is** `Memory.Federation.mergeSafePred` on typed history objects;
  honest `Err` on mismatch — no CRDT fork.

  Imports `Memory.MergeSafe` (do not fork). Sole physics axiom remains
  `LandauerLaw.physicalSecondLaw` (imported transitively, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Memory.MergeSafe
import Urge.AdmitKleisli
import LandauerLaw

open Memory.Federation UMST.Urge.AdmitKleisli

namespace UMST.Urge.MergeSafe

/-- Federated history object: content-addressed snapshot + theorem registry string. -/
structure HistoryObject where
  snapshot   : HistorySnapshot
  theorem_id : String

/-- Embed history object into federated `MemoryEntry` (imported carrier — no fork). -/
def toMemoryEntry (h : HistoryObject) : MemoryEntry :=
  { memory_id := h.snapshot.commitId, theorem_id := h.theorem_id }

/-- History merge-safe predicate: imported `mergeSafePred` on embedded entries. -/
def historyMergeSafePred (h_A h_B : HistoryObject) : Prop :=
  mergeSafePred (toMemoryEntry h_A) (toMemoryEntry h_B)

/-- Refusal reasons for history merge (extensional mismatch only). -/
inductive MergeRefusal where
  | commitMismatch
  | theoremMismatch
  deriving DecidableEq, Repr

/-- Merge attempt: `ok` when merge-safe; `error` with honest reason otherwise. -/
def mergeHistoryAttempt (h_A h_B : HistoryObject) :
    Except MergeRefusal HistoryObject :=
  if h_A.snapshot.commitId = h_B.snapshot.commitId then
    if h_A.theorem_id = h_B.theorem_id then
      Except.ok h_A
    else
      Except.error MergeRefusal.theoremMismatch
  else
    Except.error MergeRefusal.commitMismatch

theorem mergeHistoryAttempt_ok (h_A h_B : HistoryObject)
    (hid : h_A.snapshot.commitId = h_B.snapshot.commitId)
    (hth : h_A.theorem_id = h_B.theorem_id) :
    mergeHistoryAttempt h_A h_B = Except.ok h_A := by
  simp [mergeHistoryAttempt, hid, hth]

theorem mergeHistoryAttempt_commit_err (h_A h_B : HistoryObject)
    (h : h_A.snapshot.commitId ≠ h_B.snapshot.commitId) :
    mergeHistoryAttempt h_A h_B = Except.error MergeRefusal.commitMismatch := by
  simp [mergeHistoryAttempt, h]

theorem mergeHistoryAttempt_theorem_err (h_A h_B : HistoryObject)
    (hid : h_A.snapshot.commitId = h_B.snapshot.commitId)
    (hth : h_A.theorem_id ≠ h_B.theorem_id) :
    mergeHistoryAttempt h_A h_B = Except.error MergeRefusal.theoremMismatch := by
  simp [mergeHistoryAttempt, hid, hth]

theorem historyMergeSafePred_iff (h_A h_B : HistoryObject) :
    historyMergeSafePred h_A h_B ↔
      (∃ h, mergeHistoryAttempt h_A h_B = Except.ok h) := by
  unfold historyMergeSafePred mergeSafePred toMemoryEntry
  constructor
  · intro ⟨hid, hth⟩
    refine ⟨h_A, ?_⟩
    have hc : h_A.snapshot.commitId = h_B.snapshot.commitId := by simpa using hid
    have ht : h_A.theorem_id = h_B.theorem_id := by simpa using hth
    simp [mergeHistoryAttempt, hc, ht]
  · intro ⟨_, hok⟩
    rw [mergeHistoryAttempt] at hok
    by_cases hc : h_A.snapshot.commitId = h_B.snapshot.commitId
    · by_cases ht : h_A.theorem_id = h_B.theorem_id
      · exact ⟨hc, ht⟩
      · simp [hc, ht] at hok
    · simp [hc] at hok

theorem historyMergeSafe
    (h_A h_B : HistoryObject) (t : String)
    (h_id : h_A.snapshot.commitId = h_B.snapshot.commitId)
    (h_thm : h_A.theorem_id = t ∧ h_B.theorem_id = t)
    (_h_reg : True) :
    historyMergeSafePred h_A h_B := by
  unfold historyMergeSafePred mergeSafePred toMemoryEntry
  exact MergeSafe (toMemoryEntry h_A) (toMemoryEntry h_B) t
    (by simpa using h_id) (by simpa [h_thm.1, h_thm.2]) _h_reg

theorem historyMergeSafe_from_attempt (h_A h_B : HistoryObject)
    (h : mergeHistoryAttempt h_A h_B = Except.ok h_A) :
    historyMergeSafePred h_A h_B :=
  (historyMergeSafePred_iff h_A h_B).2 ⟨h_A, h⟩

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def mergeSafeProductionWired : Bool := false

theorem mergeSafeProductionWiredFalse : mergeSafeProductionWired = false := rfl

theorem mergeSafeModuleWitness : True := trivial

theorem historyMergeSafePred_eq_imported (h_A h_B : HistoryObject) :
    historyMergeSafePred h_A h_B =
      mergeSafePred (toMemoryEntry h_A) (toMemoryEntry h_B) :=
  rfl

end UMST.Urge.MergeSafe
