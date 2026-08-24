(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/MergeSafe.v                                       *)
(*                                                                      *)
(*  Meso acting Urge — history merge-safety (L-M5 / GMD-8 mirror).       *)
(*  §4 / §12: federated rows merge-safe iff matching canonical content   *)
(*  id and theorem binding. Honest refuse on mismatch; no CRDT theater. *)
(*                                                                      *)
(*  Predicate mirrors Lean `Memory.MergeSafe` (import-only pin).         *)
(*  ZERO Admitted. ZERO new axioms.                                      *)
(* ================================================================== *)

From Coq Require Import Arith Bool.
Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: History memory carriers (parallel to Rust HistoryObject) *)
(* ------------------------------------------------------------------ *)

(** Minimal history memory row: SDF-canonical content id + theorem binding. *)
Record HistoryMemoryEntry : Set := {
  history_content_id : nat;
  history_theorem_id : nat
}.

(** Merge-safe predicate: same canonical content id and same theorem binding. *)
Definition mergeSafePred (e_A e_B : HistoryMemoryEntry) : Prop :=
  history_content_id e_A = history_content_id e_B /\
  history_theorem_id e_A = history_theorem_id e_B.

Lemma mergeSafePred_intro (e_A e_B : HistoryMemoryEntry)
    (hid : history_content_id e_A = history_content_id e_B)
    (hth : history_theorem_id e_A = history_theorem_id e_B) :
  mergeSafePred e_A e_B.
Proof.
  exact (conj hid hth).
Qed.

(** Main L-M5 theorem: shared content id + shared theorem binding ⇒ merge-safe.
    Registry membership (`_h_reg`) is orthogonal well-formedness — not used here. *)
Theorem MergeSafe
    (e_A e_B : HistoryMemoryEntry) (t : nat)
    (h_id : history_content_id e_A = history_content_id e_B)
    (h_thm : history_theorem_id e_A = t /\ history_theorem_id e_B = t)
    (_h_reg : True) :
  mergeSafePred e_A e_B.
Proof.
  apply mergeSafePred_intro.
  - exact h_id.
  - destruct h_thm as [HtA HtB]. rewrite HtA, HtB. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Honest refuse verdicts (no CRDT auto-merge)              *)
(* ------------------------------------------------------------------ *)

Inductive mergeSafeVerdict :=
  | merge_safe_admit
  | merge_safe_refuse_mismatch.

(** Computational merge-safe check — honest refuse on any mismatch. *)
Definition merge_safe (left right : HistoryMemoryEntry) : mergeSafeVerdict :=
  if Nat.eqb (history_content_id left) (history_content_id right) then
    if Nat.eqb (history_theorem_id left) (history_theorem_id right) then
      merge_safe_admit
    else
      merge_safe_refuse_mismatch
  else
    merge_safe_refuse_mismatch.

Lemma merge_safe_admit_iff (left right : HistoryMemoryEntry) :
  merge_safe left right = merge_safe_admit <->
  mergeSafePred left right.
Proof.
  unfold merge_safe, mergeSafePred.
  split.
  - intro H.
    destruct (Nat.eqb (history_content_id left) (history_content_id right)) eqn:Hc.
    + destruct (Nat.eqb (history_theorem_id left) (history_theorem_id right)) eqn:Ht.
      * inversion H; split; apply Nat.eqb_eq; assumption.
      * discriminate H.
    + discriminate H.
  - intros [Hid Hth].
    unfold merge_safe.
    rewrite <- Hid, <- Hth.
    rewrite Nat.eqb_refl, Nat.eqb_refl.
    reflexivity.
Qed.

Inductive crdt_auto_merge_refused := crdt_auto_merge_refused_tag.

(** Positive refuse: CRDT auto-merge is forbidden (not silent swallow). *)
Definition refuse_crdt_auto_merge : crdt_auto_merge_refused :=
  crdt_auto_merge_refused_tag.

Lemma refuse_crdt_auto_merge_is_tag :
  refuse_crdt_auto_merge = crdt_auto_merge_refused_tag.
Proof. reflexivity. Qed.

Lemma merge_safe_refuse_not_pred (left right : HistoryMemoryEntry) :
  merge_safe left right = merge_safe_refuse_mismatch ->
  ~ mergeSafePred left right.
Proof.
  intros Hrefuse.
  intros Hpred.
  apply merge_safe_admit_iff in Hpred.
  rewrite Hpred in Hrefuse. discriminate Hrefuse.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Lean Memory.MergeSafe pin + honesty flags                 *)
(* ------------------------------------------------------------------ *)

(** Conceptual pin — Lean `Memory.MergeSafe` (proof import-only). *)
Definition memory_merge_safe_lean_pin : nat := 0.

Lemma memory_merge_safe_lean_pin_marker :
  memory_merge_safe_lean_pin = 0.
Proof. reflexivity. Qed.

Definition urge_merge_safe_physics_green : bool := false.

Lemma urge_merge_safe_physics_green_false :
  urge_merge_safe_physics_green = false.
Proof. reflexivity. Qed.

Definition merge_safe_production_wired : bool := false.

Lemma merge_safe_production_wired_false :
  merge_safe_production_wired = false.
Proof. reflexivity. Qed.

Definition merge_safe_history_marker : nat := 1.

Lemma merge_safe_history_marker_pos :
  0 < merge_safe_history_marker.
Proof. apply Nat.lt_0_succ. Qed.

Theorem urge_merge_safe_module_witness : True.
Proof. exact I. Qed.
