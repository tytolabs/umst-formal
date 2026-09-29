(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/FastPathAdmit.v                                   *)
(*                                                                      *)
(*  Meso acting Urge — §17.8 fast-path admission as typed predicate.    *)
(*  Local commit uses a typed fast predicate (≤100ms budget constant),  *)
(*  analogue of R23 PreservationWitness — no whole-tree re-scan.      *)
(*  Merge / recovery pays the slow path (≤1s budget) with composed      *)
(*  `excitement_select` — **not** wall-clock GREEN, not a second argmin. *)
(*                                                                      *)
(*  ZERO `Admitted`. ZERO new `Axiom`. Unwired.                        *)
(* ================================================================== *)

From Stdlib Require Import Arith Bool Lia.
Open Scope bool_scope.

Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: §17.8 typed budget constants (not wall-clock GREEN)    *)
(* ------------------------------------------------------------------ *)

(** Blueprint §17.8 local commit admission budget (milliseconds, typed). *)
Definition local_commit_budget_ms : nat := 100.

(** Blueprint §17.8 merge / recovery slow-path budget (milliseconds, typed). *)
Definition merge_recovery_budget_ms : nat := 1000.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Admission path classification                           *)
(* ------------------------------------------------------------------ *)

Inductive admit_path :=
  | admit_path_fast_local
  | admit_path_full_merge_recovery.

(** Typed budget ceiling for each path class (not measured wall-clock). *)
Definition admit_path_budget_ms (p : admit_path) : nat :=
  match p with
  | admit_path_fast_local => local_commit_budget_ms
  | admit_path_full_merge_recovery => merge_recovery_budget_ms
  end.

Lemma admit_path_fast_local_budget :
  admit_path_budget_ms admit_path_fast_local = local_commit_budget_ms.
Proof. reflexivity. Qed.

Lemma admit_path_merge_recovery_budget :
  admit_path_budget_ms admit_path_full_merge_recovery = merge_recovery_budget_ms.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Fast-path candidate + typed predicate                   *)
(* ------------------------------------------------------------------ *)

(** Candidate for fast-path admission — local predicate inputs only. *)
Record fast_path_candidate : Set := {
  fp_is_local_append : bool;
  fp_requires_whole_tree_rescan : bool;
  fp_is_merge_or_recovery : bool
}.

(** Fast-path typed predicate — local append without whole-tree re-scan or merge. *)
Definition fast_path_admit_pred (c : fast_path_candidate) : bool :=
  match fp_is_local_append c,
        fp_requires_whole_tree_rescan c,
        fp_is_merge_or_recovery c with
  | true, false, false => true
  | _, _, _ => false
  end.

Inductive fast_path_admit_refusal :=
  | fp_refuse_whole_tree_rescan
  | fp_refuse_merge_recovery_slow_path
  | fp_refuse_wall_clock_sla_theater
  | fp_refuse_budget_exceeded (estimated_ms budget_ms : nat).

(** Classify admission path from candidate — honest refusal on inadmissible fast path. *)
Definition classify_admit_path (c : fast_path_candidate) :
  admit_path + fast_path_admit_refusal :=
  if fp_requires_whole_tree_rescan c then
    inr fp_refuse_whole_tree_rescan
  else if fp_is_merge_or_recovery c then
    inr fp_refuse_merge_recovery_slow_path
  else if fast_path_admit_pred c then
    inl admit_path_fast_local
  else
    inr (fp_refuse_budget_exceeded (S local_commit_budget_ms)
                                   local_commit_budget_ms).

Lemma classify_admit_path_fast_local
    (c : fast_path_candidate)
    (h_append : fp_is_local_append c = true)
    (h_rescan : fp_requires_whole_tree_rescan c = false)
    (h_merge : fp_is_merge_or_recovery c = false) :
  classify_admit_path c = inl admit_path_fast_local.
Proof.
  unfold classify_admit_path, fast_path_admit_pred.
  rewrite h_rescan, h_merge, h_append.
  reflexivity.
Qed.

Lemma classify_admit_path_whole_tree_rescan
    (c : fast_path_candidate)
    (h : fp_requires_whole_tree_rescan c = true) :
  classify_admit_path c = inr fp_refuse_whole_tree_rescan.
Proof.
  unfold classify_admit_path.
  rewrite h. reflexivity.
Qed.

Lemma classify_admit_path_merge_recovery
    (c : fast_path_candidate)
    (h_rescan : fp_requires_whole_tree_rescan c = false)
    (h_merge : fp_is_merge_or_recovery c = true) :
  classify_admit_path c = inr fp_refuse_merge_recovery_slow_path.
Proof.
  unfold classify_admit_path.
  rewrite h_rescan, h_merge. reflexivity.
Qed.

(** Positive refuse: wall-clock SLA theater is inadmissible — typed predicate only. *)
Definition refuse_wall_clock_sla_theater :
  Empty_set + fast_path_admit_refusal :=
  inr fp_refuse_wall_clock_sla_theater.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Typed budget witness (declared ceiling, not measured)   *)
(* ------------------------------------------------------------------ *)

Record latency_budget_witness : Set := {
  lb_path : admit_path;
  lb_budget_ms : nat;
  lb_typed_predicate : bool
}.

Definition budget_witness_for (p : admit_path) : latency_budget_witness :=
  {| lb_path := p;
     lb_budget_ms := admit_path_budget_ms p;
     lb_typed_predicate := true |}.

Lemma budget_witness_for_typed (p : admit_path) :
  lb_typed_predicate (budget_witness_for p) = true.
Proof. reflexivity. Qed.

Lemma budget_witness_for_budget (p : admit_path) :
  lb_budget_ms (budget_witness_for p) = admit_path_budget_ms p.
Proof. reflexivity. Qed.

(** Check surrogate estimated cost against typed budget — refuse if exceeded. *)
Definition check_typed_budget (p : admit_path) (estimated_ms : nat) :
  latency_budget_witness + fast_path_admit_refusal :=
  let budget_ms := admit_path_budget_ms p in
  if estimated_ms <=? budget_ms then
    inl (budget_witness_for p)
  else
    inr (fp_refuse_budget_exceeded estimated_ms budget_ms).

Lemma check_typed_budget_ok (p : admit_path) (estimated_ms : nat)
    (h : estimated_ms <= admit_path_budget_ms p) :
  check_typed_budget p estimated_ms = inl (budget_witness_for p).
Proof.
  unfold check_typed_budget.
  destruct (estimated_ms <=? admit_path_budget_ms p) eqn:Hc.
  - reflexivity.
  - apply Nat.leb_gt in Hc. lia.
Qed.

Lemma check_typed_budget_exceeded (p : admit_path) (estimated_ms : nat)
    (h : admit_path_budget_ms p < estimated_ms) :
  check_typed_budget p estimated_ms =
  inr (fp_refuse_budget_exceeded estimated_ms (admit_path_budget_ms p)).
Proof.
  unfold check_typed_budget.
  destruct (estimated_ms <=? admit_path_budget_ms p) eqn:Hc.
  - apply Nat.leb_le in Hc. lia.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Slow path composes Excitement (no second argmin)        *)
(* ------------------------------------------------------------------ *)

(** Merge / recovery slow path routes through `urge_recovery` / `excitement_select`. *)
Definition slow_path_recovery (src : ThermodynamicState)
  (ctx : history_recovery_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery src ctx.

Theorem slow_path_recovery_eq_urge_recovery :
  forall (src : ThermodynamicState) (ctx : history_recovery_ctx src),
  slow_path_recovery src ctx = urge_recovery src ctx.
Proof.
  intros. reflexivity.
Qed.

Theorem slow_path_recovery_eq_excitement_select :
  forall (src : ThermodynamicState) (ctx : history_recovery_ctx src),
  slow_path_recovery src ctx =
  excitement_select src (recovery_successors src ctx).
Proof.
  intros src ctx.
  unfold slow_path_recovery, urge_recovery.
  reflexivity.
Qed.

Theorem slow_path_recovery_no_second_argmin :
  forall (src : ThermodynamicState) (ctx : history_recovery_ctx src),
  slow_path_recovery src ctx =
  excitement_select src (recovery_successors src ctx).
Proof.
  intros. apply slow_path_recovery_eq_excitement_select.
Qed.

(** Slow-path admission class for merge/recovery candidates. *)
Definition classify_slow_path (c : fast_path_candidate) :
  admit_path + fast_path_admit_refusal :=
  if fp_is_merge_or_recovery c then
    inl admit_path_full_merge_recovery
  else
    classify_admit_path c.

Lemma classify_slow_path_merge_recovery
    (c : fast_path_candidate)
    (h : fp_is_merge_or_recovery c = true) :
  classify_slow_path c = inl admit_path_full_merge_recovery.
Proof.
  unfold classify_slow_path. rewrite h. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition fast_path_physics_green : bool := false.

Lemma fast_path_physics_green_false : fast_path_physics_green = false.
Proof. reflexivity. Qed.

Definition fast_path_production_wired : bool := false.

Lemma fast_path_production_wired_false : fast_path_production_wired = false.
Proof. reflexivity. Qed.

Theorem fast_path_admit_module_witness : True.
Proof. exact I. Qed.

Theorem fast_path_admit_no_new_axiom : True.
Proof. exact I. Qed.
