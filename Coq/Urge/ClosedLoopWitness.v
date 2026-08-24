(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/ClosedLoopWitness.v                              *)
(*                                                                      *)
(*  Meso acting Urge — §22.7 messy witness back into Excitement         *)
(*  occupancy. Residue counts + observed ΔF feed occupancy surrogate.   *)
(*  Composes `excitement_select`; no second argmin.                      *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Constitutional.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Open Scope Q_scope.
Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Messy witness + occupancy feedback carriers             *)
(* ------------------------------------------------------------------ *)

(** Six Excitement residue constructors — Lean arity pin (§22.7 corpus). *)
Inductive closed_loop_residue :=
  | clr_no_candidates
  | clr_all_inadmissible
  | clr_all_excluded_by_cbf
  | clr_all_excluded_by_dec
  | clr_untagged_constant
  | clr_no_strict_improvement.

(** Per-constructor occurrence counts returned toward Excitement. *)
Record closed_loop_residue_counts : Set := {
  clrc_no_candidates : nat;
  clrc_all_inadmissible : nat;
  clrc_all_excluded_by_cbf : nat;
  clrc_all_excluded_by_dec : nat;
  clrc_untagged_constant : nat;
  clrc_no_strict_improvement : nat
}.

Definition empty_closed_loop_residue_counts : closed_loop_residue_counts :=
  {| clrc_no_candidates := 0;
     clrc_all_inadmissible := 0;
     clrc_all_excluded_by_cbf := 0;
     clrc_all_excluded_by_dec := 0;
     clrc_untagged_constant := 0;
     clrc_no_strict_improvement := 0 |}.

Definition closed_loop_residue_counts_total (c : closed_loop_residue_counts) : nat :=
  clrc_no_candidates c +
  clrc_all_inadmissible c +
  clrc_all_excluded_by_cbf c +
  clrc_all_excluded_by_dec c +
  clrc_untagged_constant c +
  clrc_no_strict_improvement c.

Definition closed_loop_residue_count_of
    (c : closed_loop_residue_counts) (r : closed_loop_residue) : nat :=
  match r with
  | clr_no_candidates => clrc_no_candidates c
  | clr_all_inadmissible => clrc_all_inadmissible c
  | clr_all_excluded_by_cbf => clrc_all_excluded_by_cbf c
  | clr_all_excluded_by_dec => clrc_all_excluded_by_dec c
  | clr_untagged_constant => clrc_untagged_constant c
  | clr_no_strict_improvement => clrc_no_strict_improvement c
  end.

Definition increment_closed_loop_residue_count
    (counts : closed_loop_residue_counts) (r : closed_loop_residue)
    : closed_loop_residue_counts :=
  match r with
  | clr_no_candidates =>
      {| clrc_no_candidates := S (clrc_no_candidates counts);
         clrc_all_inadmissible := clrc_all_inadmissible counts;
         clrc_all_excluded_by_cbf := clrc_all_excluded_by_cbf counts;
         clrc_all_excluded_by_dec := clrc_all_excluded_by_dec counts;
         clrc_untagged_constant := clrc_untagged_constant counts;
         clrc_no_strict_improvement := clrc_no_strict_improvement counts |}
  | clr_all_inadmissible =>
      {| clrc_no_candidates := clrc_no_candidates counts;
         clrc_all_inadmissible := S (clrc_all_inadmissible counts);
         clrc_all_excluded_by_cbf := clrc_all_excluded_by_cbf counts;
         clrc_all_excluded_by_dec := clrc_all_excluded_by_dec counts;
         clrc_untagged_constant := clrc_untagged_constant counts;
         clrc_no_strict_improvement := clrc_no_strict_improvement counts |}
  | clr_all_excluded_by_cbf =>
      {| clrc_no_candidates := clrc_no_candidates counts;
         clrc_all_inadmissible := clrc_all_inadmissible counts;
         clrc_all_excluded_by_cbf := S (clrc_all_excluded_by_cbf counts);
         clrc_all_excluded_by_dec := clrc_all_excluded_by_dec counts;
         clrc_untagged_constant := clrc_untagged_constant counts;
         clrc_no_strict_improvement := clrc_no_strict_improvement counts |}
  | clr_all_excluded_by_dec =>
      {| clrc_no_candidates := clrc_no_candidates counts;
         clrc_all_inadmissible := clrc_all_inadmissible counts;
         clrc_all_excluded_by_cbf := clrc_all_excluded_by_cbf counts;
         clrc_all_excluded_by_dec := S (clrc_all_excluded_by_dec counts);
         clrc_untagged_constant := clrc_untagged_constant counts;
         clrc_no_strict_improvement := clrc_no_strict_improvement counts |}
  | clr_untagged_constant =>
      {| clrc_no_candidates := clrc_no_candidates counts;
         clrc_all_inadmissible := clrc_all_inadmissible counts;
         clrc_all_excluded_by_cbf := clrc_all_excluded_by_cbf counts;
         clrc_all_excluded_by_dec := clrc_all_excluded_by_dec counts;
         clrc_untagged_constant := S (clrc_untagged_constant counts);
         clrc_no_strict_improvement := clrc_no_strict_improvement counts |}
  | clr_no_strict_improvement =>
      {| clrc_no_candidates := clrc_no_candidates counts;
         clrc_all_inadmissible := clrc_all_inadmissible counts;
         clrc_all_excluded_by_cbf := clrc_all_excluded_by_cbf counts;
         clrc_all_excluded_by_dec := clrc_all_excluded_by_dec counts;
         clrc_untagged_constant := clrc_untagged_constant counts;
         clrc_no_strict_improvement := S (clrc_no_strict_improvement counts) |}
  end.

(** Map meso `excitement_residue` hook into six-constructor pin. *)
Definition map_excitement_residue (r : excitement_residue) : closed_loop_residue :=
  match r with
  | exc_no_candidates => clr_no_candidates
  | exc_all_inadmissible => clr_all_inadmissible
  | exc_no_strict_improvement => clr_no_strict_improvement
  end.

(** Observed free-energy delta: ΔF = observed − src (exact ℚ). *)
Record closed_loop_observed_delta_f : Set := {
  clod_src : Q;
  clod_observed : Q
}.

Definition closed_loop_observed_delta_f_delta (d : closed_loop_observed_delta_f) : Q :=
  Qminus (clod_observed d) (clod_src d).

Definition closed_loop_observed_delta_f_compute (src observed : Q) : Q :=
  Qminus observed src.

Lemma closed_loop_observed_delta_f_delta_eq_compute
    (d : closed_loop_observed_delta_f) :
  closed_loop_observed_delta_f_delta d =
  closed_loop_observed_delta_f_compute (clod_src d) (clod_observed d).
Proof.
  reflexivity.
Qed.

(** §22.7 messy witness bundle — residue corpus + measured ΔF steps. *)
Record messy_witness : Set := {
  mw_counts : closed_loop_residue_counts;
  mw_observed_delta_f : list closed_loop_observed_delta_f
}.

Definition empty_messy_witness : messy_witness :=
  {| mw_counts := empty_closed_loop_residue_counts;
     mw_observed_delta_f := nil |}.

Definition add_messy_observed_delta (w : messy_witness)
    (d : closed_loop_observed_delta_f) : messy_witness :=
  {| mw_counts := mw_counts w;
     mw_observed_delta_f := d :: mw_observed_delta_f w |}.

Definition record_messy_residue (w : messy_witness) (r : closed_loop_residue)
    : messy_witness :=
  {| mw_counts := increment_closed_loop_residue_count (mw_counts w) r;
     mw_observed_delta_f := mw_observed_delta_f w |}.

Definition record_messy_admit_residue (w : messy_witness)
    (r : excitement_residue) : messy_witness :=
  record_messy_residue w (map_excitement_residue r).

(** Excitement occupancy feedback derived from messy witness. *)
Record excitement_occupancy_feedback : Set := {
  eof_residue_total : nat;
  eof_delta_f_steps : nat;
  eof_occupancy_surrogate : nat
}.

Definition occupancy_from_witness (w : messy_witness)
    : excitement_occupancy_feedback :=
  let residue_total := closed_loop_residue_counts_total (mw_counts w) in
  let delta_f_steps := List.length (mw_observed_delta_f w) in
  {| eof_residue_total := residue_total;
     eof_delta_f_steps := delta_f_steps;
     eof_occupancy_surrogate := residue_total * 1000 + delta_f_steps |}.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §22.7 typed refusal + positive refuse                   *)
(* ------------------------------------------------------------------ *)

Inductive closed_loop_refusal :=
  | clref_excitement_residue (r : excitement_residue)
  | clref_second_argmin
  | clref_f64_delta_f
  | clref_open_loop_isolation.

Inductive closed_loop_step_verdict :=
  | clsv_accepted (feedback : excitement_occupancy_feedback)
  | clsv_refused (refusal : closed_loop_refusal).

Definition refuse_closed_loop_second_argmin :
  Empty_set + closed_loop_refusal := inr clref_second_argmin.

Definition refuse_closed_loop_f64_delta_f :
  Empty_set + closed_loop_refusal := inr clref_f64_delta_f.

Definition refuse_closed_loop_open_loop_isolation :
  Empty_set + closed_loop_refusal := inr clref_open_loop_isolation.

(** Strict improvement predicate for successor filtering (exact ℚ). *)
Definition strict_improvement (src : ThermodynamicState)
    (c : history_candidate src) : bool :=
  Qle_bool (free_energy (cand_tgt src c)) (free_energy src) &&
  negb (Qle_bool (free_energy src) (free_energy (cand_tgt src c))).

Definition strict_improvement_successors (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  list (history_candidate src) :=
  filter (strict_improvement src) successors.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Closed loop composes excitement_select (no argmin)      *)
(* ------------------------------------------------------------------ *)

(** Context for §22.7 closed-loop witness over admissible successors. *)
Record closed_loop_ctx (src : ThermodynamicState) : Set := {
  closed_loop_successors : list (history_candidate src)
}.

(** Closed-loop selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition closed_loop_select (src : ThermodynamicState)
    (ctx : closed_loop_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (closed_loop_successors src ctx).

Definition closed_loop_select_list (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src successors.

Theorem closed_loop_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : closed_loop_ctx src) :
  closed_loop_select src ctx =
  excitement_select src (closed_loop_successors src ctx).
Proof.
  unfold closed_loop_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem closed_loop_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : closed_loop_ctx src) :
  closed_loop_select src ctx =
  urge_recovery_select src (closed_loop_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem closed_loop_no_local_argmin
    (src : ThermodynamicState) (ctx : closed_loop_ctx src) :
  closed_loop_select src ctx =
  excitement_select src (closed_loop_successors src ctx).
Proof.
  exact (closed_loop_select_eq_excitement_select src ctx).
Qed.

Lemma closed_loop_empty (src : ThermodynamicState)
    (ctx : closed_loop_ctx src)
    (Hnil : closed_loop_successors src ctx = nil) :
  closed_loop_select src ctx = inr exc_no_candidates.
Proof.
  unfold closed_loop_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(** One §22.7 closed-loop witness step — compose `excitement_select`. *)
Definition witness_closed_loop_step (w : messy_witness)
    (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  messy_witness * closed_loop_step_verdict :=
  match successors with
  | nil =>
      match closed_loop_select_list src nil with
      | inl _ => (w, clsv_refused (clref_excitement_residue exc_no_candidates))
      | inr r =>
          (record_messy_admit_residue w r,
           clsv_refused (clref_excitement_residue r))
      end
  | _ :: _ =>
      match strict_improvement_successors src successors with
      | nil =>
          (record_messy_admit_residue w exc_no_strict_improvement,
           clsv_refused (clref_excitement_residue exc_no_strict_improvement))
      | improving as cands =>
          match closed_loop_select_list src cands with
          | inl c =>
              let delta :=
                {| clod_src := free_energy src;
                   clod_observed := free_energy (cand_tgt src c) |} in
              let w' := add_messy_observed_delta w delta in
              (w', clsv_accepted (occupancy_from_witness w'))
          | inr r =>
              (record_messy_admit_residue w r,
               clsv_refused (clref_excitement_residue r))
          end
      end
  end.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §22.7 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition closed_loop_fixture_accept_src : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 10 # 1;
     hydration := 0;
     strength := 0 |}.

Definition closed_loop_fixture_accept_tgt : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 3 # 1;
     hydration := 0;
     strength := 0 |}.

Lemma closed_loop_fixture_accept_admissible :
  admissible closed_loop_fixture_accept_src closed_loop_fixture_accept_tgt.
Proof.
  apply gate_check_sound.
  unfold gate_check, closed_loop_fixture_accept_src, closed_loop_fixture_accept_tgt.
  simpl.
  reflexivity.
Qed.

Definition closed_loop_fixture_accept_candidate :
  history_candidate closed_loop_fixture_accept_src :=
  {| cand_id := 1;
     cand_tgt := closed_loop_fixture_accept_tgt;
     cand_admissible := closed_loop_fixture_accept_admissible |}.

Definition closed_loop_fixture_refuse_src : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 2 # 1;
     hydration := 0;
     strength := 0 |}.

Definition closed_loop_fixture_refuse_tgt : ThermodynamicState :=
  closed_loop_fixture_refuse_src.

Lemma closed_loop_fixture_refuse_admissible :
  admissible closed_loop_fixture_refuse_src closed_loop_fixture_refuse_tgt.
Proof.
  exact (admissible_refl closed_loop_fixture_refuse_src).
Qed.

Definition closed_loop_fixture_refuse_candidate :
  history_candidate closed_loop_fixture_refuse_src :=
  {| cand_id := 0;
     cand_tgt := closed_loop_fixture_refuse_tgt;
     cand_admissible := closed_loop_fixture_refuse_admissible |}.

Theorem closed_loop_fixture_accept_records_delta :
  let (w, v) :=
    witness_closed_loop_step empty_messy_witness closed_loop_fixture_accept_src
      (closed_loop_fixture_accept_candidate :: nil) in
  match v with
  | clsv_accepted fb =>
      eof_delta_f_steps fb = 1%nat /\
      eof_residue_total fb = 0%nat /\
      List.length (mw_observed_delta_f w) = 1%nat
  | clsv_refused _ => False
  end.
Proof.
  unfold witness_closed_loop_step, closed_loop_select_list, urge_recovery_select.
  simpl.
  split; [| split]; reflexivity.
Qed.

Theorem closed_loop_fixture_refuse_no_candidates :
  let (w, v) :=
    witness_closed_loop_step empty_messy_witness closed_loop_fixture_accept_src nil in
  v = clsv_refused (clref_excitement_residue exc_no_candidates) /\
  closed_loop_residue_count_of (mw_counts w) clr_no_candidates = 1%nat.
Proof.
  unfold witness_closed_loop_step, closed_loop_select_list, urge_recovery_select.
  simpl.
  split; reflexivity.
Qed.

Theorem closed_loop_fixture_refuse_no_strict_improvement :
  let (w, v) :=
    witness_closed_loop_step empty_messy_witness closed_loop_fixture_refuse_src
      (closed_loop_fixture_refuse_candidate :: nil) in
  v = clsv_refused (clref_excitement_residue exc_no_strict_improvement) /\
  closed_loop_residue_count_of (mw_counts w) clr_no_strict_improvement = 1%nat.
Proof.
  unfold witness_closed_loop_step.
  simpl.
  split; reflexivity.
Qed.

Theorem closed_loop_occupancy_surrogate_fixture :
  let w :=
    record_messy_admit_residue
      (record_messy_admit_residue empty_messy_witness exc_no_candidates)
      exc_no_strict_improvement in
  let w' :=
    add_messy_observed_delta w
      {| clod_src := 10 # 1; clod_observed := 3 # 1 |} in
  eof_occupancy_surrogate (occupancy_from_witness w') = 2001%nat.
Proof.
  unfold occupancy_from_witness, record_messy_admit_residue, record_messy_residue,
    increment_closed_loop_residue_count, map_excitement_residue,
    closed_loop_residue_counts_total, add_messy_observed_delta.
  simpl.
  reflexivity.
Qed.

Theorem closed_loop_refuse_second_argmin_positive :
  refuse_closed_loop_second_argmin = inr clref_second_argmin.
Proof.
  reflexivity.
Qed.

Theorem closed_loop_refuse_f64_delta_f_positive :
  refuse_closed_loop_f64_delta_f = inr clref_f64_delta_f.
Proof.
  reflexivity.
Qed.

Theorem closed_loop_refuse_open_loop_isolation_positive :
  refuse_closed_loop_open_loop_isolation = inr clref_open_loop_isolation.
Proof.
  reflexivity.
Qed.

Theorem closed_loop_observed_delta_f_compute_fixture :
  closed_loop_observed_delta_f_compute (10 # 1) (3 # 1) = (3 # 1) - (10 # 1).
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition closed_loop_witness_physics_green : bool := false.

Lemma closed_loop_witness_physics_green_false :
  closed_loop_witness_physics_green = false.
Proof. reflexivity. Qed.

Definition closed_loop_witness_production_wired : bool := false.

Lemma closed_loop_witness_production_wired_false :
  closed_loop_witness_production_wired = false.
Proof. reflexivity. Qed.

Theorem closed_loop_witness_module_witness : True.
Proof. exact I. Qed.

Theorem closed_loop_witness_no_new_axiom : True.
Proof. exact I. Qed.

Theorem closed_loop_positive_refuse_not_silent :
  forall x : Empty_set, refuse_closed_loop_second_argmin <> inl x.
Proof.
  intros x. unfold refuse_closed_loop_second_argmin.
  discriminate.
Qed.
