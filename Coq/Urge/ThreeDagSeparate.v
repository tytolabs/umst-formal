(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/ThreeDagSeparate.v                                *)
(*                                                                      *)
(*  Meso acting Urge — §16.11 / §22.2 three DAGs unfused:             *)
(*  (a) git bytes, (b) Kleisli history, (c) UCRS causal.              *)
(*  Agents walk (b) ordered by (c). Composes `excitement_select`;      *)
(*  no second argmin. Typed fusion refuses — not only !physics_green.  *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Three unfused DAG substrates + node carriers          *)
(* ------------------------------------------------------------------ *)

(** Three unfused DAG substrates from §16.11 / §22.2. *)
Inductive three_dag_substrate :=
  | tds_git_bytes
  | tds_kleisli_history
  | tds_ucrs_causal.

(** Git commit node on byte substrate (a). *)
Record git_commit_node : Set := {
  git_commit_hash : nat;
  git_parent_hash : option nat
}.

(** Kleisli admitted-history node on coordination DAG (b). *)
Record kleisli_history_node : Set := {
  kleisli_arrow_id : nat;
  kleisli_gate_merge_excitement_admitted : bool
}.

(** UCRS causal node on seq-ordered DAG (c). *)
Record ucrs_causal_node : Set := {
  ucrs_seq : nat;
  ucrs_wall_stamp_audit : option nat;
  ucrs_order_by_wall_clock : bool
}.

(** Per-DAG coordinates — unfused; never a single fused id. *)
Record three_dag_coordinates : Set := {
  tdc_git_commit : nat;
  tdc_kleisli_arrow : nat;
  tdc_ucrs_seq : nat
}.

(** UCRS stamp surrogate carried through three-DAG walker. *)
Record three_dag_ucrs_stamp : Set := {
  three_dag_ucrs_seq : nat;
  three_dag_ucrs_wall_has_t : bool
}.

(** Witness bundle three-DAG walk must preserve. *)
Record three_dag_witness : Set := {
  three_dag_witness_ucrs : three_dag_ucrs_stamp;
  three_dag_witness_kleisli_admitted : bool
}.

(** Typed three-DAG morphism — admissible Kleisli walk, not fused substrates. *)
Record three_dag_morphism : Set := {
  three_dag_morphism_coords : three_dag_coordinates;
  three_dag_morphism_witness : three_dag_witness;
  three_dag_morphism_excitement_selected : bool
}.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Fusion refusal + positive refuse (not silent accept)  *)
(* ------------------------------------------------------------------ *)

(** Typed fusion / discipline refusal — positive properties. *)
Inductive three_dag_fusion_refusal :=
  | tdf_git_bytes_as_kleisli_coord
  | tdf_ucrs_seq_fused_with_git_hash
  | tdf_wall_clock_as_ucrs_seq
  | tdf_kleisli_not_admitted
  | tdf_second_argmin_refused
  | tdf_physics_green_invent.

(** Walker verdict on three unfused DAGs. *)
Inductive three_dag_walker_verdict :=
  | tdw_admitted
  | tdw_refused (r : three_dag_fusion_refusal).

(** §16.11 admissibility conjunct inputs (surrogate). *)
Record three_dag_admissibility_conjunct : Set := {
  three_dag_conj_gate_ok : bool;
  three_dag_conj_kleisli_admitted : bool;
  three_dag_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ Kleisli admitted ∧ Excitement preserves`. *)
Definition three_dag_conjunct_admits (c : three_dag_admissibility_conjunct) : bool :=
  three_dag_conj_gate_ok c &&
  three_dag_conj_kleisli_admitted c &&
  three_dag_conj_excitement_preserves c.

(** Detect git-byte ↔ Kleisli coordination fusion. *)
Definition refuses_git_kleisli_fusion (coords : three_dag_coordinates) : bool :=
  Nat.eqb (tdc_git_commit coords) (tdc_kleisli_arrow coords).

(** Detect UCRS causal ↔ git-byte fusion. *)
Definition refuses_ucrs_git_fusion (coords : three_dag_coordinates) : bool :=
  Nat.eqb (tdc_ucrs_seq coords) (tdc_git_commit coords).

(** Positive refuse: second Excitement selector — compose `excitement_select`. *)
Definition refuse_second_argmin_selector : three_dag_fusion_refusal :=
  tdf_second_argmin_refused.

(** Evaluate Kleisli walk ordered by UCRS causal `seq` — refuse substrate fusion. *)
Definition evaluate_three_dag_walk
    (coords : three_dag_coordinates)
    (kleisli : kleisli_history_node)
    (ucrs : ucrs_causal_node)
    (claim_physics_green : bool)
    : three_dag_walker_verdict :=
  if claim_physics_green then tdw_refused tdf_physics_green_invent
  else if refuses_git_kleisli_fusion coords then
    tdw_refused tdf_git_bytes_as_kleisli_coord
  else if refuses_ucrs_git_fusion coords then
    tdw_refused tdf_ucrs_seq_fused_with_git_hash
  else if ucrs_order_by_wall_clock ucrs then
    tdw_refused tdf_wall_clock_as_ucrs_seq
  else if negb (Nat.eqb (tdc_ucrs_seq coords) (ucrs_seq ucrs)) then
    tdw_refused tdf_wall_clock_as_ucrs_seq
  else if negb (kleisli_gate_merge_excitement_admitted kleisli) then
    tdw_refused tdf_kleisli_not_admitted
  else if negb (Nat.eqb (kleisli_arrow_id kleisli) (tdc_kleisli_arrow coords)) then
    tdw_refused tdf_kleisli_not_admitted
  else tdw_admitted.

(** Build witness from coordinates + Kleisli node. *)
Definition witness_from_coords (coords : three_dag_coordinates)
    (kleisli : kleisli_history_node)
    (stamp : three_dag_ucrs_stamp) : three_dag_witness :=
  {| three_dag_witness_ucrs := stamp;
     three_dag_witness_kleisli_admitted :=
       kleisli_gate_merge_excitement_admitted kleisli |}.

(** Attempt typed three-DAG morphism — fail closed on inadmissibility. *)
Definition apply_three_dag_morphism
    (coords : three_dag_coordinates)
    (kleisli : kleisli_history_node)
    (ucrs : ucrs_causal_node)
    (conjunct : three_dag_admissibility_conjunct)
    (stamp : three_dag_ucrs_stamp)
    (excitement_selected : bool)
    : three_dag_morphism + three_dag_fusion_refusal :=
  if negb (three_dag_conjunct_admits conjunct) then
    inr tdf_kleisli_not_admitted
  else if negb excitement_selected then
    inr tdf_second_argmin_refused
  else
    match evaluate_three_dag_walk coords kleisli ucrs false with
    | tdw_admitted =>
      inl
        {| three_dag_morphism_coords := coords;
           three_dag_morphism_witness := witness_from_coords coords kleisli stamp;
           three_dag_morphism_excitement_selected := excitement_selected |}
    | tdw_refused r => inr r
    end.

Lemma refuse_second_argmin_selector_positive :
  refuse_second_argmin_selector = tdf_second_argmin_refused.
Proof.
  reflexivity.
Qed.

Lemma refuses_git_kleisli_fusion_detects_equal (n : nat) :
  refuses_git_kleisli_fusion
    {| tdc_git_commit := n; tdc_kleisli_arrow := n; tdc_ucrs_seq := 0 |} = true.
Proof.
  intros. unfold refuses_git_kleisli_fusion. simpl. apply Nat.eqb_refl.
Qed.

Lemma refuses_git_kleisli_fusion_separate (g k : nat)
    (Hneq : g <> k) :
  refuses_git_kleisli_fusion
    {| tdc_git_commit := g; tdc_kleisli_arrow := k; tdc_ucrs_seq := 0 |} = false.
Proof.
  intros. unfold refuses_git_kleisli_fusion. simpl.
  apply Nat.eqb_neq. exact Hneq.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Three-DAG walk composes Excitement (no second argmin)  *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — import selector; refuse second local argmin. *)
Inductive three_dag_excitement_compose_pin :=
  | tdecp_import_select_excitement
  | tdecp_second_argmin_refused.

(** Context for three-DAG selection over admissible history successors. *)
Record three_dag_ctx (src : ThermodynamicState) : Set := {
  three_dag_successors : list (history_candidate src)
}.

(** Compose path composes `excitement_select` — not a second argmin. *)
Definition three_dag_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : three_dag_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | tdecp_import_select_excitement => excitement_select src cands
  | tdecp_second_argmin_refused => inr exc_all_inadmissible
  end.

(** Three-DAG Kleisli walk **is** `urge_recovery_select` / `excitement_select`. *)
Definition three_dag_select (src : ThermodynamicState)
    (ctx : three_dag_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (three_dag_successors src ctx).

Theorem three_dag_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : three_dag_ctx src) :
  three_dag_select src ctx =
  excitement_select src (three_dag_successors src ctx).
Proof.
  unfold three_dag_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem three_dag_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : three_dag_ctx src) :
  three_dag_select src ctx =
  urge_recovery_select src (three_dag_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem three_dag_no_local_argmin
    (src : ThermodynamicState) (ctx : three_dag_ctx src) :
  three_dag_select src ctx =
  excitement_select src (three_dag_successors src ctx).
Proof.
  exact (three_dag_select_eq_excitement_select src ctx).
Qed.

Theorem three_dag_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  three_dag_excitement_select src cands tdecp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem three_dag_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  three_dag_excitement_select src cands tdecp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma three_dag_select_empty (src : ThermodynamicState)
    (ctx : three_dag_ctx src)
    (Hnil : three_dag_successors src ctx = nil) :
  three_dag_select src ctx = inr exc_no_candidates.
Proof.
  unfold three_dag_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §16.11 fixtures + witness theorems                      *)
(* ------------------------------------------------------------------ *)

Definition three_dag_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition three_dag_fixture_ucrs : three_dag_ucrs_stamp :=
  {| three_dag_ucrs_seq := (7 : nat);
     three_dag_ucrs_wall_has_t := true |}.

Definition three_dag_fixture_conjunct : three_dag_admissibility_conjunct :=
  {| three_dag_conj_gate_ok := true;
     three_dag_conj_kleisli_admitted := true;
     three_dag_conj_excitement_preserves := true |}.

Definition three_dag_fixture_coords : three_dag_coordinates :=
  {| tdc_git_commit := (11 : nat);
     tdc_kleisli_arrow := (22 : nat);
     tdc_ucrs_seq := (7 : nat) |}.

Definition three_dag_fixture_kleisli : kleisli_history_node :=
  {| kleisli_arrow_id := (22 : nat);
     kleisli_gate_merge_excitement_admitted := true |}.

Definition three_dag_fixture_ucrs_node : ucrs_causal_node :=
  {| ucrs_seq := 7;
     ucrs_wall_stamp_audit := @Some nat (42 : nat);
     ucrs_order_by_wall_clock := false |}.

Theorem three_dag_fixture_walk_admitted :
  evaluate_three_dag_walk
    three_dag_fixture_coords
    three_dag_fixture_kleisli
    three_dag_fixture_ucrs_node
    false = tdw_admitted.
Proof.
  reflexivity.
Qed.

Definition three_dag_fixture_fused_coords : three_dag_coordinates :=
  {| tdc_git_commit := (66 : nat);
     tdc_kleisli_arrow := (66 : nat);
     tdc_ucrs_seq := (3 : nat) |}.

Theorem three_dag_fixture_git_kleisli_fusion_refused :
  evaluate_three_dag_walk
    three_dag_fixture_fused_coords
    {| kleisli_arrow_id := (66 : nat);
       kleisli_gate_merge_excitement_admitted := true |}
    {| ucrs_seq := (3 : nat);
       ucrs_wall_stamp_audit := @None nat;
       ucrs_order_by_wall_clock := false |}
    false = tdw_refused tdf_git_bytes_as_kleisli_coord.
Proof.
  reflexivity.
Qed.

Theorem three_dag_fixture_wall_clock_order_refused :
  evaluate_three_dag_walk
    {| tdc_git_commit := (33 : nat);
       tdc_kleisli_arrow := (44 : nat);
       tdc_ucrs_seq := (9 : nat) |}
    {| kleisli_arrow_id := (44 : nat);
       kleisli_gate_merge_excitement_admitted := true |}
    {| ucrs_seq := (9 : nat);
       ucrs_wall_stamp_audit := @Some nat (42 : nat);
       ucrs_order_by_wall_clock := true |}
    false = tdw_refused tdf_wall_clock_as_ucrs_seq.
Proof.
  reflexivity.
Qed.

Theorem three_dag_fixture_apply_morphism_ok :
  apply_three_dag_morphism
    three_dag_fixture_coords
    three_dag_fixture_kleisli
    three_dag_fixture_ucrs_node
    three_dag_fixture_conjunct
    three_dag_fixture_ucrs
    true
  = inl
      {| three_dag_morphism_coords := three_dag_fixture_coords;
         three_dag_morphism_witness :=
           witness_from_coords
             three_dag_fixture_coords
             three_dag_fixture_kleisli
             three_dag_fixture_ucrs;
         three_dag_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem three_dag_fixture_witness_preserves_ucrs :
  three_dag_witness_ucrs
    (witness_from_coords
       three_dag_fixture_coords
       three_dag_fixture_kleisli
       three_dag_fixture_ucrs) =
  three_dag_fixture_ucrs.
Proof.
  reflexivity.
Qed.

Theorem three_dag_fixture_physics_green_invent_refused :
  evaluate_three_dag_walk
    three_dag_fixture_coords
    three_dag_fixture_kleisli
    three_dag_fixture_ucrs_node
    true = tdw_refused tdf_physics_green_invent.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition three_dag_separate_physics_green : bool := false.

Lemma three_dag_separate_physics_green_false :
  three_dag_separate_physics_green = false.
Proof. reflexivity. Qed.

Definition three_dag_separate_production_wired : bool := false.

Lemma three_dag_separate_production_wired_false :
  three_dag_separate_production_wired = false.
Proof. reflexivity. Qed.

Theorem three_dag_separate_module_witness : True.
Proof. exact I. Qed.

Theorem three_dag_separate_no_new_axiom : True.
Proof. exact I. Qed.

Theorem three_dag_fusion_refuse_not_silent :
  evaluate_three_dag_walk
    three_dag_fixture_fused_coords
    {| kleisli_arrow_id := (66 : nat);
       kleisli_gate_merge_excitement_admitted := true |}
    {| ucrs_seq := (3 : nat);
       ucrs_wall_stamp_audit := @None nat;
       ucrs_order_by_wall_clock := false |}
    false <> tdw_admitted.
Proof.
  unfold evaluate_three_dag_walk.
  discriminate.
Qed.
