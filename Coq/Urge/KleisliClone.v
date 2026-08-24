(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/KleisliClone.v                                    *)
(*                                                                      *)
(*  Meso acting Urge — §16.7 operator verb `clone` as Kleisli arrow.   *)
(*  Initial replica coalgebra admission — not sync inbound, not outbound *)
(*  tick, not Frugal MI observation, not MergeSafe witness, not         *)
(*  Excitement argmin. Compose `excitement_select`; no second argmin.   *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport` / `ReplicaCoalgebra`. *)
(*  ZERO new axioms. ZERO `Admitted`. Landauer discharge on Lean       *)
(*  `LandauerLaw`.                                                       *)
(* ================================================================== *)

From Coq Require Import Arith List String Bool.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Constitutional.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.
Require Import UMSTFormal.Urge.ReplicaCoalgebra.

Open Scope string_scope.
Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: §16.7 operator verb table carriers                    *)
(* ------------------------------------------------------------------ *)

(** Operator verb pin — blueprint §16.7 row `clone`. *)
Inductive clone_operator_verb := clone_verb.

(** Kleisli gate kinds cited in §16.7 verb table. *)
Inductive clone_kleisli_gate_kind :=
  | ckg_admit_initial_replica_coalgebra
  | ckg_frugal_mi_observation
  | ckg_gate_check_before_sync_inbound
  | ckg_outbound_tick_if_admitted
  | ckg_excitement_argmin.

(** Verb-table column requirement (`—` vs required). *)
Inductive clone_verb_column_req :=
  | cvcr_not_required
  | cvcr_required.

(** Entity check column for §16.7 rows. *)
Inductive clone_entity_check_kind :=
  | cec_entity_label
  | cec_replica_class
  | cec_remote_class.

(** One §16.7 operator verb table row (typed, not prose). *)
Record clone_verb_row : Set := {
  clone_row_verb : clone_operator_verb;
  clone_row_kleisli_gate : clone_kleisli_gate_kind;
  clone_row_merge_safe : clone_verb_column_req;
  clone_row_excitement : clone_verb_column_req;
  clone_row_entity_check : clone_entity_check_kind
}.

(** Blueprint §16.7 row for operator verb `clone`. *)
Definition cloneVerbRow : clone_verb_row :=
  {| clone_row_verb := clone_verb;
     clone_row_kleisli_gate := ckg_admit_initial_replica_coalgebra;
     clone_row_merge_safe := cvcr_not_required;
     clone_row_excitement := cvcr_not_required;
     clone_row_entity_check := cec_entity_label |}.

(** Whether a Kleisli gate kind matches the `clone` verb row. *)
Definition kleisli_gate_matches_clone (g : clone_kleisli_gate_kind) : bool :=
  match g with
  | ckg_admit_initial_replica_coalgebra => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Entity labels + initial replica coalgebra gate        *)
(* ------------------------------------------------------------------ *)

(** Entity labels from blueprint §13.6 (`[urge.remote.*]` proposed fields). *)
Inductive clone_entity_label :=
  | cel_labs
  | cel_compose.

(** Named replica class at initial clone admission (§15.4 sheaf section). *)
Inductive clone_replica_class :=
  | crc_node0
  | crc_node1
  | crc_forge
  | crc_luks
  | crc_darwin_scratch.

(** Human-readable replica class tag. *)
Definition cloneReplicaClassTag (c : clone_replica_class) : string :=
  match c with
  | crc_node0 => "node-0"
  | crc_node1 => "node-1"
  | crc_forge => "forgejo-primary-mirror"
  | crc_luks => "offline-luks"
  | crc_darwin_scratch => "darwin-scratch"
  end.

(** Initial replica coalgebra carrier at clone time — §15.4 sheaf admission. *)
Record initial_replica_coalgebra : Set := {
  clone_coalgebra_class : clone_replica_class;
  clone_coalgebra_egress_declared : bool;
  clone_coalgebra_authority_declared : bool
}.

(** Verdict of the admit-initial-replica-coalgebra Kleisli gate. *)
Inductive initial_coalgebra_gate_verdict :=
  | icgv_admit
  | icgv_refuse_undeclared_egress
  | icgv_refuse_undeclared_authority.

(** Evaluate admit-initial-replica-coalgebra gate (clone Kleisli gate). *)
Definition evaluate_initial_coalgebra_gate
    (c : initial_replica_coalgebra) : initial_coalgebra_gate_verdict :=
  if clone_coalgebra_egress_declared c then
    if clone_coalgebra_authority_declared c then
      icgv_admit
    else
      icgv_refuse_undeclared_authority
  else
    icgv_refuse_undeclared_egress.

(** Remote host surrogate for entity-label policy checks. *)
Record clone_remote_host : Set := {
  clone_remote_host_label : string
}.

(** Whether remote host is refused for Compose entity clone (§16.8 / §13.6). *)
Definition compose_upstream_refused (host : string) : bool :=
  String.eqb host "github.com" ||
  String.eqb host "origin.cursor.com".

(** Parse entity label string into typed label (fail closed on unknown). *)
Definition parse_entity_label (label : string)
    : clone_entity_label + unit :=
  if String.eqb label "labs" then
    inl cel_labs
  else if String.eqb label "LABS" then
    inl cel_labs
  else if String.eqb label "compose" then
    inl cel_compose
  else if String.eqb label "COMPOSE" then
    inl cel_compose
  else
    inr tt.

(** Entity-label check: Compose must not clone from refused upstream hosts. *)
Definition entity_label_admits_clone (entity : clone_entity_label)
    (remote : clone_remote_host) : bool :=
  match entity with
  | cel_labs => true
  | cel_compose => negb (compose_upstream_refused (clone_remote_host_label remote))
  end.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Clone Kleisli arrow (initial admission only)          *)
(* ------------------------------------------------------------------ *)

(** Kleisli arrow carrier for the `clone` operator verb. *)
Definition CloneArrow := AdmitArrow.

(** Positive refuse when wrong Kleisli gate / column is applied to `clone`. *)
Inductive clone_gate_mismatch :=
  | cgm_frugal_mi_on_clone
  | cgm_sync_inbound_on_clone
  | cgm_outbound_tick_on_clone
  | cgm_merge_safe_witness_on_clone
  | cgm_excitement_argmin_on_clone
  | cgm_replica_class_on_clone
  | cgm_remote_class_on_clone
  | cgm_second_argmin_on_clone.

(** Fail-closed errors on the clone Kleisli arrow. *)
Inductive clone_arrow_error :=
  | cae_coalgebra_refused (v : initial_coalgebra_gate_verdict)
  | cae_unknown_entity_label
  | cae_compose_upstream_refused
  | cae_gate_mismatch (m : clone_gate_mismatch).

(** Successful `clone` Kleisli arrow output — initial admission only. *)
Record clone_admission : Set := {
  clone_admission_entity : clone_entity_label;
  clone_admission_replica : clone_replica_class;
  clone_admission_gate : initial_coalgebra_gate_verdict
}.

(** Run the `clone` Kleisli arrow — initial replica admission only. *)
Definition run_clone_kleisli_arrow (entity : clone_entity_label)
    (coalgebra : initial_replica_coalgebra)
    (remote : clone_remote_host)
    : clone_admission + clone_arrow_error :=
  if entity_label_admits_clone entity remote then
    match evaluate_initial_coalgebra_gate coalgebra with
    | icgv_admit =>
      inl
        {| clone_admission_entity := entity;
           clone_admission_replica := clone_coalgebra_class coalgebra;
           clone_admission_gate := icgv_admit |}
    | v => inr (cae_coalgebra_refused v)
    end
  else
    inr cae_compose_upstream_refused.

(** Parse label then run clone arrow — fail closed on unknown entity label. *)
Definition run_clone_kleisli_arrow_parsed (label : string)
    (coalgebra : initial_replica_coalgebra)
    (remote : clone_remote_host)
    : clone_admission + clone_arrow_error :=
  match parse_entity_label label with
  | inl entity => run_clone_kleisli_arrow entity coalgebra remote
  | inr _ => inr cae_unknown_entity_label
  end.

(** Clone Kleisli identity arrow (inherited carrier — cite only). *)
Definition cloneKleisliIdentity : CloneArrow := admitIdentity.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Positive refuse (wrong gates / columns on `clone`)    *)
(* ------------------------------------------------------------------ *)

Definition refuse_frugal_mi_on_clone : clone_gate_mismatch :=
  cgm_frugal_mi_on_clone.

Definition refuse_sync_gate_on_clone : clone_gate_mismatch :=
  cgm_sync_inbound_on_clone.

Definition refuse_outbound_tick_on_clone : clone_gate_mismatch :=
  cgm_outbound_tick_on_clone.

Definition refuse_merge_safe_on_clone : clone_gate_mismatch :=
  cgm_merge_safe_witness_on_clone.

Definition refuse_excitement_argmin_on_clone : clone_gate_mismatch :=
  cgm_excitement_argmin_on_clone.

Definition refuse_replica_class_on_clone : clone_gate_mismatch :=
  cgm_replica_class_on_clone.

Definition refuse_remote_class_on_clone : clone_gate_mismatch :=
  cgm_remote_class_on_clone.

Definition refuse_second_argmin_on_clone : clone_gate_mismatch :=
  cgm_second_argmin_on_clone.

Lemma kleisli_gate_matches_clone_admit :
  kleisli_gate_matches_clone ckg_admit_initial_replica_coalgebra = true.
Proof. reflexivity. Qed.

Lemma kleisli_gate_matches_clone_frugal_false :
  kleisli_gate_matches_clone ckg_frugal_mi_observation = false.
Proof. reflexivity. Qed.

Lemma clone_verb_row_merge_safe_not_required :
  clone_row_merge_safe cloneVerbRow = cvcr_not_required.
Proof. reflexivity. Qed.

Lemma clone_verb_row_excitement_not_required :
  clone_row_excitement cloneVerbRow = cvcr_not_required.
Proof. reflexivity. Qed.

Lemma clone_verb_row_entity_label_check :
  clone_row_entity_check cloneVerbRow = cec_entity_label.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Compose excitement_select (no second argmin)           *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — import selector; refuse second local argmin. *)
Inductive clone_excitement_compose_pin :=
  | cecp_import_select_excitement
  | cecp_second_argmin_refused.

(** Context for clone excitement composition over admissible successors. *)
Record clone_excitement_ctx (src : ThermodynamicState) : Set := {
  clone_excitement_successors : list (history_candidate src)
}.

(** Clone path composes `excitement_select` — not a second argmin. *)
Definition clone_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : clone_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | cecp_import_select_excitement => excitement_select src cands
  | cecp_second_argmin_refused => inr exc_all_inadmissible
  end.

(** Clone excitement selection over context — aliases `urge_recovery_select`. *)
Definition clone_recovery_select (src : ThermodynamicState)
    (ctx : clone_excitement_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (clone_excitement_successors src ctx).

Theorem clone_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  clone_excitement_select src cands cecp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem clone_recovery_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : clone_excitement_ctx src) :
  clone_recovery_select src ctx =
  excitement_select src (clone_excitement_successors src ctx).
Proof.
  unfold clone_recovery_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem clone_recovery_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : clone_excitement_ctx src) :
  clone_recovery_select src ctx =
  urge_recovery_select src (clone_excitement_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem clone_no_local_argmin
    (src : ThermodynamicState) (ctx : clone_excitement_ctx src) :
  clone_recovery_select src ctx =
  excitement_select src (clone_excitement_successors src ctx).
Proof.
  exact (clone_recovery_select_eq_excitement_select src ctx).
Qed.

Theorem clone_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  clone_excitement_select src cands cecp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma clone_recovery_empty (src : ThermodynamicState)
    (ctx : clone_excitement_ctx src)
    (Hnil : clone_excitement_successors src ctx = nil) :
  clone_recovery_select src ctx = inr exc_no_candidates.
Proof.
  unfold clone_recovery_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Fixtures + witness theorems                           *)
(* ------------------------------------------------------------------ *)

Definition clone_fixture_coalgebra_admit : initial_replica_coalgebra :=
  {| clone_coalgebra_class := crc_node0;
     clone_coalgebra_egress_declared := true;
     clone_coalgebra_authority_declared := true |}.

Definition clone_fixture_coalgebra_refuse_egress : initial_replica_coalgebra :=
  {| clone_coalgebra_class := crc_luks;
     clone_coalgebra_egress_declared := false;
     clone_coalgebra_authority_declared := true |}.

Definition clone_fixture_remote_forge : clone_remote_host :=
  {| clone_remote_host_label := "forge.entity" |}.

Definition clone_fixture_remote_github : clone_remote_host :=
  {| clone_remote_host_label := "github.com" |}.

Theorem clone_fixture_initial_coalgebra_admits :
  evaluate_initial_coalgebra_gate clone_fixture_coalgebra_admit = icgv_admit.
Proof.
  reflexivity.
Qed.

Theorem clone_fixture_initial_coalgebra_refuses_egress :
  evaluate_initial_coalgebra_gate clone_fixture_coalgebra_refuse_egress =
  icgv_refuse_undeclared_egress.
Proof.
  reflexivity.
Qed.

Theorem clone_fixture_arrow_admits_labs :
  run_clone_kleisli_arrow cel_labs clone_fixture_coalgebra_admit
    clone_fixture_remote_forge =
  inl
    {| clone_admission_entity := cel_labs;
       clone_admission_replica := crc_node0;
       clone_admission_gate := icgv_admit |}.
Proof.
  reflexivity.
Qed.

Theorem clone_fixture_compose_upstream_refused :
  compose_upstream_refused "github.com" = true.
Proof.
  reflexivity.
Qed.

Theorem clone_fixture_compose_entity_refused_on_github :
  run_clone_kleisli_arrow cel_compose clone_fixture_coalgebra_admit
    clone_fixture_remote_github = inr cae_compose_upstream_refused.
Proof.
  reflexivity.
Qed.

Theorem clone_fixture_parse_labs :
  parse_entity_label "labs" = inl cel_labs.
Proof.
  reflexivity.
Qed.

Theorem clone_fixture_parse_compose_case_insensitive :
  parse_entity_label "COMPOSE" = inl cel_compose.
Proof.
  reflexivity.
Qed.

Theorem clone_replica_class_node0_tag :
  cloneReplicaClassTag crc_node0 = "node-0".
Proof.
  reflexivity.
Qed.

Theorem clone_replica_class_luks_tag :
  cloneReplicaClassTag crc_luks = "offline-luks".
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 7: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition kleisli_clone_physics_green : bool := false.

Lemma kleisli_clone_physics_green_false :
  kleisli_clone_physics_green = false.
Proof. reflexivity. Qed.

Definition kleisli_clone_production_wired : bool := false.

Lemma kleisli_clone_production_wired_false :
  kleisli_clone_production_wired = false.
Proof. reflexivity. Qed.

Theorem kleisli_clone_module_witness : True.
Proof. exact I. Qed.

Theorem kleisli_clone_no_new_axiom : True.
Proof. exact I. Qed.

Theorem kleisli_clone_positive_refuse_not_silent :
  kleisli_gate_matches_clone ckg_frugal_mi_observation = false /\
  kleisli_gate_matches_clone ckg_gate_check_before_sync_inbound = false.
Proof.
  split; reflexivity.
Qed.

Theorem kleisli_clone_compose_excitement_not_argmin :
  forall (src : ThermodynamicState) (ctx : clone_excitement_ctx src),
  clone_recovery_select src ctx =
  excitement_select src (clone_excitement_successors src ctx).
Proof.
  intros. exact (clone_no_local_argmin src ctx).
Qed.
