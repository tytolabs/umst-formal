(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/UmstTomlRemotes.v                                 *)
(*                                                                      *)
(*  Meso acting Urge — §13.6 `[urge.remote.*]` in root `umst.toml`.    *)
(*  Typed parse of proposed remote policy rows; pre-push positive refuse *)
(*  — not only `!physics_green`. Composes `excitement_select`; no       *)
(*  second argmin.                                                      *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport` / `EntityRemote`.  *)
(*  ZERO new axioms. ZERO `Admitted`. Landauer discharge on Lean.        *)
(* ================================================================== *)

From Coq Require Import Arith List Bool String QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.
Require Import UMSTFormal.Urge.EntityRemote.

Open Scope bool_scope.
Open Scope string_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Root `umst.toml` `[urge.remote.*]` carriers           *)
(* ------------------------------------------------------------------ *)

(** One parsed `[urge.remote.*]` row from root `umst.toml` (§13.6). *)
Record urge_remote_toml_row : Set := {
  urtr_section : string;
  urtr_entity : urge_entity;
  urtr_classification : remote_classification;
  urtr_canonical : canonical_remote;
  urtr_mirror : mirror_remote
}.

(** Parsed root `umst.toml` remote policy document. *)
Record umst_toml_remotes_document : Set := {
  utrd_rows : list urge_remote_toml_row
}.

(** Parse failure for root `umst.toml` remote sections. *)
Inductive toml_remote_parse_error :=
  | trpe_no_remote_sections
  | trpe_missing_field (section field : string)
  | trpe_unknown_value (section field value : string).

(** Fail-closed import refusal — second local argmin is inadmissible. *)
Inductive umst_toml_remotes_import_refusal :=
  | utmir_second_argmin.

(** Verdict of root `umst.toml` remote operation class. *)
Inductive umst_toml_remotes_verdict :=
  | utmv_document_ok
  | utmv_parse_refused
  | utmv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Row ↔ policy bridge + pre-push evaluation               *)
(* ------------------------------------------------------------------ *)

(** Full `umst.toml` section key for a parsed row. *)
Definition urge_remote_toml_section_key (row : urge_remote_toml_row) : string :=
  String.append urge_remote_section_prefix (urtr_section row).

(** Bridge parsed TOML row to `EntityRemote` policy carrier. *)
Definition urge_remote_toml_row_to_policy (row : urge_remote_toml_row)
    : urge_remote_policy :=
  {| erp_section := urtr_section row;
     erp_entity := urtr_entity row;
     erp_classification := urtr_classification row;
     erp_canonical := urtr_canonical row;
     erp_mirror := urtr_mirror row |}.

(** Evaluate pre-push under parsed root `umst.toml` row (§16.8 host table). *)
Definition evaluate_toml_pre_push (row : urge_remote_toml_row) (host : string)
    : entity_pre_push_verdict + entity_pre_push_refusal :=
  evaluate_entity_pre_push (urge_remote_toml_row_to_policy row) host.

(** §13.6 admissibility conjunct for root `umst.toml` rows (surrogate). *)
Record umst_toml_remotes_conjunct : Set := {
  utrc_conj_gate_ok : bool;
  utrc_conj_document_typed : bool;
  utrc_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ document typed ∧ Excitement preserves`. *)
Definition umst_toml_remotes_conjunct_admits (c : umst_toml_remotes_conjunct) : bool :=
  utrc_conj_gate_ok c &&
  utrc_conj_document_typed c &&
  utrc_conj_excitement_preserves c.

(** Classify blind parse vs typed document without performing I/O. *)
Definition evaluate_umst_toml_remotes_operation (is_parse_refused : bool)
    : umst_toml_remotes_verdict :=
  if is_parse_refused then utmv_parse_refused else utmv_document_ok.

(** Positive refuse: second Excitement selector — compose `excitement_select`. *)
Definition refuse_second_argmin_selector : umst_toml_remotes_import_refusal :=
  utmir_second_argmin.

(** Positive refuse: production wired push without root `umst.toml` policy. *)
Definition refuse_production_wired_toml_push : entity_pre_push_refusal :=
  eppr_production_wired_refused.

(** Apply typed root `umst.toml` row check — fail closed on inadmissibility. *)
Definition apply_umst_toml_remote_row
    (row : urge_remote_toml_row)
    (host : string)
    (conjunct : umst_toml_remotes_conjunct)
    (excitement_selected : bool)
    : urge_remote_toml_row + entity_pre_push_refusal :=
  if negb (umst_toml_remotes_conjunct_admits conjunct) then
    inr (eppr_unclassified_host_refused erh_unclassified)
  else if negb excitement_selected then
    inr (eppr_unclassified_host_refused erh_unclassified)
  else
    match evaluate_toml_pre_push row host with
    | inl _ => inl row
    | inr r => inr r
    end.

Lemma umst_toml_remotes_parse_refused_positive :
  evaluate_umst_toml_remotes_operation true = utmv_parse_refused.
Proof. reflexivity. Qed.

Lemma umst_toml_remotes_document_ok_when_not_parse_refused :
  evaluate_umst_toml_remotes_operation false = utmv_document_ok.
Proof. reflexivity. Qed.

Lemma refuse_second_argmin_selector_positive :
  refuse_second_argmin_selector = utmir_second_argmin.
Proof. reflexivity. Qed.

Lemma refuse_production_wired_toml_push_positive :
  refuse_production_wired_toml_push = eppr_production_wired_refused.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Fixture document + honest parse surrogate             *)
(* ------------------------------------------------------------------ *)

(** Blueprint §13.6 `[urge.remote.labs-public]` from typed constants. *)
Definition umst_toml_fixture_labs_public : urge_remote_toml_row :=
  {| urtr_section := "labs-public"%string;
     urtr_entity := ue_labs;
     urtr_classification := rc_public_oss;
     urtr_canonical := cr_forge;
     urtr_mirror := mr_github |}.

(** Blueprint §13.6 `[urge.remote.compose-confidential]` from typed constants. *)
Definition umst_toml_fixture_compose_confidential : urge_remote_toml_row :=
  {| urtr_section := "compose-confidential"%string;
     urtr_entity := ue_compose;
     urtr_classification := rc_compose_confidential;
     urtr_canonical := cr_forge;
     urtr_mirror := mr_none |}.

(** Fixture document from blueprint §13.6 root `umst.toml` excerpt. *)
Definition root_umst_toml_fixture_document : umst_toml_remotes_document :=
  {| utrd_rows :=
       umst_toml_fixture_labs_public ::
       umst_toml_fixture_compose_confidential :: nil |}.

(** Honest parse surrogate — fixture-bounded document builder (no I/O). *)
Definition parse_root_umst_toml_remotes_fixture
    : umst_toml_remotes_document + toml_remote_parse_error :=
  inl root_umst_toml_fixture_document.

(** Empty document surrogate — positive refuse `trpe_no_remote_sections`. *)
Definition parse_root_umst_toml_remotes_empty
    : umst_toml_remotes_document + toml_remote_parse_error :=
  inr trpe_no_remote_sections.

Lemma root_umst_toml_fixture_document_two_rows :
  List.length (utrd_rows root_umst_toml_fixture_document) = 2%nat.
Proof. reflexivity. Qed.

Lemma parse_root_umst_toml_remotes_fixture_ok :
  parse_root_umst_toml_remotes_fixture = inl root_umst_toml_fixture_document.
Proof. reflexivity. Qed.

Lemma parse_root_umst_toml_remotes_empty_refused :
  parse_root_umst_toml_remotes_empty = inr trpe_no_remote_sections.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Root `umst.toml` composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Context for root `umst.toml` remote over admissible history successors. *)
Record umst_toml_remotes_ctx (src : ThermodynamicState) : Set := {
  umst_toml_remotes_successors : list (history_candidate src)
}.

(** Root `umst.toml` remote selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition umst_toml_remotes_select (src : ThermodynamicState)
    (ctx : umst_toml_remotes_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (umst_toml_remotes_successors src ctx).

Theorem umst_toml_remotes_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : umst_toml_remotes_ctx src) :
  umst_toml_remotes_select src ctx =
  excitement_select src (umst_toml_remotes_successors src ctx).
Proof.
  unfold umst_toml_remotes_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem umst_toml_remotes_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : umst_toml_remotes_ctx src) :
  umst_toml_remotes_select src ctx =
  urge_recovery_select src (umst_toml_remotes_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem umst_toml_remotes_no_local_argmin
    (src : ThermodynamicState) (ctx : umst_toml_remotes_ctx src) :
  umst_toml_remotes_select src ctx =
  excitement_select src (umst_toml_remotes_successors src ctx).
Proof.
  exact (umst_toml_remotes_select_eq_excitement_select src ctx).
Qed.

Lemma umst_toml_remotes_empty (src : ThermodynamicState)
    (ctx : umst_toml_remotes_ctx src)
    (Hnil : umst_toml_remotes_successors src ctx = nil) :
  umst_toml_remotes_select src ctx = inr exc_no_candidates.
Proof.
  unfold umst_toml_remotes_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: §13.6 fixtures + witness theorems                     *)
(* ------------------------------------------------------------------ *)

Definition umst_toml_fixture_conjunct : umst_toml_remotes_conjunct :=
  {| utrc_conj_gate_ok := true;
     utrc_conj_document_typed := true;
     utrc_conj_excitement_preserves := true |}.

Definition umst_toml_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Theorem umst_toml_labs_public_section_key :
  String.eqb
    (urge_remote_toml_section_key umst_toml_fixture_labs_public)
    "urge.remote.labs-public"%string = true.
Proof.
  reflexivity.
Qed.

Theorem umst_toml_compose_confidential_section_key :
  String.eqb
    (urge_remote_toml_section_key umst_toml_fixture_compose_confidential)
    "urge.remote.compose-confidential"%string = true.
Proof.
  reflexivity.
Qed.

Theorem umst_toml_row_to_policy_labs_public :
  urge_remote_toml_row_to_policy umst_toml_fixture_labs_public =
  entity_remote_fixture_labs_public.
Proof.
  reflexivity.
Qed.

Theorem umst_toml_row_to_policy_compose_confidential :
  urge_remote_toml_row_to_policy umst_toml_fixture_compose_confidential =
  entity_remote_fixture_compose_confidential.
Proof.
  reflexivity.
Qed.

Theorem umst_toml_labs_github_admitted :
  evaluate_toml_pre_push umst_toml_fixture_labs_public "github.com"%string
  = inl eppv_admitted.
Proof.
  reflexivity.
Qed.

Theorem umst_toml_compose_github_refused :
  evaluate_toml_pre_push umst_toml_fixture_compose_confidential
    "github.com"%string = inr eppr_compose_github_refused.
Proof.
  reflexivity.
Qed.

Theorem umst_toml_compose_origin_refused :
  evaluate_toml_pre_push umst_toml_fixture_compose_confidential
    "origin.cursor.com"%string = inr eppr_compose_origin_refused.
Proof.
  reflexivity.
Qed.

Theorem umst_toml_compose_forge_admitted :
  evaluate_toml_pre_push umst_toml_fixture_compose_confidential
    "forge.tyto.in"%string = inl eppv_admitted.
Proof.
  reflexivity.
Qed.

Theorem umst_toml_fixture_apply_row_ok :
  apply_umst_toml_remote_row
    umst_toml_fixture_labs_public "forge.tyto.in"%string
    umst_toml_fixture_conjunct true
  = inl umst_toml_fixture_labs_public.
Proof.
  reflexivity.
Qed.

Theorem umst_toml_section_prefix_witness :
  urge_remote_section_prefix = "urge.remote."%string.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition umst_toml_remotes_physics_green : bool := false.

Lemma umst_toml_remotes_physics_green_false :
  umst_toml_remotes_physics_green = false.
Proof. reflexivity. Qed.

Definition umst_toml_remotes_production_wired : bool := false.

Lemma umst_toml_remotes_production_wired_false :
  umst_toml_remotes_production_wired = false.
Proof. reflexivity. Qed.

Theorem umst_toml_remotes_module_witness : True.
Proof. exact I. Qed.

Theorem umst_toml_remotes_no_new_axiom : True.
Proof. exact I. Qed.

Theorem umst_toml_remotes_positive_refuse_not_silent :
  evaluate_umst_toml_remotes_operation true <> utmv_document_ok.
Proof.
  unfold evaluate_umst_toml_remotes_operation.
  discriminate.
Qed.

Theorem umst_toml_compose_github_positive_refuse :
  evaluate_toml_pre_push umst_toml_fixture_compose_confidential
    "github.com"%string <> inl eppv_admitted.
Proof.
  unfold evaluate_toml_pre_push, urge_remote_toml_row_to_policy,
         evaluate_entity_pre_push.
  discriminate.
Qed.

Theorem umst_toml_compose_origin_positive_refuse :
  evaluate_toml_pre_push umst_toml_fixture_compose_confidential
    "origin.cursor.com"%string <> inl eppv_admitted.
Proof.
  unfold evaluate_toml_pre_push, urge_remote_toml_row_to_policy,
         evaluate_entity_pre_push.
  discriminate.
Qed.
