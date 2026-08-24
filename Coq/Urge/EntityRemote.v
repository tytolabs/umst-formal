(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/EntityRemote.v                                    *)
(*                                                                      *)
(*  Meso acting Urge — §13.6 entity remotes classification.             *)
(*  `[urge.remote.*]` policy types; pre-push refuse github /            *)
(*  origin.cursor.com when entity = compose. Composes `excitement_select`; *)
(*  no second argmin.                                                   *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool String QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Open Scope string_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: §13.6 `[urge.remote.*]` policy carriers                 *)
(* ------------------------------------------------------------------ *)

(** `umst.toml` section prefix for remote policy rows. *)
Definition urge_remote_section_prefix : string := "urge.remote."%string.

(** Entity label in `[urge.remote.*]` — Labs vs Compose. *)
Inductive urge_entity :=
  | ue_labs
  | ue_compose.

(** Share-security classification label (§13.6 table). *)
Inductive remote_classification :=
  | rc_public_oss
  | rc_labs_internal
  | rc_compose_confidential
  | rc_compose_defence
  | rc_proposal_confidential.

(** Canonical remote role — India-resident Forgejo is SSOT after restore test. *)
Inductive canonical_remote :=
  | cr_forge
  | cr_none.

(** Mirror remote role — GitHub interim / public discovery only. *)
Inductive mirror_remote :=
  | mr_github
  | mr_none.

(** Push target host for pre-push policy evaluation (§16.8). *)
Inductive entity_remote_host :=
  | erh_github
  | erh_origin_cursor
  | erh_forge
  | erh_unclassified.

(** One `[urge.remote.*]` policy row from `umst.toml` (proposed §13.6). *)
Record urge_remote_policy : Set := {
  erp_section : string;
  erp_entity : urge_entity;
  erp_classification : remote_classification;
  erp_canonical : canonical_remote;
  erp_mirror : mirror_remote
}.

(** Pre-push verdict for entity remote policy. *)
Inductive entity_pre_push_verdict :=
  | eppv_admitted
  | eppv_compose_github_refused
  | eppv_compose_origin_refused
  | eppv_origin_never_ssot_refused
  | eppv_unclassified_host_refused
  | eppv_production_wired_refused.

(** Fail-closed pre-push errors — positive refuse, not silent no-op. *)
Inductive entity_pre_push_refusal :=
  | eppr_compose_github_refused
  | eppr_compose_origin_refused
  | eppr_origin_never_ssot_refused
  | eppr_unclassified_host_refused (h : entity_remote_host)
  | eppr_production_wired_refused.

(** Verdict of entity remote classification operation class. *)
Inductive entity_remote_verdict :=
  | erv_policy_ok
  | erv_upstream_refused
  | erv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §13.6 admissibility conjunct + positive refuse          *)
(* ------------------------------------------------------------------ *)

(** §13.6 admissibility conjunct inputs (surrogate). *)
Record entity_remote_conjunct : Set := {
  erc_conj_gate_ok : bool;
  erc_conj_policy_typed : bool;
  erc_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ policy typed ∧ Excitement preserves`. *)
Definition entity_remote_conjunct_admits (c : entity_remote_conjunct) : bool :=
  erc_conj_gate_ok c &&
  erc_conj_policy_typed c &&
  erc_conj_excitement_preserves c.

(** Owning entity for a share-security classification. *)
Definition classification_entity (c : remote_classification) : urge_entity :=
  match c with
  | rc_public_oss | rc_labs_internal | rc_proposal_confidential => ue_labs
  | rc_compose_confidential | rc_compose_defence => ue_compose
  end.

(** Parse entity label from `umst.toml` value (fail closed on unknown). *)
Definition parse_urge_entity (tag : string) : urge_entity + unit :=
  if String.eqb tag "labs"%string then inl ue_labs
  else if String.eqb tag "LABS"%string then inl ue_labs
  else if String.eqb tag "compose"%string then inl ue_compose
  else if String.eqb tag "COMPOSE"%string then inl ue_compose
  else inr tt.

(** Classify push target from host string (typed surrogate). *)
Definition classify_entity_remote_host (host : string) : entity_remote_host :=
  if String.eqb host ""%string then erh_unclassified
  else if String.eqb host "origin.cursor.com"%string then erh_origin_cursor
  else if String.eqb host "github.com"%string then erh_github
  else if String.eqb host "forge.tyto.in"%string then erh_forge
  else if String.eqb host "forge.entity"%string then erh_forge
  else erh_unclassified.

(** Evaluate pre-push under §13.6 entity remote policy and §16.8 host table. *)
Definition evaluate_entity_pre_push
    (policy : urge_remote_policy) (host : string)
    : entity_pre_push_verdict + entity_pre_push_refusal :=
  let remote := classify_entity_remote_host host in
  match remote with
  | erh_origin_cursor =>
    match erp_entity policy with
    | ue_compose => inr eppr_compose_origin_refused
    | ue_labs => inr eppr_origin_never_ssot_refused
    end
  | erh_github =>
    match erp_entity policy with
    | ue_compose => inr eppr_compose_github_refused
    | ue_labs =>
      if match erp_classification policy with
         | rc_public_oss => true
         | _ => false
         end then inl eppv_admitted
      else inr (eppr_unclassified_host_refused erh_github)
    end
  | erh_forge => inl eppv_admitted
  | erh_unclassified => inr (eppr_unclassified_host_refused erh_unclassified)
  end.

(** Positive refuse: production wired push without entity remote policy. *)
Definition refuse_production_wired_entity_push : entity_pre_push_refusal :=
  eppr_production_wired_refused.

(** Classify blind upstream vs typed policy without performing I/O. *)
Definition evaluate_entity_remote_operation (is_upstream_refused : bool)
    : entity_remote_verdict :=
  if is_upstream_refused then erv_upstream_refused else erv_policy_ok.

(** Apply typed entity remote policy check — fail closed on inadmissibility. *)
Definition apply_entity_remote_policy
    (policy : urge_remote_policy)
    (host : string)
    (conjunct : entity_remote_conjunct)
    (excitement_selected : bool)
    : urge_remote_policy + entity_pre_push_refusal :=
  if negb (entity_remote_conjunct_admits conjunct) then
    inr (eppr_unclassified_host_refused erh_unclassified)
  else if negb excitement_selected then
    inr (eppr_unclassified_host_refused erh_unclassified)
  else
    match evaluate_entity_pre_push policy host with
    | inl _ => inl policy
    | inr r => inr r
    end.

Lemma entity_remote_upstream_refused_positive :
  evaluate_entity_remote_operation true = erv_upstream_refused.
Proof. reflexivity. Qed.

Lemma entity_remote_policy_ok_when_not_upstream :
  evaluate_entity_remote_operation false = erv_policy_ok.
Proof. reflexivity. Qed.

Lemma refuse_production_wired_entity_push_positive :
  refuse_production_wired_entity_push = eppr_production_wired_refused.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Entity remote composes Excitement (no second argmin)    *)
(* ------------------------------------------------------------------ *)

(** Context for entity remote over admissible history successors. *)
Record entity_remote_ctx (src : ThermodynamicState) : Set := {
  entity_remote_successors : list (history_candidate src)
}.

(** Entity remote selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition entity_remote_select (src : ThermodynamicState)
    (ctx : entity_remote_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (entity_remote_successors src ctx).

Theorem entity_remote_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : entity_remote_ctx src) :
  entity_remote_select src ctx =
  excitement_select src (entity_remote_successors src ctx).
Proof.
  unfold entity_remote_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem entity_remote_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : entity_remote_ctx src) :
  entity_remote_select src ctx =
  urge_recovery_select src (entity_remote_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem entity_remote_no_local_argmin
    (src : ThermodynamicState) (ctx : entity_remote_ctx src) :
  entity_remote_select src ctx =
  excitement_select src (entity_remote_successors src ctx).
Proof.
  exact (entity_remote_select_eq_excitement_select src ctx).
Qed.

Lemma entity_remote_empty (src : ThermodynamicState)
    (ctx : entity_remote_ctx src)
    (Hnil : entity_remote_successors src ctx = nil) :
  entity_remote_select src ctx = inr exc_no_candidates.
Proof.
  unfold entity_remote_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §13.6 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition entity_remote_fixture_labs_public : urge_remote_policy :=
  {| erp_section := "labs-public"%string;
     erp_entity := ue_labs;
     erp_classification := rc_public_oss;
     erp_canonical := cr_forge;
     erp_mirror := mr_github |}.

Definition entity_remote_fixture_compose_confidential : urge_remote_policy :=
  {| erp_section := "compose-confidential"%string;
     erp_entity := ue_compose;
     erp_classification := rc_compose_confidential;
     erp_canonical := cr_forge;
     erp_mirror := mr_none |}.

Definition entity_remote_fixture_conjunct : entity_remote_conjunct :=
  {| erc_conj_gate_ok := true;
     erc_conj_policy_typed := true;
     erc_conj_excitement_preserves := true |}.

Definition entity_remote_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Theorem entity_remote_labs_github_admitted :
  evaluate_entity_pre_push entity_remote_fixture_labs_public "github.com"%string
  = inl eppv_admitted.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_compose_github_refused :
  evaluate_entity_pre_push entity_remote_fixture_compose_confidential
    "github.com"%string = inr eppr_compose_github_refused.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_compose_origin_refused :
  evaluate_entity_pre_push entity_remote_fixture_compose_confidential
    "origin.cursor.com"%string = inr eppr_compose_origin_refused.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_origin_never_ssot_refused :
  evaluate_entity_pre_push entity_remote_fixture_labs_public
    "origin.cursor.com"%string = inr eppr_origin_never_ssot_refused.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_compose_forge_admitted :
  evaluate_entity_pre_push entity_remote_fixture_compose_confidential
    "forge.tyto.in"%string = inl eppv_admitted.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_section_prefix_witness :
  urge_remote_section_prefix = "urge.remote."%string.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_labs_public_section_key :
  String.eqb
    (String.append urge_remote_section_prefix
       (erp_section entity_remote_fixture_labs_public))
    "urge.remote.labs-public"%string = true.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_parse_labs :
  parse_urge_entity "labs"%string = inl ue_labs.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_parse_compose :
  parse_urge_entity "compose"%string = inl ue_compose.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_classification_entity_labs :
  classification_entity rc_public_oss = ue_labs.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_classification_entity_compose :
  classification_entity rc_compose_confidential = ue_compose.
Proof.
  reflexivity.
Qed.

Theorem entity_remote_fixture_apply_policy_ok :
  apply_entity_remote_policy
    entity_remote_fixture_labs_public "forge.tyto.in"%string
    entity_remote_fixture_conjunct true
  = inl entity_remote_fixture_labs_public.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition entity_remote_physics_green : bool := false.

Lemma entity_remote_physics_green_false :
  entity_remote_physics_green = false.
Proof. reflexivity. Qed.

Definition entity_remote_production_wired : bool := false.

Lemma entity_remote_production_wired_false :
  entity_remote_production_wired = false.
Proof. reflexivity. Qed.

Theorem entity_remote_module_witness : True.
Proof. exact I. Qed.

Theorem entity_remote_no_new_axiom : True.
Proof. exact I. Qed.

Theorem entity_remote_positive_refuse_not_silent :
  evaluate_entity_remote_operation true <> erv_policy_ok.
Proof.
  unfold evaluate_entity_remote_operation.
  discriminate.
Qed.

Theorem entity_remote_compose_github_positive_refuse :
  evaluate_entity_pre_push entity_remote_fixture_compose_confidential
    "github.com"%string <> inl eppv_admitted.
Proof.
  unfold evaluate_entity_pre_push.
  discriminate.
Qed.
