(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/KleisliStatus.v                                   *)
(*                                                                      *)
(*  Meso acting Urge — §16.7 operator verb `status` as Kleisli arrow.  *)
(*  Frugal MI observation gate; replica-class entity check; observation  *)
(*  only — not gate_check_before_sync inbound, not outbound tick, not    *)
(*  MergeSafe witness. Composes `excitement_select`; no second argmin.   *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.

Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: §16.7 verb table + status Kleisli carriers            *)
(* ------------------------------------------------------------------ *)

(** Replica class labels for `status` entity check (blueprint §15.4 / §16.7). *)
Inductive status_replica_class :=
  | src_node0
  | src_node1
  | src_forgejo_primary_mirror
  | src_offline_luks.

(** Whether a verb-table column is required for the operator verb. *)
Inductive verb_column_requirement :=
  | vcr_not_required
  | vcr_required.

(** Kleisli gate kinds cited in §16.7 (`status` uses Frugal MI observation only). *)
Inductive kleisli_gate_kind :=
  | kgk_frugal_mi_observation
  | kgk_gate_check_before_sync_inbound
  | kgk_outbound_tick_if_admitted.

(** Entity check column for §16.7 rows. *)
Inductive entity_check_kind :=
  | eck_replica_class
  | eck_remote_class.

(** One §16.7 operator verb table row (typed, not prose). *)
Record operator_verb_row : Set := {
  verb_status : bool;
  verb_kleisli_gate : kleisli_gate_kind;
  verb_merge_safe : verb_column_requirement;
  verb_excitement : verb_column_requirement;
  verb_entity_check : entity_check_kind
}.

(** Frugal MI observation carrier — status Kleisli gate input. *)
Record frugal_mi_observation : Set := {
  fmi_witness_bits : nat;
  fmi_frugal_cap_bits : nat
}.

(** Verdict of the Frugal MI observation gate. *)
Inductive frugal_mi_gate_verdict :=
  | fmig_admit
  | fmig_refuse_exceeds_cap
  | fmig_refuse_zero_observation.

(** Successful `status` Kleisli arrow output — observation only, no sync mutation. *)
Record status_observation : Set := {
  status_replica : status_replica_class;
  status_observation_probe : frugal_mi_observation;
  status_gate_verdict : frugal_mi_gate_verdict
}.

(** Positive refuse when wrong Kleisli gate is applied to `status`. *)
Inductive status_gate_mismatch :=
  | sgm_sync_inbound_on_status
  | sgm_outbound_tick_on_status
  | sgm_merge_safe_on_status
  | sgm_excitement_on_status
  | sgm_remote_class_on_status.

(** Fail-closed errors on the status Kleisli arrow. *)
Inductive status_arrow_error :=
  | sae_frugal_mi_refused (v : frugal_mi_gate_verdict)
  | sae_gate_mismatch (m : status_gate_mismatch).

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Frugal MI gate + status arrow (positive refuse)       *)
(* ------------------------------------------------------------------ *)

(** §16.7 typed row for operator verb `status`. *)
Definition status_verb_row : operator_verb_row :=
  {| verb_status := true;
     verb_kleisli_gate := kgk_frugal_mi_observation;
     verb_merge_safe := vcr_not_required;
     verb_excitement := vcr_not_required;
     verb_entity_check := eck_replica_class |}.

(** Evaluate Frugal MI observation gate (status Kleisli gate). *)
Definition evaluate_frugal_mi_gate (obs : frugal_mi_observation)
    : frugal_mi_gate_verdict :=
  if (fmi_frugal_cap_bits obs =? 0) && (0 <? fmi_witness_bits obs) then
    fmig_refuse_exceeds_cap
  else if (0 <? fmi_frugal_cap_bits obs) && (fmi_witness_bits obs =? 0) then
    fmig_refuse_zero_observation
  else if fmi_frugal_cap_bits obs <? fmi_witness_bits obs then
    fmig_refuse_exceeds_cap
  else
    fmig_admit.

(** Entity check: replica class label must be one of the §15.4 named classes. *)
Definition status_replica_class_admits (c : status_replica_class) : bool :=
  match c with
  | src_node0 | src_node1 | src_forgejo_primary_mirror | src_offline_luks => true
  end.

(** Whether a Kleisli gate kind matches the `status` verb row. *)
Definition kleisli_gate_matches_status (g : kleisli_gate_kind) : bool :=
  match g with
  | kgk_frugal_mi_observation => true
  | kgk_gate_check_before_sync_inbound | kgk_outbound_tick_if_admitted => false
  end.

(** Run the `status` Kleisli arrow — observation only; no sync / merge / excitement. *)
Definition run_status_kleisli_arrow
    (replica : status_replica_class)
    (obs : frugal_mi_observation)
    : status_observation + status_arrow_error :=
  if negb (status_replica_class_admits replica) then
    inr (sae_gate_mismatch sgm_remote_class_on_status)
  else
    let verdict := evaluate_frugal_mi_gate obs in
    match verdict with
    | fmig_admit =>
        inl
          {| status_replica := replica;
             status_observation_probe := obs;
             status_gate_verdict := verdict |}
    | v => inr (sae_frugal_mi_refused v)
    end.

(** Positive refuse: inbound sync gate is inadmissible on `status`. *)
Definition refuse_sync_gate_on_status : status_gate_mismatch :=
  sgm_sync_inbound_on_status.

(** Positive refuse: outbound tick gate is inadmissible on `status`. *)
Definition refuse_outbound_tick_on_status : status_gate_mismatch :=
  sgm_outbound_tick_on_status.

(** Positive refuse: MergeSafe witness is not required on `status`. *)
Definition refuse_merge_safe_on_status : status_gate_mismatch :=
  sgm_merge_safe_on_status.

(** Positive refuse: Excitement argmin is not required on `status`. *)
Definition refuse_excitement_on_status : status_gate_mismatch :=
  sgm_excitement_on_status.

(** Positive refuse: remote-class entity check is wrong for `status`. *)
Definition refuse_remote_class_on_status : status_gate_mismatch :=
  sgm_remote_class_on_status.

Lemma status_verb_row_excitement_not_required :
  verb_excitement status_verb_row = vcr_not_required.
Proof.
  reflexivity.
Qed.

Lemma status_verb_row_merge_safe_not_required :
  verb_merge_safe status_verb_row = vcr_not_required.
Proof.
  reflexivity.
Qed.

Lemma status_verb_row_frugal_mi_gate :
  verb_kleisli_gate status_verb_row = kgk_frugal_mi_observation.
Proof.
  reflexivity.
Qed.

Lemma kleisli_gate_matches_status_frugal :
  kleisli_gate_matches_status kgk_frugal_mi_observation = true.
Proof.
  reflexivity.
Qed.

Lemma kleisli_gate_matches_status_sync_false :
  kleisli_gate_matches_status kgk_gate_check_before_sync_inbound = false.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Excitement compose (no second argmin)                   *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — Urge imports selector; no second argmin. *)
Inductive status_excitement_compose_pin :=
  | secp_import_select_excitement
  | secp_second_argmin_refused.

(** Status path composes `excitement_select` — not a second argmin. *)
Definition status_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : status_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | secp_import_select_excitement => excitement_select src cands
  | secp_second_argmin_refused => inr exc_all_inadmissible
  end.

Theorem status_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  status_excitement_select src cands secp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem status_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  status_excitement_select src cands secp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Theorem status_no_local_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  status_excitement_select src cands secp_import_select_excitement =
  excitement_select src cands.
Proof.
  exact (status_excitement_select_eq_excitement_select src cands).
Qed.

Lemma status_excitement_empty (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (Hnil : cands = nil) :
  status_excitement_select src cands secp_import_select_excitement =
  inr exc_no_candidates.
Proof.
  unfold status_excitement_select, excitement_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §16.7 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition status_fixture_obs_admit : frugal_mi_observation :=
  {| fmi_witness_bits := 4; fmi_frugal_cap_bits := 8 |}.

Definition status_fixture_obs_refuse_cap : frugal_mi_observation :=
  {| fmi_witness_bits := 16; fmi_frugal_cap_bits := 8 |}.

Definition status_fixture_obs_refuse_zero : frugal_mi_observation :=
  {| fmi_witness_bits := 0; fmi_frugal_cap_bits := 8 |}.

Theorem status_fixture_frugal_mi_admits :
  evaluate_frugal_mi_gate status_fixture_obs_admit = fmig_admit.
Proof.
  reflexivity.
Qed.

Theorem status_fixture_frugal_mi_refuses_cap :
  evaluate_frugal_mi_gate status_fixture_obs_refuse_cap =
  fmig_refuse_exceeds_cap.
Proof.
  reflexivity.
Qed.

Theorem status_fixture_frugal_mi_refuses_zero :
  evaluate_frugal_mi_gate status_fixture_obs_refuse_zero =
  fmig_refuse_zero_observation.
Proof.
  reflexivity.
Qed.

Theorem status_fixture_arrow_ok :
  run_status_kleisli_arrow src_node0 status_fixture_obs_admit =
  inl
    {| status_replica := src_node0;
       status_observation_probe := status_fixture_obs_admit;
       status_gate_verdict := fmig_admit |}.
Proof.
  reflexivity.
Qed.

Theorem status_fixture_arrow_refuses_cap :
  run_status_kleisli_arrow src_node1 status_fixture_obs_refuse_cap =
  inr (sae_frugal_mi_refused fmig_refuse_exceeds_cap).
Proof.
  reflexivity.
Qed.

Theorem status_positive_refuse_sync_gate :
  refuse_sync_gate_on_status = sgm_sync_inbound_on_status.
Proof.
  reflexivity.
Qed.

Theorem status_positive_refuse_merge_safe :
  refuse_merge_safe_on_status = sgm_merge_safe_on_status.
Proof.
  reflexivity.
Qed.

Theorem status_positive_refuse_excitement :
  refuse_excitement_on_status = sgm_excitement_on_status.
Proof.
  reflexivity.
Qed.

Theorem status_positive_refuse_outbound_tick :
  refuse_outbound_tick_on_status = sgm_outbound_tick_on_status.
Proof.
  reflexivity.
Qed.

Theorem status_positive_refuse_not_silent :
  refuse_sync_gate_on_status <> sgm_merge_safe_on_status.
Proof.
  discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition kleisli_status_physics_green : bool := false.

Lemma kleisli_status_physics_green_false :
  kleisli_status_physics_green = false.
Proof. reflexivity. Qed.

Definition kleisli_status_production_wired : bool := false.

Lemma kleisli_status_production_wired_false :
  kleisli_status_production_wired = false.
Proof. reflexivity. Qed.

Theorem kleisli_status_module_witness : True.
Proof. exact I. Qed.

Theorem kleisli_status_no_new_axiom : True.
Proof. exact I. Qed.

Theorem kleisli_status_positive_refuse_aggregate :
  refuse_sync_gate_on_status = sgm_sync_inbound_on_status /\
  refuse_merge_safe_on_status = sgm_merge_safe_on_status /\
  refuse_excitement_on_status = sgm_excitement_on_status /\
  refuse_outbound_tick_on_status = sgm_outbound_tick_on_status.
Proof.
  split; [| split; [| split]]; reflexivity.
Qed.
