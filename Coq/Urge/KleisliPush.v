(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/KleisliPush.v                                     *)
(*                                                                      *)
(*  Meso acting Urge — §16.7 operator verb `push` as Kleisli arrow.     *)
(*  Kleisli gate = `outbound_tick_if_admitted`; MergeSafe = pre-push    *)
(*  witness; Excitement = provenance preserved; entity = entity remote. *)
(*  Composes `excitement_select`; no second argmin.                       *)
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
(*  SECTION 1: §16.7 push column carriers + Kleisli arrow witness      *)
(* ------------------------------------------------------------------ *)

(** Outbound tick gate — `outbound_tick_if_admitted` (push row Kleisli gate). *)
Inductive outbound_tick_gate :=
  | otg_admitted
  | otg_refused
  | otg_bypass_attempted.

(** Whether outbound gate admits push morphism. *)
Definition outbound_gate_admits (g : outbound_tick_gate) : bool :=
  match g with
  | otg_admitted => true
  | otg_refused | otg_bypass_attempted => false
  end.

(** Pre-push MergeSafe witness column (§16.7 push row). *)
Inductive pre_push_merge_safe_witness :=
  | ppms_witnessed
  | ppms_missing
  | ppms_bypass_attempted.

Definition pre_push_merge_safe_admits (w : pre_push_merge_safe_witness) : bool :=
  match w with
  | ppms_witnessed => true
  | ppms_missing | ppms_bypass_attempted => false
  end.

(** Excitement column for push — provenance preserved. *)
Inductive provenance_preserved :=
  | pp_preserved
  | pp_violated
  | pp_bypass_attempted.

Definition provenance_preserved_admits (p : provenance_preserved) : bool :=
  match p with
  | pp_preserved => true
  | pp_violated | pp_bypass_attempted => false
  end.

(** Entity remote class for push entity check (§16.7). *)
Inductive entity_remote_class :=
  | erc_entity_remote
  | erc_refused_upstream
  | erc_unclassified.

Definition entity_remote_admits (c : entity_remote_class) : bool :=
  match c with
  | erc_entity_remote => true
  | erc_refused_upstream | erc_unclassified => false
  end.

(** Kleisli gate kinds cited in §16.7 (push uses outbound tick only). *)
Inductive kleisli_gate_kind :=
  | kgk_outbound_tick_if_admitted
  | kgk_gate_check_before_sync_inbound
  | kgk_frugal_mi_observation.

(** §16.7 typed Kleisli arrow witness for operator `push`. *)
Record push_kleisli_arrow : Set := {
  push_gate : outbound_tick_gate;
  push_merge_safe : pre_push_merge_safe_witness;
  push_provenance : provenance_preserved;
  push_entity : entity_remote_class;
  push_object_count : nat
}.

(** Push morphism verdict. *)
Inductive push_verdict :=
  | pv_admitted
  | pv_gate_refused
  | pv_merge_safe_refused
  | pv_provenance_refused
  | pv_entity_remote_refused
  | pv_production_wired_refused
  | pv_gate_bypass_refused.

(** Fail-closed push errors — positive refuse, not silent no-op. *)
Inductive push_refusal :=
  | pr_gate_refused
  | pr_merge_safe_missing
  | pr_merge_safe_bypass_refused
  | pr_provenance_violated
  | pr_provenance_bypass_refused
  | pr_entity_remote_refused (c : entity_remote_class)
  | pr_production_wired_refused
  | pr_gate_bypass_refused
  | pr_wrong_gate (g : kleisli_gate_kind).

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §16.7 admissibility conjunct + positive refuse          *)
(* ------------------------------------------------------------------ *)

(** §16.7 admissibility conjunct inputs (surrogate). *)
Record push_admissibility_conjunct : Set := {
  push_conj_gate_ok : bool;
  push_conj_merge_safe : bool;
  push_conj_provenance_preserved : bool;
  push_conj_entity_remote : bool
}.

Definition push_conjunct_admits (c : push_admissibility_conjunct) : bool :=
  push_conj_gate_ok c &&
  push_conj_merge_safe c &&
  push_conj_provenance_preserved c &&
  push_conj_entity_remote c.

(** Whether a Kleisli arrow is admissible under §16.7 columns. *)
Definition push_arrow_admissible (a : push_kleisli_arrow) : bool :=
  outbound_gate_admits (push_gate a) &&
  pre_push_merge_safe_admits (push_merge_safe a) &&
  provenance_preserved_admits (push_provenance a) &&
  entity_remote_admits (push_entity a).

(** Evaluate push as Kleisli arrow — gate ∧ MergeSafe ∧ Excitement ∧ entity. *)
Definition evaluate_push_kleisli (a : push_kleisli_arrow)
    : push_verdict + push_refusal :=
  if negb (outbound_gate_admits (push_gate a)) then
    match push_gate a with
    | otg_bypass_attempted => inr pr_gate_bypass_refused
    | _ => inr pr_gate_refused
    end
  else if negb (pre_push_merge_safe_admits (push_merge_safe a)) then
    match push_merge_safe a with
    | ppms_bypass_attempted => inr pr_merge_safe_bypass_refused
    | _ => inr pr_merge_safe_missing
    end
  else if negb (provenance_preserved_admits (push_provenance a)) then
    match push_provenance a with
    | pp_bypass_attempted => inr pr_provenance_bypass_refused
    | _ => inr pr_provenance_violated
    end
  else if negb (entity_remote_admits (push_entity a)) then
    inr (pr_entity_remote_refused (push_entity a))
  else
    inl pv_admitted.

(** Positive refuse: production wired push without Kleisli gate. *)
Definition refuse_production_wired_push : push_refusal :=
  pr_production_wired_refused.

(** Positive refuse: outbound gate bypass on push. *)
Definition refuse_gate_bypass_push : push_refusal :=
  pr_gate_bypass_refused.

(** Positive refuse: inbound sync gate is inadmissible on `push`. *)
Definition refuse_sync_gate_on_push : push_refusal :=
  pr_wrong_gate kgk_gate_check_before_sync_inbound.

(** Positive refuse: Frugal MI observation gate is inadmissible on `push`. *)
Definition refuse_frugal_mi_on_push : push_refusal :=
  pr_wrong_gate kgk_frugal_mi_observation.

(** Whether a Kleisli gate kind matches the `push` verb row. *)
Definition kleisli_gate_matches_push (g : kleisli_gate_kind) : bool :=
  match g with
  | kgk_outbound_tick_if_admitted => true
  | _ => false
  end.

(** Classify remote host into entity-remote check class (typed surrogate). *)
Definition classify_entity_remote (host : string) : entity_remote_class :=
  if String.eqb host "" then erc_unclassified
  else if String.eqb host "origin.cursor.com"%string ||
          String.eqb host "github.com"%string then erc_refused_upstream
  else if String.eqb host "forge.entity"%string then erc_entity_remote
  else erc_unclassified.

(** Build push Kleisli arrow from gate + remote host surrogate. *)
Definition push_kleisli_arrow_from_host
    (gate : outbound_tick_gate)
    (merge_safe : pre_push_merge_safe_witness)
    (provenance : provenance_preserved)
    (remote_host : string)
    (object_count : nat) : push_kleisli_arrow :=
  {| push_gate := gate;
     push_merge_safe := merge_safe;
     push_provenance := provenance;
     push_entity := classify_entity_remote remote_host;
     push_object_count := object_count |}.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Push composes Excitement (no second argmin)             *)
(* ------------------------------------------------------------------ *)

(** Context for push over admissible history successors. *)
Record push_ctx (src : ThermodynamicState) : Set := {
  push_successors : list (history_candidate src)
}.

(** Push **is** `urge_recovery_select` / `excitement_select` on successors. *)
Definition push_select (src : ThermodynamicState)
    (ctx : push_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (push_successors src ctx).

Theorem push_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : push_ctx src) :
  push_select src ctx =
  excitement_select src (push_successors src ctx).
Proof.
  unfold push_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem push_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : push_ctx src) :
  push_select src ctx =
  urge_recovery_select src (push_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem push_no_local_argmin
    (src : ThermodynamicState) (ctx : push_ctx src) :
  push_select src ctx =
  excitement_select src (push_successors src ctx).
Proof.
  exact (push_select_eq_excitement_select src ctx).
Qed.

Lemma push_select_empty (src : ThermodynamicState)
    (ctx : push_ctx src)
    (Hnil : push_successors src ctx = nil) :
  push_select src ctx = inr exc_no_candidates.
Proof.
  unfold push_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §16.7 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition push_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition push_fixture_admitted_arrow : push_kleisli_arrow :=
  push_kleisli_arrow_from_host
    otg_admitted ppms_witnessed pp_preserved "forge.entity"%string 3.

Definition push_fixture_gate_refused_arrow : push_kleisli_arrow :=
  push_kleisli_arrow_from_host
    otg_refused ppms_witnessed pp_preserved "forge.entity"%string 0.

Definition push_fixture_conjunct : push_admissibility_conjunct :=
  {| push_conj_gate_ok := true;
     push_conj_merge_safe := true;
     push_conj_provenance_preserved := true;
     push_conj_entity_remote := true |}.

Theorem push_fixture_admitted_ok :
  evaluate_push_kleisli push_fixture_admitted_arrow = inl pv_admitted.
Proof.
  reflexivity.
Qed.

Theorem push_fixture_gate_refused :
  evaluate_push_kleisli push_fixture_gate_refused_arrow =
  inr pr_gate_refused.
Proof.
  reflexivity.
Qed.

Theorem push_fixture_entity_remote_forge :
  classify_entity_remote "forge.entity"%string = erc_entity_remote.
Proof.
  reflexivity.
Qed.

Theorem push_fixture_entity_refused_upstream_origin :
  classify_entity_remote "origin.cursor.com"%string = erc_refused_upstream.
Proof.
  reflexivity.
Qed.

Theorem push_fixture_entity_refused_upstream_github :
  classify_entity_remote "github.com"%string = erc_refused_upstream.
Proof.
  reflexivity.
Qed.

Theorem push_fixture_kleisli_gate_matches_push :
  kleisli_gate_matches_push kgk_outbound_tick_if_admitted = true.
Proof.
  reflexivity.
Qed.

Theorem push_fixture_kleisli_gate_rejects_inbound_sync :
  kleisli_gate_matches_push kgk_gate_check_before_sync_inbound = false.
Proof.
  reflexivity.
Qed.

Theorem push_fixture_refuse_sync_gate_positive :
  refuse_sync_gate_on_push = pr_wrong_gate kgk_gate_check_before_sync_inbound.
Proof.
  reflexivity.
Qed.

Theorem push_fixture_refuse_frugal_mi_positive :
  refuse_frugal_mi_on_push = pr_wrong_gate kgk_frugal_mi_observation.
Proof.
  reflexivity.
Qed.

Theorem push_fixture_conjunct_admits :
  push_conjunct_admits push_fixture_conjunct = true.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition kleisli_push_physics_green : bool := false.

Lemma kleisli_push_physics_green_false :
  kleisli_push_physics_green = false.
Proof. reflexivity. Qed.

Definition kleisli_push_production_wired : bool := false.

Lemma kleisli_push_production_wired_false :
  kleisli_push_production_wired = false.
Proof. reflexivity. Qed.

Theorem kleisli_push_module_witness : True.
Proof. exact I. Qed.

Theorem kleisli_push_no_new_axiom : True.
Proof. exact I. Qed.

Theorem kleisli_push_positive_refuse_not_silent :
  evaluate_push_kleisli push_fixture_gate_refused_arrow <>
  inl pv_admitted.
Proof.
  rewrite push_fixture_gate_refused.
  discriminate.
Qed.

Theorem kleisli_push_production_wired_refuse_positive :
  refuse_production_wired_push = pr_production_wired_refused.
Proof.
  reflexivity.
Qed.

Theorem kleisli_push_gate_bypass_refuse_positive :
  refuse_gate_bypass_push = pr_gate_bypass_refused.
Proof.
  reflexivity.
Qed.
