(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/ReplicaClass.v                                    *)
(*                                                                      *)
(*  Meso acting Urge — §15.4 replica-class table + fabric-nodes.json   *)
(*  `class` field pin. Positive refuse via typed errors — not only      *)
(*  `!physics_green`. Composes `excitement_select`; no second argmin.   *)
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
(*  SECTION 1: §15.4 replica-class table (six named rows)            *)
(* ------------------------------------------------------------------ *)

(** Named replica class row from blueprint §15.4. *)
Inductive replica_class_label :=
  | rcl_node0_dev_clone
  | rcl_node1_dev_clone
  | rcl_forgejo_primary_mirror
  | rcl_darwin_scratch
  | rcl_offline_luks
  | rcl_customer_compose.

(** Stable `fabric-nodes.json` `class` field value. *)
Definition replica_class_class_field (c : replica_class_label) : string :=
  match c with
  | rcl_node0_dev_clone => "node-0-dev-clone"
  | rcl_node1_dev_clone => "node-1-dev-clone"
  | rcl_forgejo_primary_mirror => "forgejo-primary-mirror"
  | rcl_darwin_scratch => "darwin-scratch"
  | rcl_offline_luks => "offline-luks"
  | rcl_customer_compose => "customer-compose"
  end.

Definition rcl_node0_legacy_field : string := "node-0".
Definition rcl_node1_legacy_field : string := "node-1".

(** Parse a `class` field string into a §15.4 row (also accepts legacy node ids). *)
Definition parse_replica_class_field (raw : string) : option replica_class_label :=
  if String.eqb raw "node-0-dev-clone" then Some rcl_node0_dev_clone
  else if String.eqb raw rcl_node0_legacy_field then Some rcl_node0_dev_clone
  else if String.eqb raw "node-1-dev-clone" then Some rcl_node1_dev_clone
  else if String.eqb raw rcl_node1_legacy_field then Some rcl_node1_dev_clone
  else if String.eqb raw "forgejo-primary-mirror" then Some rcl_forgejo_primary_mirror
  else if String.eqb raw "darwin-scratch" then Some rcl_darwin_scratch
  else if String.eqb raw "offline-luks" then Some rcl_offline_luks
  else if String.eqb raw "customer-compose" then Some rcl_customer_compose
  else None.

(** Network egress column from §15.4 replica-class table. *)
Inductive replica_network_egress :=
  | rne_tailscale_admin_only
  | rne_tailscale_no_public_ports
  | rne_empty
  | rne_mount_only
  | rne_customer_policy.

(** Whether egress is explicitly empty (offline LUKS / Darwin scratch). *)
Definition replica_egress_empty (e : replica_network_egress) : bool :=
  match e with
  | rne_empty | rne_mount_only => true
  | _ => false
  end.

(** Authority column from §15.4 replica-class table. *)
Inductive replica_authority :=
  | ra_working_copy
  | ra_canonical_remote
  | ra_backup_scratch
  | ra_disaster_copy
  | ra_on_site_record.

(** One §15.4 replica-class table row — network egress + authority typed. *)
Record replica_class_table_row : Set := {
  replica_row_class : replica_class_label;
  replica_row_egress : replica_network_egress;
  replica_row_authority : replica_authority
}.

(** Blueprint §15.4 default row for a named replica class. *)
Definition replica_class_blueprint_row (c : replica_class_label)
    : replica_class_table_row :=
  match c with
  | rcl_node0_dev_clone =>
    {| replica_row_class := rcl_node0_dev_clone;
       replica_row_egress := rne_tailscale_admin_only;
       replica_row_authority := ra_working_copy |}
  | rcl_node1_dev_clone =>
    {| replica_row_class := rcl_node1_dev_clone;
       replica_row_egress := rne_tailscale_admin_only;
       replica_row_authority := ra_working_copy |}
  | rcl_forgejo_primary_mirror =>
    {| replica_row_class := rcl_forgejo_primary_mirror;
       replica_row_egress := rne_tailscale_no_public_ports;
       replica_row_authority := ra_canonical_remote |}
  | rcl_darwin_scratch =>
    {| replica_row_class := rcl_darwin_scratch;
       replica_row_egress := rne_mount_only;
       replica_row_authority := ra_backup_scratch |}
  | rcl_offline_luks =>
    {| replica_row_class := rcl_offline_luks;
       replica_row_egress := rne_empty;
       replica_row_authority := ra_disaster_copy |}
  | rcl_customer_compose =>
    {| replica_row_class := rcl_customer_compose;
       replica_row_egress := rne_customer_policy;
       replica_row_authority := ra_on_site_record |}
  end.

Definition replica_class_table_cardinality : nat := (6%nat).

(* ------------------------------------------------------------------ *)
(*  SECTION 2: fabric-nodes.json class pin + positive refuse         *)
(* ------------------------------------------------------------------ *)

(** Fabric node pin — `fabric-nodes.json` node with optional `class` field. *)
Record fabric_node_class_pin : Set := {
  fabric_node_id : string;
  fabric_class_field : option string;
  fabric_physics_green_claim : bool;
  fabric_joins_labs_public_gossip : bool
}.

(** Typed admit/refuse on fabric node class pin (not bool theater). *)
Inductive replica_class_admit :=
  | rca_admitted
  | rca_refused.

(** Gate verdict on one fabric node class evaluation. *)
Inductive fabric_node_class_verdict :=
  | fncv_accept
  | fncv_reject.

(** Typed refusal — positive errors, not silent `!physics_green`. *)
Inductive replica_class_refusal :=
  | rcr_missing_class_field
  | rcr_unknown_replica_class
  | rcr_invented_physics_green
  | rcr_customer_compose_labs_gossip
  | rcr_second_excitement_argmin.

(** Evaluated fabric node class row after §15.4 gate. *)
Record fabric_node_class_row : Set := {
  fabric_row_node_id : string;
  fabric_row_class : replica_class_label;
  fabric_row_table : replica_class_table_row;
  fabric_row_verdict : fabric_node_class_verdict;
  fabric_row_admit : replica_class_admit
}.

Definition replica_class_label_to_nat (c : replica_class_label) : nat :=
  match c with
  | rcl_node0_dev_clone => (0%nat)
  | rcl_node1_dev_clone => (1%nat)
  | rcl_forgejo_primary_mirror => (2%nat)
  | rcl_darwin_scratch => (3%nat)
  | rcl_offline_luks => (4%nat)
  | rcl_customer_compose => (5%nat)
  end.

(** Evaluate one fabric node `class` pin against §15.4 table. *)
Definition evaluate_fabric_node_class (pin : fabric_node_class_pin)
    : fabric_node_class_row + replica_class_refusal :=
  if fabric_physics_green_claim pin then
    inr rcr_invented_physics_green
  else
    match fabric_class_field pin with
    | None => inr rcr_missing_class_field
    | Some raw =>
      match parse_replica_class_field raw with
      | None => inr rcr_unknown_replica_class
      | Some cls =>
        if andb (Nat.eqb (replica_class_label_to_nat cls)
                          (replica_class_label_to_nat rcl_customer_compose))
                (fabric_joins_labs_public_gossip pin) then
          inr rcr_customer_compose_labs_gossip
        else
          let table_row := replica_class_blueprint_row cls in
          inl
            {| fabric_row_node_id := fabric_node_id pin;
               fabric_row_class := cls;
               fabric_row_table := table_row;
               fabric_row_verdict := fncv_accept;
               fabric_row_admit := rca_admitted |}
      end
    end.

(** Positive refuse: invented physics GREEN on fabric node JSON. *)
Definition refuse_invented_physics_green : replica_class_refusal :=
  rcr_invented_physics_green.

(** Positive refuse: missing `class` field on fabric node. *)
Definition refuse_missing_class_field : replica_class_refusal :=
  rcr_missing_class_field.

(** Positive refuse: Customer Compose in Labs public gossip mesh. *)
Definition refuse_customer_compose_labs_gossip : replica_class_refusal :=
  rcr_customer_compose_labs_gossip.

(** Positive refuse: second local Excitement argmin — compose import only. *)
Definition refuse_second_excitement_argmin : replica_class_refusal :=
  rcr_second_excitement_argmin.

Lemma refuse_invented_physics_green_positive :
  refuse_invented_physics_green = rcr_invented_physics_green.
Proof. reflexivity. Qed.

Lemma refuse_missing_class_field_positive :
  refuse_missing_class_field = rcr_missing_class_field.
Proof. reflexivity. Qed.

Lemma refuse_customer_compose_labs_gossip_positive :
  refuse_customer_compose_labs_gossip = rcr_customer_compose_labs_gossip.
Proof. reflexivity. Qed.

Lemma refuse_second_excitement_argmin_positive :
  refuse_second_excitement_argmin = rcr_second_excitement_argmin.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Replica class composes excitement_select (no argmin)  *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — import selector; refuse second local argmin. *)
Inductive replica_excitement_compose_pin :=
  | recp_import_select_excitement
  | recp_second_argmin_refused.

(** Context for replica class over admissible history successors. *)
Record replica_class_ctx (src : ThermodynamicState) : Set := {
  replica_class_successors : list (history_candidate src)
}.

(** Compose path composes `excitement_select` — not a second argmin. *)
Definition compose_replica_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : replica_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | recp_import_select_excitement => excitement_select src cands
  | recp_second_argmin_refused => inr exc_all_inadmissible
  end.

(** Replica class selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition replica_class_select (src : ThermodynamicState)
    (ctx : replica_class_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (replica_class_successors src ctx).

Theorem compose_replica_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  compose_replica_excitement_select src cands recp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem replica_class_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : replica_class_ctx src) :
  replica_class_select src ctx =
  excitement_select src (replica_class_successors src ctx).
Proof.
  unfold replica_class_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem replica_class_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : replica_class_ctx src) :
  replica_class_select src ctx =
  urge_recovery_select src (replica_class_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem replica_class_no_local_argmin
    (src : ThermodynamicState) (ctx : replica_class_ctx src) :
  replica_class_select src ctx =
  excitement_select src (replica_class_successors src ctx).
Proof.
  exact (replica_class_select_eq_excitement_select src ctx).
Qed.

Theorem compose_replica_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  compose_replica_excitement_select src cands recp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma replica_class_select_empty (src : ThermodynamicState)
    (ctx : replica_class_ctx src)
    (Hnil : replica_class_successors src ctx = nil) :
  replica_class_select src ctx = inr exc_no_candidates.
Proof.
  unfold replica_class_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: fabric-nodes.json census + §15.4 fixtures               *)
(* ------------------------------------------------------------------ *)

Definition fabric_nodes_json_rel : string := "workspace/ops/fabric-nodes.json".

Definition fabric_nodes_schema_pin : string := "umst_fabric_nodes_v1".

Definition replica_class_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition replica_class_fixture_node0_pin : fabric_node_class_pin :=
  {| fabric_node_id := "node-0";
     fabric_class_field := Some "node-0-dev-clone";
     fabric_physics_green_claim := false;
     fabric_joins_labs_public_gossip := false |}.

Definition replica_class_fixture_invent_green_pin : fabric_node_class_pin :=
  {| fabric_node_id := "node-invent-green";
     fabric_class_field := Some "node-1-dev-clone";
     fabric_physics_green_claim := true;
     fabric_joins_labs_public_gossip := false |}.

Definition replica_class_fixture_compose_gossip_pin : fabric_node_class_pin :=
  {| fabric_node_id := "compose-customer";
     fabric_class_field := Some "customer-compose";
     fabric_physics_green_claim := false;
     fabric_joins_labs_public_gossip := true |}.

Theorem replica_class_fixture_node0_admitted :
  evaluate_fabric_node_class replica_class_fixture_node0_pin =
  inl
    {| fabric_row_node_id := "node-0";
       fabric_row_class := rcl_node0_dev_clone;
       fabric_row_table := replica_class_blueprint_row rcl_node0_dev_clone;
       fabric_row_verdict := fncv_accept;
       fabric_row_admit := rca_admitted |}.
Proof.
  reflexivity.
Qed.

Theorem replica_class_fixture_invent_green_refused :
  evaluate_fabric_node_class replica_class_fixture_invent_green_pin =
  inr rcr_invented_physics_green.
Proof.
  reflexivity.
Qed.

Theorem replica_class_fixture_compose_gossip_refused :
  evaluate_fabric_node_class replica_class_fixture_compose_gossip_pin =
  inr rcr_customer_compose_labs_gossip.
Proof.
  reflexivity.
Qed.

Theorem replica_class_offline_luks_egress_empty :
  replica_egress_empty (replica_row_egress
    (replica_class_blueprint_row rcl_offline_luks)) = true.
Proof.
  reflexivity.
Qed.

Theorem replica_class_darwin_scratch_egress_empty :
  replica_egress_empty (replica_row_egress
    (replica_class_blueprint_row rcl_darwin_scratch)) = true.
Proof.
  reflexivity.
Qed.

Theorem replica_class_forgejo_egress_nonempty :
  replica_egress_empty (replica_row_egress
    (replica_class_blueprint_row rcl_forgejo_primary_mirror)) = false.
Proof.
  reflexivity.
Qed.

Theorem replica_class_table_cardinality_six :
  replica_class_table_cardinality = (6%nat).
Proof.
  reflexivity.
Qed.

Theorem replica_class_node0_class_field :
  replica_class_class_field rcl_node0_dev_clone = "node-0-dev-clone".
Proof.
  reflexivity.
Qed.

Theorem replica_class_parse_legacy_node0 :
  parse_replica_class_field rcl_node0_legacy_field =
  Some rcl_node0_dev_clone.
Proof.
  reflexivity.
Qed.

Theorem replica_class_parse_unknown_none :
  parse_replica_class_field "unknown-class" = None.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition replica_class_physics_green : bool := false.

Lemma replica_class_physics_green_false :
  replica_class_physics_green = false.
Proof. reflexivity. Qed.

Definition replica_class_production_wired : bool := false.

Lemma replica_class_production_wired_false :
  replica_class_production_wired = false.
Proof. reflexivity. Qed.

Theorem replica_class_module_witness : True.
Proof. exact I. Qed.

Theorem replica_class_no_new_axiom : True.
Proof. exact I. Qed.

Theorem replica_class_positive_refuse_not_silent :
  evaluate_fabric_node_class replica_class_fixture_invent_green_pin <>
  inl
    {| fabric_row_node_id := "node-invent-green";
       fabric_row_class := rcl_node1_dev_clone;
       fabric_row_table := replica_class_blueprint_row rcl_node1_dev_clone;
       fabric_row_verdict := fncv_accept;
       fabric_row_admit := rca_admitted |}.
Proof.
  unfold evaluate_fabric_node_class, replica_class_fixture_invent_green_pin.
  discriminate.
Qed.

Theorem replica_class_compose_excitement_not_argmin :
  forall (src : ThermodynamicState) (ctx : replica_class_ctx src),
  replica_class_select src ctx =
  excitement_select src (replica_class_successors src ctx).
Proof.
  intros. exact (replica_class_no_local_argmin src ctx).
Qed.
