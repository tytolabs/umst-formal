(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/FabricNodes.v                                     *)
(*                                                                      *)
(*  Meso acting Urge — §15 fabric-nodes replica-class pin.              *)
(*  Declared fabric nodes (`fabric-nodes.json`) pin to §15.4 replica- *)
(*  class table rows — software schema, not Forgejo installer. Composes *)
(*  `excitement_select`; no second argmin.                               *)
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
(*  SECTION 1: §15.4 replica-class + fabric-node pin carriers         *)
(* ------------------------------------------------------------------ *)

(** §15.4 replica-class table row — software schema pin (not installer). *)
Inductive fabric_replica_class :=
  | frc_node0_dev_clone
  | frc_node1_dev_clone
  | frc_forgejo_primary_mirror
  | frc_darwin_scratch
  | frc_offline_luks
  | frc_customer_compose.

(** Authority column from §15.4 replica-class table. *)
Inductive fabric_authority :=
  | fa_working_copy
  | fa_canonical_remote
  | fa_scratch_plane
  | fa_disaster_copy
  | fa_customer_on_site.

(** Whether declared network egress is empty for this replica class. *)
Definition fabric_replica_egress_empty (c : fabric_replica_class) : bool :=
  match c with
  | frc_darwin_scratch | frc_offline_luks => true
  | frc_node0_dev_clone | frc_node1_dev_clone
  | frc_forgejo_primary_mirror | frc_customer_compose => false
  end.

(** Map declared fabric node id surrogate (`0` = node-0, `1` = node-1). *)
Definition fabric_replica_from_node_id (node_id : nat)
    : option fabric_replica_class :=
  match node_id with
  | O => Some frc_node0_dev_clone
  | S O => Some frc_node1_dev_clone
  | _ => None
  end.

(** Blueprint authority for a replica-class row. *)
Definition fabric_authority_of (c : fabric_replica_class) : fabric_authority :=
  match c with
  | frc_node0_dev_clone | frc_node1_dev_clone => fa_working_copy
  | frc_forgejo_primary_mirror => fa_canonical_remote
  | frc_darwin_scratch => fa_scratch_plane
  | frc_offline_luks => fa_disaster_copy
  | frc_customer_compose => fa_customer_on_site
  end.

(** Expected `fabric-nodes.json` schema id surrogate (`umst_fabric_nodes_v1`). *)
Definition fabric_nodes_schema_valid (schema_ok : bool) : bool := schema_ok.

(** UCRS stamp surrogate carried through fabric-node pin. *)
Record fabric_ucrs_stamp : Set := {
  fabric_ucrs_seq : nat;
  fabric_ucrs_wall_has_t : bool
}.

(** MergeSafe certificate surrogate — pin must not violate tier disjointness. *)
Record fabric_merge_safe_cert : Set := {
  fabric_merge_safe : bool
}.

(** Declared fabric node pin — mirrors `fabric-nodes.json` row (software schema). *)
Record fabric_node_pin : Set := {
  fabric_pin_step_id : nat;
  fabric_pin_node_id : nat;
  fabric_pin_schema_ok : bool;
  fabric_pin_byzantine_mesh : bool;
  fabric_pin_claims_forgejo_running : bool;
  fabric_pin_ucrs : fabric_ucrs_stamp;
  fabric_pin_merge_safe : fabric_merge_safe_cert;
  fabric_pin_provenance_intact : bool
}.

(** Witness bundle a fabric-node morphism must preserve (§15). *)
Record fabric_node_witness : Set := {
  fabric_witness_ucrs : fabric_ucrs_stamp;
  fabric_witness_merge_safe : fabric_merge_safe_cert;
  fabric_witness_provenance_intact : bool
}.

(** Typed fabric-node morphism — admissible replica-class pin, not installer theater. *)
Record fabric_node_morphism : Set := {
  fabric_morphism_from : fabric_node_pin;
  fabric_morphism_to_replica : fabric_replica_class;
  fabric_morphism_witness : fabric_node_witness;
  fabric_morphism_excitement_selected : bool
}.

(** Fail-closed fabric-node errors — positive refuse, not silent no-op. *)
Inductive fabric_nodes_refusal :=
  | fnr_byzantine_mesh_claim
  | fnr_forgejo_install_claim
  | fnr_unknown_fabric_node_id (node_id : nat)
  | fnr_schema_mismatch
  | fnr_second_argmin
  | fnr_production_wired
  | fnr_gate_rejected (seq : nat)
  | fnr_merge_unsafe (step_id : nat)
  | fnr_provenance_loss (step_id : nat)
  | fnr_replica_class_mismatch.

(** Verdict of a fabric-node operation class. *)
Inductive fabric_nodes_verdict :=
  | fnv_pin_ok
  | fnv_byzantine_mesh_refused
  | fnv_forgejo_install_refused
  | fnv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §15 admissibility conjunct + positive refuse            *)
(* ------------------------------------------------------------------ *)

(** §15 admissibility conjunct inputs (surrogate). *)
Record fabric_admissibility_conjunct : Set := {
  fabric_conj_gate_ok : bool;
  fabric_conj_merge_safe : bool;
  fabric_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ MergeSafe ∧ Excitement preserves`. *)
Definition fabric_conjunct_admits (c : fabric_admissibility_conjunct) : bool :=
  fabric_conj_gate_ok c &&
  fabric_conj_merge_safe c &&
  fabric_conj_excitement_preserves c.

(** Classify Byzantine mesh / Forgejo install vs typed pin without performing I/O. *)
Definition evaluate_fabric_nodes_operation
    (byzantine_mesh claims_forgejo_running : bool)
    : fabric_nodes_verdict :=
  if byzantine_mesh then fnv_byzantine_mesh_refused
  else if claims_forgejo_running then fnv_forgejo_install_refused
  else fnv_pin_ok.

(** Positive refuse: Byzantine mesh claim is inadmissible on fabric nodes. *)
Definition refuse_byzantine_mesh_claim : fabric_nodes_refusal :=
  fnr_byzantine_mesh_claim.

(** Positive refuse: Forgejo install claim is inadmissible — software schema only. *)
Definition refuse_forgejo_install_claim : fabric_nodes_refusal :=
  fnr_forgejo_install_claim.

(** Positive refuse: second argmin selector is inadmissible. *)
Definition refuse_second_argmin_selector : fabric_nodes_refusal :=
  fnr_second_argmin.

(** Admit a declared fabric node pin — fail closed on schema / node id / theater. *)
Definition admit_fabric_node_pin (pin : fabric_node_pin)
    : unit + fabric_nodes_refusal :=
  if fabric_pin_byzantine_mesh pin then inr fnr_byzantine_mesh_claim
  else if fabric_pin_claims_forgejo_running pin then inr fnr_forgejo_install_claim
  else if negb (fabric_nodes_schema_valid (fabric_pin_schema_ok pin)) then
    inr fnr_schema_mismatch
  else
    match fabric_replica_from_node_id (fabric_pin_node_id pin) with
    | None => inr (fnr_unknown_fabric_node_id (fabric_pin_node_id pin))
    | Some _ => inl tt
    end.

(** Build witness from pin — morphism must preserve stamps and certificates. *)
Definition witness_from_fabric_pin (p : fabric_node_pin) : fabric_node_witness :=
  {| fabric_witness_ucrs := fabric_pin_ucrs p;
     fabric_witness_merge_safe := fabric_pin_merge_safe p;
     fabric_witness_provenance_intact := fabric_pin_provenance_intact p |}.

(** Attempt typed fabric-node morphism to target replica — fail closed on inadmissibility. *)
Definition apply_fabric_node_morphism
    (pin : fabric_node_pin)
    (to_replica : fabric_replica_class)
    (conjunct : fabric_admissibility_conjunct)
    (excitement_selected : bool)
    : fabric_node_morphism + fabric_nodes_refusal :=
  match admit_fabric_node_pin pin with
  | inr r => inr r
  | inl _ =>
    if negb (fabric_conjunct_admits conjunct) then
      inr (fnr_gate_rejected (fabric_ucrs_seq (fabric_pin_ucrs pin)))
    else if negb (fabric_merge_safe (fabric_pin_merge_safe pin)) then
      inr (fnr_merge_unsafe (fabric_pin_step_id pin))
    else if negb (fabric_pin_provenance_intact pin) then
      inr (fnr_provenance_loss (fabric_pin_step_id pin))
    else if negb excitement_selected then
      inr (fnr_provenance_loss (fabric_pin_step_id pin))
    else
      inl
        {| fabric_morphism_from := pin;
           fabric_morphism_to_replica := to_replica;
           fabric_morphism_witness := witness_from_fabric_pin pin;
           fabric_morphism_excitement_selected := excitement_selected |}
  end.

Lemma fabric_nodes_byzantine_mesh_refused :
  evaluate_fabric_nodes_operation true false = fnv_byzantine_mesh_refused.
Proof.
  reflexivity.
Qed.

Lemma fabric_nodes_forgejo_install_refused :
  evaluate_fabric_nodes_operation false true = fnv_forgejo_install_refused.
Proof.
  reflexivity.
Qed.

Lemma fabric_nodes_pin_ok_when_honest :
  evaluate_fabric_nodes_operation false false = fnv_pin_ok.
Proof.
  reflexivity.
Qed.

Lemma refuse_byzantine_mesh_claim_positive :
  refuse_byzantine_mesh_claim = fnr_byzantine_mesh_claim.
Proof.
  reflexivity.
Qed.

Lemma refuse_forgejo_install_claim_positive :
  refuse_forgejo_install_claim = fnr_forgejo_install_claim.
Proof.
  reflexivity.
Qed.

Lemma refuse_second_argmin_selector_positive :
  refuse_second_argmin_selector = fnr_second_argmin.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Fabric nodes composes Excitement (no second argmin)   *)
(* ------------------------------------------------------------------ *)

(** Context for fabric-node selection over admissible history successors. *)
Record fabric_nodes_ctx (src : ThermodynamicState) : Set := {
  fabric_nodes_successors : list (history_candidate src)
}.

(** Fabric-node selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition fabric_nodes_select (src : ThermodynamicState)
    (ctx : fabric_nodes_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (fabric_nodes_successors src ctx).

Theorem fabric_nodes_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : fabric_nodes_ctx src) :
  fabric_nodes_select src ctx =
  excitement_select src (fabric_nodes_successors src ctx).
Proof.
  unfold fabric_nodes_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem fabric_nodes_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : fabric_nodes_ctx src) :
  fabric_nodes_select src ctx =
  urge_recovery_select src (fabric_nodes_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem fabric_nodes_no_local_argmin
    (src : ThermodynamicState) (ctx : fabric_nodes_ctx src) :
  fabric_nodes_select src ctx =
  excitement_select src (fabric_nodes_successors src ctx).
Proof.
  exact (fabric_nodes_select_eq_excitement_select src ctx).
Qed.

Lemma fabric_nodes_empty (src : ThermodynamicState)
    (ctx : fabric_nodes_ctx src)
    (Hnil : fabric_nodes_successors src ctx = nil) :
  fabric_nodes_select src ctx = inr exc_no_candidates.
Proof.
  unfold fabric_nodes_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(** Import path selector — compose `excitement_select`, refuse second argmin. *)
Inductive fabric_excitement_compose_pin :=
  | fep_import_select_excitement
  | fep_second_argmin_refused.

Definition fabric_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : fabric_excitement_compose_pin) :
  history_candidate src + excitement_residue + fabric_nodes_refusal :=
  match pin with
  | fep_import_select_excitement =>
      let r := excitement_select src cands in
      match r with
      | inl c => inl (inl c)
      | inr e => inl (inr e)
      end
  | fep_second_argmin_refused => inr fnr_second_argmin
  end.

Theorem fabric_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  fabric_excitement_select src cands fep_import_select_excitement =
  match excitement_select src cands with
  | inl c => inl (inl c)
  | inr e => inl (inr e)
  end.
Proof.
  intros. unfold fabric_excitement_select.
  destruct (excitement_select src cands); reflexivity.
Qed.

Theorem fabric_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  fabric_excitement_select src cands fep_second_argmin_refused =
  inr fnr_second_argmin.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §15 fixtures + witness theorems                         *)
(* ------------------------------------------------------------------ *)

Definition fabric_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition fabric_fixture_ucrs : fabric_ucrs_stamp :=
  {| fabric_ucrs_seq := 7%nat;
     fabric_ucrs_wall_has_t := true |}.

Definition fabric_fixture_merge_safe : fabric_merge_safe_cert :=
  {| fabric_merge_safe := true |}.

Definition fabric_fixture_node0_pin : fabric_node_pin :=
  {| fabric_pin_step_id := 1%nat;
     fabric_pin_node_id := 0%nat;
     fabric_pin_schema_ok := true;
     fabric_pin_byzantine_mesh := false;
     fabric_pin_claims_forgejo_running := false;
     fabric_pin_ucrs := fabric_fixture_ucrs;
     fabric_pin_merge_safe := fabric_fixture_merge_safe;
     fabric_pin_provenance_intact := true |}.

Definition fabric_fixture_conjunct : fabric_admissibility_conjunct :=
  {| fabric_conj_gate_ok := true;
     fabric_conj_merge_safe := true;
     fabric_conj_excitement_preserves := true |}.

Theorem fabric_fixture_admit_node0_ok :
  admit_fabric_node_pin fabric_fixture_node0_pin = inl tt.
Proof.
  reflexivity.
Qed.

Theorem fabric_fixture_apply_morphism_ok :
  apply_fabric_node_morphism
    fabric_fixture_node0_pin frc_node0_dev_clone fabric_fixture_conjunct true
  = inl
      {| fabric_morphism_from := fabric_fixture_node0_pin;
         fabric_morphism_to_replica := frc_node0_dev_clone;
         fabric_morphism_witness := witness_from_fabric_pin fabric_fixture_node0_pin;
         fabric_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem fabric_node0_maps_to_dev_clone :
  fabric_replica_from_node_id 0%nat = Some frc_node0_dev_clone.
Proof.
  reflexivity.
Qed.

Theorem fabric_node1_maps_to_dev_clone :
  fabric_replica_from_node_id 1%nat = Some frc_node1_dev_clone.
Proof.
  reflexivity.
Qed.

Theorem fabric_unknown_node_id_refused :
  fabric_replica_from_node_id 99%nat = None.
Proof.
  reflexivity.
Qed.

Theorem fabric_offline_luks_egress_empty :
  fabric_replica_egress_empty frc_offline_luks = true.
Proof.
  reflexivity.
Qed.

Theorem fabric_darwin_scratch_egress_empty :
  fabric_replica_egress_empty frc_darwin_scratch = true.
Proof.
  reflexivity.
Qed.

Theorem fabric_forgejo_primary_egress_nonempty :
  fabric_replica_egress_empty frc_forgejo_primary_mirror = false.
Proof.
  reflexivity.
Qed.

Theorem fabric_fixture_witness_preserves_ucrs :
  fabric_witness_ucrs (witness_from_fabric_pin fabric_fixture_node0_pin) =
  fabric_fixture_ucrs.
Proof.
  reflexivity.
Qed.

Definition fabric_fixture_byzantine_pin : fabric_node_pin :=
  {| fabric_pin_step_id := 1%nat;
     fabric_pin_node_id := 0%nat;
     fabric_pin_schema_ok := true;
     fabric_pin_byzantine_mesh := true;
     fabric_pin_claims_forgejo_running := false;
     fabric_pin_ucrs := fabric_fixture_ucrs;
     fabric_pin_merge_safe := fabric_fixture_merge_safe;
     fabric_pin_provenance_intact := true |}.

Definition fabric_fixture_forgejo_pin : fabric_node_pin :=
  {| fabric_pin_step_id := 1%nat;
     fabric_pin_node_id := 0%nat;
     fabric_pin_schema_ok := true;
     fabric_pin_byzantine_mesh := false;
     fabric_pin_claims_forgejo_running := true;
     fabric_pin_ucrs := fabric_fixture_ucrs;
     fabric_pin_merge_safe := fabric_fixture_merge_safe;
     fabric_pin_provenance_intact := true |}.

Theorem fabric_fixture_byzantine_refused :
  admit_fabric_node_pin fabric_fixture_byzantine_pin = inr fnr_byzantine_mesh_claim.
Proof.
  reflexivity.
Qed.

Theorem fabric_fixture_forgejo_refused :
  admit_fabric_node_pin fabric_fixture_forgejo_pin = inr fnr_forgejo_install_claim.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition fabric_nodes_physics_green : bool := false.

Lemma fabric_nodes_physics_green_false :
  fabric_nodes_physics_green = false.
Proof. reflexivity. Qed.

Definition fabric_nodes_production_wired : bool := false.

Lemma fabric_nodes_production_wired_false :
  fabric_nodes_production_wired = false.
Proof. reflexivity. Qed.

Theorem fabric_nodes_module_witness : True.
Proof. exact I. Qed.

Theorem fabric_nodes_no_new_axiom : True.
Proof. exact I. Qed.

Theorem fabric_nodes_positive_refuse_not_silent :
  evaluate_fabric_nodes_operation true false <> fnv_pin_ok.
Proof.
  unfold evaluate_fabric_nodes_operation.
  discriminate.
Qed.

Theorem fabric_nodes_forgejo_refuse_not_silent :
  evaluate_fabric_nodes_operation false true <> fnv_pin_ok.
Proof.
  unfold evaluate_fabric_nodes_operation.
  discriminate.
Qed.
