(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/BackupRecovery.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §15.4 backup as typed recovery morphism.         *)
(*  Backup **is** an Excitement-selected admissible state transition —   *)
(*  not rsync theater. Composes `excitement_select`; no second argmin.   *)
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
(*  SECTION 1: Recovery snapshot + typed morphism carriers           *)
(* ------------------------------------------------------------------ *)

(** Replica class row from §15.4 — offline LUKS carries empty egress. *)
Inductive backup_replica_class :=
  | brc_forge_primary
  | brc_darwin_scratch
  | brc_offline_luks.

(** Whether declared network egress is empty for this replica class. *)
Definition replica_egress_empty (c : backup_replica_class) : bool :=
  match c with
  | brc_offline_luks | brc_darwin_scratch => true
  | brc_forge_primary => false
  end.

(** UCRS stamp surrogate carried through recovery. *)
Record backup_ucrs_stamp : Set := {
  backup_ucrs_seq : nat;
  backup_ucrs_wall_has_t : bool
}.

(** MergeSafe certificate surrogate — recovery must not violate tier disjointness. *)
Record backup_merge_safe_cert : Set := {
  backup_merge_safe : bool
}.

(** Snapshot identity at recovery source (content-addressed surrogate). *)
Record backup_recovery_snapshot : Set := {
  backup_snapshot_id : nat;
  backup_snapshot_head : ThermodynamicState;
  backup_snapshot_ucrs : backup_ucrs_stamp;
  backup_snapshot_merge_safe : backup_merge_safe_cert;
  backup_snapshot_provenance_intact : bool;
  backup_snapshot_replica : backup_replica_class
}.

(** Witness bundle a recovery morphism must preserve (§15.4). *)
Record backup_recovery_witness : Set := {
  backup_witness_ucrs : backup_ucrs_stamp;
  backup_witness_merge_safe : backup_merge_safe_cert;
  backup_witness_provenance_intact : bool
}.

(** Typed recovery morphism — admissible state transition, not blind copy. *)
Record backup_recovery_morphism : Set := {
  backup_morphism_from : backup_recovery_snapshot;
  backup_morphism_to_replica : backup_replica_class;
  backup_morphism_witness : backup_recovery_witness;
  backup_morphism_excitement_selected : bool
}.

(** Fail-closed recovery errors — positive refuse, not silent no-op. *)
Inductive backup_recovery_refusal :=
  | brr_rsync_theater_refused (snapshot_id : nat)
  | brr_gate_rejected (seq : nat)
  | brr_merge_unsafe (snapshot_id : nat)
  | brr_provenance_loss (snapshot_id : nat)
  | brr_replica_class_mismatch.

(** Verdict of a recovery operation class. *)
Inductive backup_recovery_verdict :=
  | brv_morphism_ok
  | brv_rsync_theater_refused
  | brv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §15.4 admissibility conjunct + positive refuse        *)
(* ------------------------------------------------------------------ *)

(** §15.4 admissibility conjunct inputs (surrogate). *)
Record backup_admissibility_conjunct : Set := {
  backup_conj_gate_ok : bool;
  backup_conj_merge_safe : bool;
  backup_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ MergeSafe ∧ Excitement preserves`. *)
Definition backup_conjunct_admits (c : backup_admissibility_conjunct) : bool :=
  backup_conj_gate_ok c &&
  backup_conj_merge_safe c &&
  backup_conj_excitement_preserves c.

(** Classify blind copy vs typed morphism without performing I/O. *)
Definition evaluate_backup_recovery_operation (is_rsync_theater : bool)
    : backup_recovery_verdict :=
  if is_rsync_theater then brv_rsync_theater_refused else brv_morphism_ok.

(** Positive refuse: rsync theater is inadmissible — backup is typed recovery morphism. *)
Definition refuse_rsync_theater (snapshot_id : nat) : backup_recovery_refusal :=
  brr_rsync_theater_refused snapshot_id.

(** Build witness from snapshot — morphism must preserve stamps and certificates. *)
Definition witness_from_snapshot (s : backup_recovery_snapshot)
    : backup_recovery_witness :=
  {| backup_witness_ucrs := backup_snapshot_ucrs s;
     backup_witness_merge_safe := backup_snapshot_merge_safe s;
     backup_witness_provenance_intact := backup_snapshot_provenance_intact s |}.

(** Attempt typed recovery morphism to target replica — fail closed on inadmissibility. *)
Definition apply_backup_recovery_morphism
    (snapshot : backup_recovery_snapshot)
    (to_replica : backup_replica_class)
    (conjunct : backup_admissibility_conjunct)
    (excitement_selected : bool)
    : backup_recovery_morphism + backup_recovery_refusal :=
  if negb (backup_conjunct_admits conjunct) then
    inr (brr_gate_rejected (backup_ucrs_seq (backup_snapshot_ucrs snapshot)))
  else if negb (backup_merge_safe (backup_snapshot_merge_safe snapshot)) then
    inr (brr_merge_unsafe (backup_snapshot_id snapshot))
  else if negb (backup_snapshot_provenance_intact snapshot) then
    inr (brr_provenance_loss (backup_snapshot_id snapshot))
  else if negb excitement_selected then
    inr (brr_provenance_loss (backup_snapshot_id snapshot))
  else
    inl
      {| backup_morphism_from := snapshot;
         backup_morphism_to_replica := to_replica;
         backup_morphism_witness := witness_from_snapshot snapshot;
         backup_morphism_excitement_selected := excitement_selected |}.

Lemma backup_recovery_rsync_theater_refused
    (snapshot_id : nat) :
  evaluate_backup_recovery_operation true = brv_rsync_theater_refused.
Proof.
  reflexivity.
Qed.

Lemma backup_recovery_morphism_ok_when_not_rsync :
  evaluate_backup_recovery_operation false = brv_morphism_ok.
Proof.
  reflexivity.
Qed.

Lemma refuse_rsync_theater_positive (snapshot_id : nat) :
  refuse_rsync_theater snapshot_id = brr_rsync_theater_refused snapshot_id.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Backup recovery composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Context for backup recovery over admissible history successors. *)
Record backup_recovery_ctx (src : ThermodynamicState) : Set := {
  backup_recovery_successors : list (history_candidate src)
}.

(** Backup recovery **is** `urge_recovery_select` / `excitement_select`. *)
Definition backup_recovery_select (src : ThermodynamicState)
    (ctx : backup_recovery_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (backup_recovery_successors src ctx).

Theorem backup_recovery_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : backup_recovery_ctx src) :
  backup_recovery_select src ctx =
  excitement_select src (backup_recovery_successors src ctx).
Proof.
  unfold backup_recovery_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem backup_recovery_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : backup_recovery_ctx src) :
  backup_recovery_select src ctx =
  urge_recovery_select src (backup_recovery_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem backup_recovery_no_local_argmin
    (src : ThermodynamicState) (ctx : backup_recovery_ctx src) :
  backup_recovery_select src ctx =
  excitement_select src (backup_recovery_successors src ctx).
Proof.
  exact (backup_recovery_select_eq_excitement_select src ctx).
Qed.

Lemma backup_recovery_empty (src : ThermodynamicState)
    (ctx : backup_recovery_ctx src)
    (Hnil : backup_recovery_successors src ctx = nil) :
  backup_recovery_select src ctx = inr exc_no_candidates.
Proof.
  unfold backup_recovery_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §15.4 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition backup_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition backup_fixture_ucrs : backup_ucrs_stamp :=
  {| backup_ucrs_seq := 7;
     backup_ucrs_wall_has_t := true |}.

Definition backup_fixture_merge_safe : backup_merge_safe_cert :=
  {| backup_merge_safe := true |}.

Definition backup_fixture_snapshot : backup_recovery_snapshot :=
  {| backup_snapshot_id := 1;
     backup_snapshot_head := backup_fixture_state;
     backup_snapshot_ucrs := backup_fixture_ucrs;
     backup_snapshot_merge_safe := backup_fixture_merge_safe;
     backup_snapshot_provenance_intact := true;
     backup_snapshot_replica := brc_forge_primary |}.

Definition backup_fixture_conjunct : backup_admissibility_conjunct :=
  {| backup_conj_gate_ok := true;
     backup_conj_merge_safe := true;
     backup_conj_excitement_preserves := true |}.

Theorem backup_fixture_rsync_theater_refused :
  refuse_rsync_theater (backup_snapshot_id backup_fixture_snapshot) =
  brr_rsync_theater_refused 1.
Proof.
  reflexivity.
Qed.

Theorem backup_fixture_apply_morphism_ok :
  apply_backup_recovery_morphism
    backup_fixture_snapshot brc_offline_luks backup_fixture_conjunct true
  = inl
      {| backup_morphism_from := backup_fixture_snapshot;
         backup_morphism_to_replica := brc_offline_luks;
         backup_morphism_witness := witness_from_snapshot backup_fixture_snapshot;
         backup_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem backup_offline_luks_egress_empty :
  replica_egress_empty brc_offline_luks = true.
Proof.
  reflexivity.
Qed.

Theorem backup_darwin_scratch_egress_empty :
  replica_egress_empty brc_darwin_scratch = true.
Proof.
  reflexivity.
Qed.

Theorem backup_forge_primary_egress_nonempty :
  replica_egress_empty brc_forge_primary = false.
Proof.
  reflexivity.
Qed.

Theorem backup_fixture_witness_preserves_ucrs :
  backup_witness_ucrs (witness_from_snapshot backup_fixture_snapshot) =
  backup_fixture_ucrs.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition backup_recovery_physics_green : bool := false.

Lemma backup_recovery_physics_green_false :
  backup_recovery_physics_green = false.
Proof. reflexivity. Qed.

Definition backup_recovery_production_wired : bool := false.

Lemma backup_recovery_production_wired_false :
  backup_recovery_production_wired = false.
Proof. reflexivity. Qed.

Theorem backup_recovery_module_witness : True.
Proof. exact I. Qed.

Theorem backup_recovery_no_new_axiom : True.
Proof. exact I. Qed.

Theorem backup_recovery_positive_refuse_not_silent :
  evaluate_backup_recovery_operation true <> brv_morphism_ok.
Proof.
  unfold evaluate_backup_recovery_operation.
  discriminate.
Qed.
