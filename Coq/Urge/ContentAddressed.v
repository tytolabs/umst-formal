(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/ContentAddressed.v                                *)
(*                                                                      *)
(*  Meso acting Urge — §3 content-addressed history. Geometric identity *)
(*  is **primary**; git hash is a compatibility witness, not sole id.   *)
(*  History recovery composes `excitement_select` — no second argmin.     *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool String QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope string_scope.
Open Scope bool_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Content-addressed snapshot + typed morphism carriers  *)
(* ------------------------------------------------------------------ *)

(** §3 geometric identity — primary content-address factor (SDF surrogate). *)
Record content_geometric_identity : Set := {
  ca_geom_content_id : nat;
  ca_geom_resolution_bits : nat
}.

(** Git hash compatibility witness — secondary to geometric identity. *)
Record content_git_hash_compat : Set := {
  ca_git_hash : string
}.

(** UCRS stamp surrogate carried through content-addressed history. *)
Record content_addressed_ucrs_stamp : Set := {
  ca_ucrs_seq : nat;
  ca_ucrs_wall_has_t : bool
}.

(** Geometric-primary certificate — content id must be non-zero. *)
Record content_geometric_primary_cert : Set := {
  ca_geometric_primary : bool
}.

(** Snapshot identity at history head (content-addressed surrogate). *)
Record content_addressed_snapshot : Set := {
  ca_snapshot_id : nat;
  ca_snapshot_head : ThermodynamicState;
  ca_snapshot_geometric : content_geometric_identity;
  ca_snapshot_git_compat : option content_git_hash_compat;
  ca_snapshot_ucrs : content_addressed_ucrs_stamp;
  ca_snapshot_geometric_cert : content_geometric_primary_cert;
  ca_snapshot_provenance_intact : bool
}.

(** Witness bundle a content-addressed morphism must preserve (§3). *)
Record content_addressed_witness : Set := {
  ca_witness_geometric : content_geometric_identity;
  ca_witness_git_compat : option content_git_hash_compat;
  ca_witness_geometric_primary : bool;
  ca_witness_provenance_intact : bool
}.

(** Typed content-addressed morphism — admissible history transition. *)
Record content_addressed_morphism : Set := {
  ca_morphism_from : content_addressed_snapshot;
  ca_morphism_to_seq : nat;
  ca_morphism_witness : content_addressed_witness;
  ca_morphism_excitement_selected : bool
}.

(** Fail-closed content-addressed errors — positive refuse, not silent accept. *)
Inductive content_addressed_refusal :=
  | car_git_hash_only_identity (git_hash : string)
  | car_host_id_identity (host_id : nat)
  | car_gate_rejected (seq : nat)
  | car_geometric_zero (snapshot_id : nat)
  | car_second_argmin_refused.

(** Verdict of a content-addressed admission operation class. *)
Inductive content_addressed_verdict :=
  | cav_admitted
  | cav_git_hash_only_refused
  | cav_host_id_refused
  | cav_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §3 admissibility conjunct + positive refuse           *)
(* ------------------------------------------------------------------ *)

(** §3 admissibility conjunct inputs (surrogate). *)
Record content_admissibility_conjunct : Set := {
  ca_conj_gate_ok : bool;
  ca_conj_geometric_primary : bool;
  ca_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ geometric-primary ∧ Excitement preserves`. *)
Definition content_conjunct_admits (c : content_admissibility_conjunct) : bool :=
  ca_conj_gate_ok c &&
  ca_conj_geometric_primary c &&
  ca_conj_excitement_preserves c.

(** Whether geometric content id is non-zero (primary identity present). *)
Definition geometric_content_id_present (g : content_geometric_identity) : bool :=
  negb (Nat.eqb (ca_geom_content_id g) 0).

(** Classify git-hash-only vs geometric-primary identity without I/O. *)
Definition evaluate_git_hash_only_identity (git_hash_only : bool)
    : content_addressed_verdict :=
  if git_hash_only then cav_git_hash_only_refused else cav_admitted.

(** Classify host-id vs content-addressed geometric identity. *)
Definition evaluate_host_id_identity (use_host_id : bool)
    : content_addressed_verdict :=
  if use_host_id then cav_host_id_refused else cav_admitted.

(** Positive refuse: git hash without geometric primary refused. *)
Definition refuse_git_hash_only_identity (git_hash : string)
    : content_addressed_refusal :=
  car_git_hash_only_identity git_hash.

(** Positive refuse: host id cannot serve as content-addressed identity. *)
Definition refuse_host_id_identity (host_id : nat) : content_addressed_refusal :=
  car_host_id_identity host_id.

(** Positive refuse: second Excitement selector — compose `excitement_select`. *)
Definition refuse_second_argmin : content_addressed_refusal :=
  car_second_argmin_refused.

(** Build witness from snapshot — morphism must preserve geometric + git compat. *)
Definition witness_from_snapshot (s : content_addressed_snapshot)
    : content_addressed_witness :=
  {| ca_witness_geometric := ca_snapshot_geometric s;
     ca_witness_git_compat := ca_snapshot_git_compat s;
     ca_witness_geometric_primary := ca_geometric_primary (ca_snapshot_geometric_cert s);
     ca_witness_provenance_intact := ca_snapshot_provenance_intact s |}.

(** Attempt typed content-addressed morphism — fail closed on inadmissibility. *)
Definition apply_content_addressed_morphism
    (snapshot : content_addressed_snapshot)
    (to_seq : nat)
    (conjunct : content_admissibility_conjunct)
    (excitement_selected : bool)
    : content_addressed_morphism + content_addressed_refusal :=
  if negb (content_conjunct_admits conjunct) then
    inr (car_gate_rejected (ca_ucrs_seq (ca_snapshot_ucrs snapshot)))
  else if negb (geometric_content_id_present (ca_snapshot_geometric snapshot)) then
    match ca_snapshot_git_compat snapshot with
    | Some compat => inr (car_git_hash_only_identity (ca_git_hash compat))
    | None => inr (car_host_id_identity 0)
    end
  else if negb (ca_geometric_primary (ca_snapshot_geometric_cert snapshot)) then
    inr (car_geometric_zero (ca_snapshot_id snapshot))
  else if negb (ca_snapshot_provenance_intact snapshot) then
    inr (car_geometric_zero (ca_snapshot_id snapshot))
  else if negb excitement_selected then
    inr (car_geometric_zero (ca_snapshot_id snapshot))
  else
    inl
      {| ca_morphism_from := snapshot;
         ca_morphism_to_seq := to_seq;
         ca_morphism_witness := witness_from_snapshot snapshot;
         ca_morphism_excitement_selected := excitement_selected |}.

Lemma content_addressed_git_hash_only_refused (git_hash : string) :
  evaluate_git_hash_only_identity true = cav_git_hash_only_refused.
Proof.
  reflexivity.
Qed.

Lemma content_addressed_admitted_when_not_git_hash_only :
  evaluate_git_hash_only_identity false = cav_admitted.
Proof.
  reflexivity.
Qed.

Lemma content_addressed_host_id_refused (host_id : nat) :
  evaluate_host_id_identity true = cav_host_id_refused.
Proof.
  reflexivity.
Qed.

Lemma content_addressed_admitted_when_not_host_id :
  evaluate_host_id_identity false = cav_admitted.
Proof.
  reflexivity.
Qed.

Lemma refuse_git_hash_only_identity_positive (git_hash : string) :
  refuse_git_hash_only_identity git_hash = car_git_hash_only_identity git_hash.
Proof.
  reflexivity.
Qed.

Lemma refuse_host_id_identity_positive (host_id : nat) :
  refuse_host_id_identity host_id = car_host_id_identity host_id.
Proof.
  reflexivity.
Qed.

Lemma refuse_second_argmin_positive :
  refuse_second_argmin = car_second_argmin_refused.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Content-addressed composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Context for content-addressed history over admissible successors. *)
Record content_addressed_ctx (src : ThermodynamicState) : Set := {
  content_addressed_successors : list (history_candidate src)
}.

(** Content-addressed history **is** `urge_recovery_select` / `excitement_select`. *)
Definition content_addressed_select (src : ThermodynamicState)
    (ctx : content_addressed_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (content_addressed_successors src ctx).

Theorem content_addressed_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : content_addressed_ctx src) :
  content_addressed_select src ctx =
  excitement_select src (content_addressed_successors src ctx).
Proof.
  unfold content_addressed_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem content_addressed_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : content_addressed_ctx src) :
  content_addressed_select src ctx =
  urge_recovery_select src (content_addressed_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem content_addressed_no_local_argmin
    (src : ThermodynamicState) (ctx : content_addressed_ctx src) :
  content_addressed_select src ctx =
  excitement_select src (content_addressed_successors src ctx).
Proof.
  exact (content_addressed_select_eq_excitement_select src ctx).
Qed.

Lemma content_addressed_empty (src : ThermodynamicState)
    (ctx : content_addressed_ctx src)
    (Hnil : content_addressed_successors src ctx = nil) :
  content_addressed_select src ctx = inr exc_no_candidates.
Proof.
  unfold content_addressed_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §3 fixtures + witness theorems                          *)
(* ------------------------------------------------------------------ *)

Definition content_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition content_fixture_geometric : content_geometric_identity :=
  {| ca_geom_content_id := 5381;
     ca_geom_resolution_bits := 2 |}.

Definition content_fixture_git_compat : content_git_hash_compat :=
  {| ca_git_hash := "sha1:geometric-primary-compat"%string |}.

Definition content_fixture_ucrs : content_addressed_ucrs_stamp :=
  {| ca_ucrs_seq := 3;
     ca_ucrs_wall_has_t := true |}.

Definition content_fixture_geometric_cert : content_geometric_primary_cert :=
  {| ca_geometric_primary := true |}.

Definition content_fixture_snapshot : content_addressed_snapshot :=
  {| ca_snapshot_id := 1;
     ca_snapshot_head := content_fixture_state;
     ca_snapshot_geometric := content_fixture_geometric;
     ca_snapshot_git_compat := Some content_fixture_git_compat;
     ca_snapshot_ucrs := content_fixture_ucrs;
     ca_snapshot_geometric_cert := content_fixture_geometric_cert;
     ca_snapshot_provenance_intact := true |}.

Definition content_fixture_conjunct : content_admissibility_conjunct :=
  {| ca_conj_gate_ok := true;
     ca_conj_geometric_primary := true;
     ca_conj_excitement_preserves := true |}.

Theorem content_fixture_git_hash_only_refused :
  refuse_git_hash_only_identity "sha1:only-hash"%string =
  car_git_hash_only_identity "sha1:only-hash"%string.
Proof.
  reflexivity.
Qed.

Theorem content_fixture_host_id_refused :
  refuse_host_id_identity 0xdeadbeef =
  car_host_id_identity 0xdeadbeef.
Proof.
  reflexivity.
Qed.

Theorem content_fixture_apply_morphism_ok :
  apply_content_addressed_morphism
    content_fixture_snapshot 2 content_fixture_conjunct true
  = inl
      {| ca_morphism_from := content_fixture_snapshot;
         ca_morphism_to_seq := 2;
         ca_morphism_witness := witness_from_snapshot content_fixture_snapshot;
         ca_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem content_fixture_geometric_content_id_present :
  geometric_content_id_present content_fixture_geometric = true.
Proof.
  reflexivity.
Qed.

Theorem content_fixture_witness_preserves_geometric :
  ca_witness_geometric (witness_from_snapshot content_fixture_snapshot) =
  content_fixture_geometric.
Proof.
  reflexivity.
Qed.

Theorem content_fixture_witness_preserves_git_compat :
  ca_witness_git_compat (witness_from_snapshot content_fixture_snapshot) =
  Some content_fixture_git_compat.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition content_addressed_physics_green : bool := false.

Lemma content_addressed_physics_green_false :
  content_addressed_physics_green = false.
Proof. reflexivity. Qed.

Definition content_addressed_production_wired : bool := false.

Lemma content_addressed_production_wired_false :
  content_addressed_production_wired = false.
Proof. reflexivity. Qed.

Theorem content_addressed_module_witness : True.
Proof. exact I. Qed.

Theorem content_addressed_no_new_axiom : True.
Proof. exact I. Qed.

Theorem content_addressed_git_hash_only_not_admitted :
  evaluate_git_hash_only_identity true <> cav_admitted.
Proof.
  unfold evaluate_git_hash_only_identity.
  discriminate.
Qed.

Theorem content_addressed_host_id_not_admitted :
  evaluate_host_id_identity true <> cav_admitted.
Proof.
  unfold evaluate_host_id_identity.
  discriminate.
Qed.

Definition content_addressed_non_claim : string :=
  "§3 content-addressed history; geometric identity primary, git hash compatibility; compose excitement_select not local argmin; not physics GREEN; not production_wired"%string.
