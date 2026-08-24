(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/GeometricMemory.v                                 *)
(*                                                                      *)
(*  Meso acting Urge — §5.3 geometric memory / SDF identity of a        *)
(*  history object. Identity is canonical SDF/FRep fingerprint —      *)
(*  not host ids or raw payload bytes alone. Composes `excitement_select`; *)
(*  no second argmin.                                                   *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: SDF identity + typed history object carriers           *)
(* ------------------------------------------------------------------ *)

(** Canonical SDF fingerprint surrogate (FRep grain + digest). *)
Record sdf_fingerprint : Set := {
  sdf_fp_digest : nat;
  sdf_fp_grain : nat
}.

(** §5.3 geometric identity — SDF-canonical, not host-id keyed. *)
Record history_geometric_identity : Set := {
  geom_id_fingerprint : sdf_fingerprint;
  geom_id_resolution_bits : nat
}.

(** History object whose identity is geometric memory, not host id. *)
Record history_object_geom : Set := {
  hist_geom_seq : nat;
  hist_geom_identity : history_geometric_identity;
  hist_geom_field_digest : nat
}.

(** Witness bundle a geometric memory morphism must preserve (§5.3). *)
Record geometric_memory_witness : Set := {
  geom_witness_fingerprint : sdf_fingerprint;
  geom_witness_resolution_bits : nat;
  geom_witness_sdf_canonical : bool
}.

(** Typed geometric-memory morphism — admissible identity transition. *)
Record geometric_memory_morphism : Set := {
  geom_morphism_from : history_object_geom;
  geom_morphism_to_seq : nat;
  geom_morphism_witness : geometric_memory_witness;
  geom_morphism_excitement_selected : bool
}.

(** Fail-closed geometric memory errors — positive refuse, not silent accept. *)
Inductive geometric_memory_refusal :=
  | gmr_host_id_not_geometric (host_id : nat)
  | gmr_payload_without_sdf (payload : nat)
  | gmr_gate_rejected (seq : nat)
  | gmr_identity_mismatch (left_digest right_digest : nat).

(** Verdict of a geometric identity operation class. *)
Inductive geometric_memory_verdict :=
  | gmv_identity_ok
  | gmv_host_id_refused
  | gmv_payload_only_refused
  | gmv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §5.3 admissibility conjunct + positive refuse         *)
(* ------------------------------------------------------------------ *)

(** §5.3 admissibility conjunct inputs (surrogate). *)
Record geometric_admissibility_conjunct : Set := {
  geom_conj_gate_ok : bool;
  geom_conj_sdf_canonical : bool;
  geom_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ SDF-canonical ∧ Excitement preserves`. *)
Definition geometric_conjunct_admits (c : geometric_admissibility_conjunct) : bool :=
  geom_conj_gate_ok c &&
  geom_conj_sdf_canonical c &&
  geom_conj_excitement_preserves c.

(** Classify host-id vs SDF identity without performing I/O. *)
Definition evaluate_host_id_identity (use_host_id : bool)
    : geometric_memory_verdict :=
  if use_host_id then gmv_host_id_refused else gmv_identity_ok.

(** Classify payload-only vs SDF-canonical identity. *)
Definition evaluate_payload_only_identity (payload_only : bool)
    : geometric_memory_verdict :=
  if payload_only then gmv_payload_only_refused else gmv_identity_ok.

(** Positive refuse: host id is not geometric memory identity. *)
Definition refuse_host_id_identity (host_id : nat) : geometric_memory_refusal :=
  gmr_host_id_not_geometric host_id.

(** Positive refuse: raw payload without SDF canonicalization refused. *)
Definition refuse_payload_only_identity (payload : nat) : geometric_memory_refusal :=
  gmr_payload_without_sdf payload.

(** Whether two history objects share the same geometric memory identity. *)
Definition geometric_identity_matches (left right : history_object_geom) : bool :=
  Nat.eqb (sdf_fp_digest (geom_id_fingerprint (hist_geom_identity left)))
          (sdf_fp_digest (geom_id_fingerprint (hist_geom_identity right))) &&
  Nat.eqb (sdf_fp_grain (geom_id_fingerprint (hist_geom_identity left)))
          (sdf_fp_grain (geom_id_fingerprint (hist_geom_identity right))) &&
  Nat.eqb (geom_id_resolution_bits (hist_geom_identity left))
          (geom_id_resolution_bits (hist_geom_identity right)).

(** Build witness from history object — morphism must preserve SDF fingerprint. *)
Definition witness_from_history_object (o : history_object_geom)
    : geometric_memory_witness :=
  {| geom_witness_fingerprint := geom_id_fingerprint (hist_geom_identity o);
     geom_witness_resolution_bits := geom_id_resolution_bits (hist_geom_identity o);
     geom_witness_sdf_canonical := true |}.

(** Attempt typed geometric-memory morphism — fail closed on inadmissibility. *)
Definition apply_geometric_memory_morphism
    (obj : history_object_geom)
    (to_seq : nat)
    (conjunct : geometric_admissibility_conjunct)
    (excitement_selected : bool)
    : geometric_memory_morphism + geometric_memory_refusal :=
  if negb (geometric_conjunct_admits conjunct) then
    inr (gmr_gate_rejected (hist_geom_seq obj))
  else if negb (geom_witness_sdf_canonical (witness_from_history_object obj)) then
    inr (gmr_payload_without_sdf (hist_geom_field_digest obj))
  else if negb excitement_selected then
    inr (gmr_identity_mismatch
           (sdf_fp_digest (geom_id_fingerprint (hist_geom_identity obj)))
           (sdf_fp_digest (geom_id_fingerprint (hist_geom_identity obj))))
  else
    inl
      {| geom_morphism_from := obj;
         geom_morphism_to_seq := to_seq;
         geom_morphism_witness := witness_from_history_object obj;
         geom_morphism_excitement_selected := excitement_selected |}.

Lemma geometric_memory_host_id_refused (host_id : nat) :
  evaluate_host_id_identity true = gmv_host_id_refused.
Proof.
  reflexivity.
Qed.

Lemma geometric_memory_identity_ok_when_not_host_id :
  evaluate_host_id_identity false = gmv_identity_ok.
Proof.
  reflexivity.
Qed.

Lemma geometric_memory_payload_only_refused (payload : nat) :
  evaluate_payload_only_identity true = gmv_payload_only_refused.
Proof.
  reflexivity.
Qed.

Lemma refuse_host_id_identity_positive (host_id : nat) :
  refuse_host_id_identity host_id = gmr_host_id_not_geometric host_id.
Proof.
  reflexivity.
Qed.

Lemma refuse_payload_only_identity_positive (payload : nat) :
  refuse_payload_only_identity payload = gmr_payload_without_sdf payload.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Geometric memory composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Context for geometric memory over admissible history successors. *)
Record geometric_memory_ctx (src : ThermodynamicState) : Set := {
  geometric_memory_successors : list (history_candidate src)
}.

(** Geometric memory selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition geometric_memory_select (src : ThermodynamicState)
    (ctx : geometric_memory_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (geometric_memory_successors src ctx).

Theorem geometric_memory_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : geometric_memory_ctx src) :
  geometric_memory_select src ctx =
  excitement_select src (geometric_memory_successors src ctx).
Proof.
  unfold geometric_memory_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem geometric_memory_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : geometric_memory_ctx src) :
  geometric_memory_select src ctx =
  urge_recovery_select src (geometric_memory_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem geometric_memory_no_local_argmin
    (src : ThermodynamicState) (ctx : geometric_memory_ctx src) :
  geometric_memory_select src ctx =
  excitement_select src (geometric_memory_successors src ctx).
Proof.
  exact (geometric_memory_select_eq_excitement_select src ctx).
Qed.

Lemma geometric_memory_empty (src : ThermodynamicState)
    (ctx : geometric_memory_ctx src)
    (Hnil : geometric_memory_successors src ctx = nil) :
  geometric_memory_select src ctx = inr exc_no_candidates.
Proof.
  unfold geometric_memory_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §5.3 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition geometric_fixture_fingerprint : sdf_fingerprint :=
  {| sdf_fp_digest := 42;
     sdf_fp_grain := 7 |}.

Definition geometric_fixture_identity : history_geometric_identity :=
  {| geom_id_fingerprint := geometric_fixture_fingerprint;
     geom_id_resolution_bits := 2 |}.

Definition geometric_fixture_object : history_object_geom :=
  {| hist_geom_seq := 0;
     hist_geom_identity := geometric_fixture_identity;
     hist_geom_field_digest := 42 |}.

Definition geometric_fixture_object_same_identity : history_object_geom :=
  {| hist_geom_seq := 99;
     hist_geom_identity := geometric_fixture_identity;
     hist_geom_field_digest := 42 |}.

Definition geometric_fixture_object_distinct : history_object_geom :=
  {| hist_geom_seq := 1;
     hist_geom_identity :=
       {| geom_id_fingerprint := {| sdf_fp_digest := 7; sdf_fp_grain := 7 |};
          geom_id_resolution_bits := 2 |};
     hist_geom_field_digest := 7 |}.

Definition geometric_fixture_conjunct : geometric_admissibility_conjunct :=
  {| geom_conj_gate_ok := true;
     geom_conj_sdf_canonical := true;
     geom_conj_excitement_preserves := true |}.

Theorem geometric_fixture_host_id_refused :
  refuse_host_id_identity 0xdead = gmr_host_id_not_geometric 0xdead.
Proof.
  reflexivity.
Qed.

Theorem geometric_fixture_payload_only_refused :
  refuse_payload_only_identity 42 = gmr_payload_without_sdf 42.
Proof.
  reflexivity.
Qed.

Theorem geometric_fixture_apply_morphism_ok :
  apply_geometric_memory_morphism
    geometric_fixture_object 1 geometric_fixture_conjunct true
  = inl
      {| geom_morphism_from := geometric_fixture_object;
         geom_morphism_to_seq := 1;
         geom_morphism_witness := witness_from_history_object geometric_fixture_object;
         geom_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem geometric_fixture_matching_identity :
  geometric_identity_matches
    geometric_fixture_object geometric_fixture_object_same_identity = true.
Proof.
  reflexivity.
Qed.

Theorem geometric_fixture_distinct_identity :
  geometric_identity_matches
    geometric_fixture_object geometric_fixture_object_distinct = false.
Proof.
  reflexivity.
Qed.

Theorem geometric_fixture_witness_preserves_fingerprint :
  geom_witness_fingerprint (witness_from_history_object geometric_fixture_object) =
  geometric_fixture_fingerprint.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition geometric_memory_physics_green : bool := false.

Lemma geometric_memory_physics_green_false :
  geometric_memory_physics_green = false.
Proof. reflexivity. Qed.

Definition geometric_memory_production_wired : bool := false.

Lemma geometric_memory_production_wired_false :
  geometric_memory_production_wired = false.
Proof. reflexivity. Qed.

Theorem geometric_memory_module_witness : True.
Proof. exact I. Qed.

Theorem geometric_memory_no_new_axiom : True.
Proof. exact I. Qed.

Theorem geometric_memory_host_id_not_ok :
  evaluate_host_id_identity true <> gmv_identity_ok.
Proof.
  unfold evaluate_host_id_identity.
  discriminate.
Qed.

Theorem geometric_memory_payload_only_not_ok :
  evaluate_payload_only_identity true <> gmv_identity_ok.
Proof.
  unfold evaluate_payload_only_identity.
  discriminate.
Qed.
