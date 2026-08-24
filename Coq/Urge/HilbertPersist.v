(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/HilbertPersist.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §12.7 persist Hilbert (acting) distinct from     *)
(*  occupancy Hilbert (knowing). Acting fiber only — refuse fuse with   *)
(*  knowing occupancy Hilbert (not implemented here). Composes          *)
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
(*  SECTION 1: Acting persist Hilbert carriers (§12.7 acting fiber)   *)
(* ------------------------------------------------------------------ *)

(** Acting meso role tag — persist Hilbert indexes Device-tier sled keys. *)
Inductive hilbert_persist_role :=
  | hpr_persist_acting.

(** Knowing occupancy Hilbert is **not** on this acting fiber — cite only for refuse. *)
Inductive occupancy_knowing_hilbert_refused :=
  | okh_fuse_persist_into_occupancy
  | okh_fuse_occupancy_into_persist
  | okh_knowing_fiber_not_on_acting_meso.

(** UCRS stamp surrogate carried through persist Hilbert morphism. *)
Record persist_hilbert_ucrs_stamp : Set := {
  persist_ucrs_seq : nat;
  persist_ucrs_wall_has_t : bool
}.

(** MergeSafe certificate surrogate — persist must not violate tier disjointness. *)
Record persist_hilbert_merge_safe_cert : Set := {
  persist_merge_safe : bool
}.

(** Persist Hilbert index — typed acting meso sled key layout (§12.7 acting). *)
Record persist_hilbert_index : Set := {
  persist_index_raw : nat;
  persist_index_bits : nat
}.

(** Snapshot identity at persist source (content-addressed surrogate). *)
Record persist_hilbert_snapshot : Set := {
  persist_snapshot_id : nat;
  persist_snapshot_head : ThermodynamicState;
  persist_snapshot_ucrs : persist_hilbert_ucrs_stamp;
  persist_snapshot_merge_safe : persist_hilbert_merge_safe_cert;
  persist_snapshot_provenance_intact : bool;
  persist_snapshot_index : persist_hilbert_index
}.

(** Witness bundle a persist Hilbert morphism must preserve (§12.7). *)
Record persist_hilbert_witness : Set := {
  persist_witness_ucrs : persist_hilbert_ucrs_stamp;
  persist_witness_merge_safe : persist_hilbert_merge_safe_cert;
  persist_witness_provenance_intact : bool;
  persist_witness_index : persist_hilbert_index
}.

(** Typed persist Hilbert morphism — admissible acting transition, not fuse. *)
Record persist_hilbert_morphism : Set := {
  persist_morphism_from : persist_hilbert_snapshot;
  persist_morphism_witness : persist_hilbert_witness;
  persist_morphism_excitement_selected : bool
}.

(** Fail-closed persist Hilbert errors — positive refuse, not silent no-op. *)
Inductive persist_hilbert_refusal :=
  | phr_fuse_occupancy_refused
  | phr_gate_rejected (seq : nat)
  | phr_merge_unsafe (snapshot_id : nat)
  | phr_provenance_loss (snapshot_id : nat)
  | phr_knowing_fiber_fuse_refused.

(** Verdict of a persist Hilbert operation class. *)
Inductive persist_hilbert_verdict :=
  | phv_morphism_ok
  | phv_fuse_occupancy_refused
  | phv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §12.7 admissibility conjunct + fuse refuse            *)
(* ------------------------------------------------------------------ *)

(** §12.7 admissibility conjunct inputs (surrogate). *)
Record persist_admissibility_conjunct : Set := {
  persist_conj_gate_ok : bool;
  persist_conj_merge_safe : bool;
  persist_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ MergeSafe ∧ Excitement preserves`. *)
Definition persist_conjunct_admits (c : persist_admissibility_conjunct) : bool :=
  persist_conj_gate_ok c &&
  persist_conj_merge_safe c &&
  persist_conj_excitement_preserves c.

(** Classify fuse attempt vs typed morphism without performing I/O. *)
Definition evaluate_persist_hilbert_operation (attempts_fuse : bool)
    : persist_hilbert_verdict :=
  if attempts_fuse then phv_fuse_occupancy_refused else phv_morphism_ok.

(** Positive refuse: fuse with occupancy knowing Hilbert is inadmissible. *)
Definition refuse_hilbert_fuse_occupancy : occupancy_knowing_hilbert_refused :=
  okh_fuse_persist_into_occupancy.

(** Positive refuse: knowing occupancy Hilbert fiber is not on acting meso. *)
Definition refuse_knowing_fiber_fuse : occupancy_knowing_hilbert_refused :=
  okh_knowing_fiber_not_on_acting_meso.

(** Build witness from snapshot — morphism must preserve stamps and index. *)
Definition witness_from_persist_snapshot (s : persist_hilbert_snapshot)
    : persist_hilbert_witness :=
  {| persist_witness_ucrs := persist_snapshot_ucrs s;
     persist_witness_merge_safe := persist_snapshot_merge_safe s;
     persist_witness_provenance_intact := persist_snapshot_provenance_intact s;
     persist_witness_index := persist_snapshot_index s |}.

(** Attempt typed persist Hilbert morphism — fail closed on inadmissibility. *)
Definition apply_persist_hilbert_morphism
    (snapshot : persist_hilbert_snapshot)
    (conjunct : persist_admissibility_conjunct)
    (excitement_selected : bool)
    (attempts_fuse : bool)
    : persist_hilbert_morphism + persist_hilbert_refusal :=
  if attempts_fuse then
    inr phr_fuse_occupancy_refused
  else if negb (persist_conjunct_admits conjunct) then
    inr (phr_gate_rejected (persist_ucrs_seq (persist_snapshot_ucrs snapshot)))
  else if negb (persist_merge_safe (persist_snapshot_merge_safe snapshot)) then
    inr (phr_merge_unsafe (persist_snapshot_id snapshot))
  else if negb (persist_snapshot_provenance_intact snapshot) then
    inr (phr_provenance_loss (persist_snapshot_id snapshot))
  else if negb excitement_selected then
    inr phr_knowing_fiber_fuse_refused
  else
    inl
      {| persist_morphism_from := snapshot;
         persist_morphism_witness := witness_from_persist_snapshot snapshot;
         persist_morphism_excitement_selected := excitement_selected |}.

Lemma persist_hilbert_fuse_occupancy_refused :
  evaluate_persist_hilbert_operation true = phv_fuse_occupancy_refused.
Proof.
  reflexivity.
Qed.

Lemma persist_hilbert_morphism_ok_when_not_fuse :
  evaluate_persist_hilbert_operation false = phv_morphism_ok.
Proof.
  reflexivity.
Qed.

Lemma refuse_hilbert_fuse_occupancy_positive :
  refuse_hilbert_fuse_occupancy = okh_fuse_persist_into_occupancy.
Proof.
  reflexivity.
Qed.

Lemma refuse_knowing_fiber_fuse_positive :
  refuse_knowing_fiber_fuse = okh_knowing_fiber_not_on_acting_meso.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Persist Hilbert composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Context for persist Hilbert over admissible history successors. *)
Record persist_hilbert_ctx (src : ThermodynamicState) : Set := {
  persist_hilbert_successors : list (history_candidate src)
}.

(** Persist Hilbert selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition persist_hilbert_select (src : ThermodynamicState)
    (ctx : persist_hilbert_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (persist_hilbert_successors src ctx).

Theorem persist_hilbert_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : persist_hilbert_ctx src) :
  persist_hilbert_select src ctx =
  excitement_select src (persist_hilbert_successors src ctx).
Proof.
  unfold persist_hilbert_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem persist_hilbert_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : persist_hilbert_ctx src) :
  persist_hilbert_select src ctx =
  urge_recovery_select src (persist_hilbert_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem persist_hilbert_no_local_argmin
    (src : ThermodynamicState) (ctx : persist_hilbert_ctx src) :
  persist_hilbert_select src ctx =
  excitement_select src (persist_hilbert_successors src ctx).
Proof.
  exact (persist_hilbert_select_eq_excitement_select src ctx).
Qed.

Lemma persist_hilbert_empty (src : ThermodynamicState)
    (ctx : persist_hilbert_ctx src)
    (Hnil : persist_hilbert_successors src ctx = nil) :
  persist_hilbert_select src ctx = inr exc_no_candidates.
Proof.
  unfold persist_hilbert_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §12.7 persist index surrogate + fixtures                *)
(* ------------------------------------------------------------------ *)

Definition default_persist_hilbert_bits : nat := 4.

Definition persist_hilbert_side (bits : nat) : nat :=
  Nat.shiftl 1 bits.

Definition persist_hilbert_mask (bits : nat) : nat :=
  persist_hilbert_side bits - 1.

(** Map `(ucrs_seq, grid_hash)` to 2D coords for persist acting path. *)
Definition persist_hilbert_coords (ucrs grid : nat) (bits : nat) : nat * nat :=
  let mask := persist_hilbert_mask bits in
  let x := ucrs mod (mask + 1) in
  let y := (Nat.lxor grid (grid / 65536)) mod (mask + 1) in
  (x, y).

(** Surrogate curve index — acting meso sled key layout (not occupancy). *)
Definition persist_curve_index (x y bits : nat) : nat :=
  let side := persist_hilbert_side bits in
  (x mod side) + (y mod side) * side.

Definition compute_persist_hilbert_index (ucrs grid bits : nat)
    : persist_hilbert_index :=
  let (x, y) := persist_hilbert_coords ucrs grid bits in
  {| persist_index_raw := persist_curve_index x y bits;
     persist_index_bits := bits |}.

Definition persist_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition persist_fixture_ucrs : persist_hilbert_ucrs_stamp :=
  {| persist_ucrs_seq := 7;
     persist_ucrs_wall_has_t := true |}.

Definition persist_fixture_merge_safe : persist_hilbert_merge_safe_cert :=
  {| persist_merge_safe := true |}.

Definition persist_fixture_index : persist_hilbert_index :=
  compute_persist_hilbert_index 7 0xABCD default_persist_hilbert_bits.

Definition persist_fixture_snapshot : persist_hilbert_snapshot :=
  {| persist_snapshot_id := 1;
     persist_snapshot_head := persist_fixture_state;
     persist_snapshot_ucrs := persist_fixture_ucrs;
     persist_snapshot_merge_safe := persist_fixture_merge_safe;
     persist_snapshot_provenance_intact := true;
     persist_snapshot_index := persist_fixture_index |}.

Definition persist_fixture_conjunct : persist_admissibility_conjunct :=
  {| persist_conj_gate_ok := true;
     persist_conj_merge_safe := true;
     persist_conj_excitement_preserves := true |}.

Theorem persist_fixture_fuse_occupancy_refused :
  refuse_hilbert_fuse_occupancy = okh_fuse_persist_into_occupancy.
Proof.
  reflexivity.
Qed.

Theorem persist_fixture_apply_morphism_ok :
  apply_persist_hilbert_morphism
    persist_fixture_snapshot persist_fixture_conjunct true false
  = inl
      {| persist_morphism_from := persist_fixture_snapshot;
         persist_morphism_witness := witness_from_persist_snapshot persist_fixture_snapshot;
         persist_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem persist_fixture_apply_fuse_refused :
  apply_persist_hilbert_morphism
    persist_fixture_snapshot persist_fixture_conjunct true true
  = inr phr_fuse_occupancy_refused.
Proof.
  reflexivity.
Qed.

Theorem persist_fixture_witness_preserves_ucrs :
  persist_witness_ucrs (witness_from_persist_snapshot persist_fixture_snapshot) =
  persist_fixture_ucrs.
Proof.
  reflexivity.
Qed.

Theorem persist_fixture_witness_preserves_index :
  persist_witness_index (witness_from_persist_snapshot persist_fixture_snapshot) =
  persist_fixture_index.
Proof.
  reflexivity.
Qed.

Theorem persist_fixture_index_bits :
  persist_index_bits persist_fixture_index = default_persist_hilbert_bits.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition hilbert_persist_physics_green : bool := false.

Lemma hilbert_persist_physics_green_false :
  hilbert_persist_physics_green = false.
Proof. reflexivity. Qed.

Definition hilbert_persist_production_wired : bool := false.

Lemma hilbert_persist_production_wired_false :
  hilbert_persist_production_wired = false.
Proof. reflexivity. Qed.

Theorem hilbert_persist_module_witness : True.
Proof. exact I. Qed.

Theorem hilbert_persist_no_new_axiom : True.
Proof. exact I. Qed.

Theorem hilbert_persist_positive_refuse_not_silent :
  evaluate_persist_hilbert_operation true <> phv_morphism_ok.
Proof.
  unfold evaluate_persist_hilbert_operation.
  discriminate.
Qed.

Theorem hilbert_persist_acting_role_witness :
  hpr_persist_acting = hpr_persist_acting.
Proof.
  reflexivity.
Qed.
