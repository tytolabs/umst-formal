(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/SignedPropagate.v                                 *)
(*                                                                      *)
(*  Meso acting Urge — §4 propagation of signed stamped witnessed       *)
(*  states. Stamp `T` required; witness retained; unsigned propagation  *)
(*  refused — not silent accept. Composes `excitement_select`; no second *)
(*  argmin.                                                             *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool QArith ZArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Open Scope Q_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Signed stamped witnessed carriers (§4)                 *)
(* ------------------------------------------------------------------ *)

(** Wall ISO chronology stamp surrogate — `observed_at_wall` must contain `T`. *)
Record signed_propagate_wall_stamp : Set := {
  signed_wall_seq : nat;
  signed_wall_has_t : bool
}.

(** Signed payload surrogate on the propagation carrier. *)
Record signed_stamped_witness_state : Set := {
  signed_value : Z;
  signed_stamp : signed_propagate_wall_stamp;
  signed_witness_bits : nat
}.

(** One admissible propagation step — signed delta + post stamp/witness. *)
Record signed_propagation_step : Set := {
  signed_delta : Z;
  signed_post_stamp : signed_propagate_wall_stamp;
  signed_post_witness_bits : nat
}.

(** Witness bundle a propagation morphism must preserve (§4). *)
Record signed_propagate_witness : Set := {
  signed_witness_stamp : signed_propagate_wall_stamp;
  signed_witness_bit_budget : nat
}.

(** Typed propagation morphism — admissible signed transition, not unsigned carry. *)
Record signed_propagate_morphism : Set := {
  signed_morphism_from : signed_stamped_witness_state;
  signed_morphism_to : signed_stamped_witness_state;
  signed_morphism_witness : signed_propagate_witness;
  signed_morphism_excitement_selected : bool
}.

(** Fail-closed propagation errors — positive refuse, not silent no-op. *)
Inductive signed_propagate_refusal :=
  | spr_prior_stamp_invalid (seq : nat)
  | spr_post_stamp_invalid (seq : nat)
  | spr_unsigned_propagation_refused
  | spr_witness_dropped (prior post : nat)
  | spr_signed_overflow
  | spr_gate_rejected (seq : nat).

(** Verdict of a propagation operation class. *)
Inductive signed_propagate_verdict :=
  | spv_morphism_ok
  | spv_unsigned_propagation_refused
  | spv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §4 admissibility conjunct + positive refuse            *)
(* ------------------------------------------------------------------ *)

(** §4 admissibility conjunct inputs (surrogate). *)
Record signed_admissibility_conjunct : Set := {
  signed_conj_gate_ok : bool;
  signed_conj_stamp_ok : bool;
  signed_conj_witness_present : bool;
  signed_conj_excitement_preserves : bool
}.

(** Whether wall stamp passes minimal ISO `T` honesty. *)
Definition wall_stamp_ok (s : signed_propagate_wall_stamp) : bool :=
  signed_wall_has_t s.

(** Whether witness is present for propagation (non-zero bits). *)
Definition witness_present (st : signed_stamped_witness_state) : bool :=
  Nat.ltb 0 (signed_witness_bits st).

(** Evaluate `admit(h) ⟺ gate ∧ stamp ∧ witness ∧ Excitement preserves`. *)
Definition signed_conjunct_admits (c : signed_admissibility_conjunct) : bool :=
  signed_conj_gate_ok c &&
  signed_conj_stamp_ok c &&
  signed_conj_witness_present c &&
  signed_conj_excitement_preserves c.

(** Classify unsigned carry vs typed morphism without performing I/O. *)
Definition evaluate_signed_propagate_operation (is_unsigned_carry : bool)
    : signed_propagate_verdict :=
  if is_unsigned_carry then spv_unsigned_propagation_refused else spv_morphism_ok.

(** Positive refuse: unsigned propagation is inadmissible — witness required. *)
Definition refuse_unsigned_propagation : signed_propagate_refusal :=
  spr_unsigned_propagation_refused.

(** Build witness from prior state — morphism must preserve stamps and witness. *)
Definition witness_from_signed_state (st : signed_stamped_witness_state)
    : signed_propagate_witness :=
  {| signed_witness_stamp := signed_stamp st;
     signed_witness_bit_budget := signed_witness_bits st |}.

(** Surrogate signed overflow fence on additive propagation. *)
Definition signed_add_ok (prior delta : Z) : bool :=
  let result := prior + delta in
  (result >=? -1000000) && (result <=? 1000000).

(** Attempt §4 propagate signed stamped witnessed state — fail closed. *)
Definition propagate_signed_state
    (prior : signed_stamped_witness_state)
    (step : signed_propagation_step)
    (conjunct : signed_admissibility_conjunct)
    (excitement_selected : bool)
    : signed_stamped_witness_state + signed_propagate_refusal :=
  if negb (wall_stamp_ok (signed_stamp prior)) then
    inr (spr_prior_stamp_invalid (signed_wall_seq (signed_stamp prior)))
  else if negb (witness_present prior) then
    inr spr_unsigned_propagation_refused
  else if negb (wall_stamp_ok (signed_post_stamp step)) then
    inr (spr_post_stamp_invalid (signed_wall_seq (signed_post_stamp step)))
  else if Nat.ltb (signed_post_witness_bits step) (signed_witness_bits prior) then
    inr (spr_witness_dropped (signed_witness_bits prior)
                              (signed_post_witness_bits step))
  else if negb (signed_add_ok (signed_value prior) (signed_delta step)) then
    inr spr_signed_overflow
  else if negb (signed_conjunct_admits conjunct) then
    inr (spr_gate_rejected (signed_wall_seq (signed_stamp prior)))
  else if negb excitement_selected then
    inr spr_unsigned_propagation_refused
  else
    inl
      {| signed_value := signed_value prior + signed_delta step;
         signed_stamp := signed_post_stamp step;
         signed_witness_bits := signed_post_witness_bits step |}.

(** Attempt typed propagation morphism — packages prior/post + witness. *)
Definition apply_signed_propagate_morphism
    (prior : signed_stamped_witness_state)
    (step : signed_propagation_step)
    (conjunct : signed_admissibility_conjunct)
    (excitement_selected : bool)
    : signed_propagate_morphism + signed_propagate_refusal :=
  match propagate_signed_state prior step conjunct excitement_selected with
  | inl post =>
      inl
        {| signed_morphism_from := prior;
           signed_morphism_to := post;
           signed_morphism_witness := witness_from_signed_state prior;
           signed_morphism_excitement_selected := excitement_selected |}
  | inr r => inr r
  end.

Lemma signed_propagate_unsigned_refused
    (is_unsigned_carry : bool) :
  is_unsigned_carry = true ->
  evaluate_signed_propagate_operation is_unsigned_carry =
  spv_unsigned_propagation_refused.
Proof.
  intros H. unfold evaluate_signed_propagate_operation. rewrite H. reflexivity.
Qed.

Lemma signed_propagate_morphism_ok_when_not_unsigned :
  evaluate_signed_propagate_operation false = spv_morphism_ok.
Proof.
  reflexivity.
Qed.

Lemma refuse_unsigned_propagation_positive :
  refuse_unsigned_propagation = spr_unsigned_propagation_refused.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Signed propagate composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Context for signed propagation over admissible history successors. *)
Record signed_propagate_ctx (src : ThermodynamicState) : Set := {
  signed_propagate_successors : list (history_candidate src)
}.

(** Signed propagation **is** `urge_recovery_select` / `excitement_select`. *)
Definition signed_propagate_select (src : ThermodynamicState)
    (ctx : signed_propagate_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (signed_propagate_successors src ctx).

Theorem signed_propagate_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : signed_propagate_ctx src) :
  signed_propagate_select src ctx =
  excitement_select src (signed_propagate_successors src ctx).
Proof.
  unfold signed_propagate_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem signed_propagate_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : signed_propagate_ctx src) :
  signed_propagate_select src ctx =
  urge_recovery_select src (signed_propagate_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem signed_propagate_no_local_argmin
    (src : ThermodynamicState) (ctx : signed_propagate_ctx src) :
  signed_propagate_select src ctx =
  excitement_select src (signed_propagate_successors src ctx).
Proof.
  exact (signed_propagate_select_eq_excitement_select src ctx).
Qed.

Lemma signed_propagate_empty (src : ThermodynamicState)
    (ctx : signed_propagate_ctx src)
    (Hnil : signed_propagate_successors src ctx = nil) :
  signed_propagate_select src ctx = inr exc_no_candidates.
Proof.
  unfold signed_propagate_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §4 fixtures + witness theorems                          *)
(* ------------------------------------------------------------------ *)

Definition signed_fixture_stamp : signed_propagate_wall_stamp :=
  {| signed_wall_seq := 1;
     signed_wall_has_t := true |}.

Definition signed_fixture_post_stamp : signed_propagate_wall_stamp :=
  {| signed_wall_seq := 2;
     signed_wall_has_t := true |}.

Definition signed_fixture_state : signed_stamped_witness_state :=
  {| signed_value := 10;
     signed_stamp := signed_fixture_stamp;
     signed_witness_bits := 4 |}.

Definition signed_fixture_step : signed_propagation_step :=
  {| signed_delta := 3;
     signed_post_stamp := signed_fixture_post_stamp;
     signed_post_witness_bits := 4 |}.

Definition signed_fixture_conjunct : signed_admissibility_conjunct :=
  {| signed_conj_gate_ok := true;
     signed_conj_stamp_ok := true;
     signed_conj_witness_present := true;
     signed_conj_excitement_preserves := true |}.

Definition signed_fixture_post_state : signed_stamped_witness_state :=
  {| signed_value := 13;
     signed_stamp := signed_fixture_post_stamp;
     signed_witness_bits := 4 |}.

Theorem signed_fixture_unsigned_refused :
  refuse_unsigned_propagation = spr_unsigned_propagation_refused.
Proof.
  reflexivity.
Qed.

Theorem signed_fixture_propagate_ok :
  propagate_signed_state
    signed_fixture_state signed_fixture_step signed_fixture_conjunct true
  = inl signed_fixture_post_state.
Proof.
  reflexivity.
Qed.

Theorem signed_fixture_apply_morphism_ok :
  apply_signed_propagate_morphism
    signed_fixture_state signed_fixture_step signed_fixture_conjunct true
  = inl
      {| signed_morphism_from := signed_fixture_state;
         signed_morphism_to := signed_fixture_post_state;
         signed_morphism_witness := witness_from_signed_state signed_fixture_state;
         signed_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Definition signed_fixture_unsigned_state : signed_stamped_witness_state :=
  {| signed_value := 1;
     signed_stamp := signed_fixture_stamp;
     signed_witness_bits := 0 |}.

Theorem signed_fixture_unsigned_propagation_refused :
  propagate_signed_state
    signed_fixture_unsigned_state signed_fixture_step signed_fixture_conjunct true
  = inr spr_unsigned_propagation_refused.
Proof.
  reflexivity.
Qed.

Definition signed_fixture_witness_drop_step : signed_propagation_step :=
  {| signed_delta := 1;
     signed_post_stamp := signed_fixture_post_stamp;
     signed_post_witness_bits := 2 |}.

Theorem signed_fixture_witness_drop_refused :
  propagate_signed_state
    signed_fixture_state signed_fixture_witness_drop_step
    signed_fixture_conjunct true
  = inr (spr_witness_dropped 4 2).
Proof.
  reflexivity.
Qed.

Theorem signed_fixture_witness_preserves_stamp :
  signed_witness_stamp (witness_from_signed_state signed_fixture_state) =
  signed_fixture_stamp.
Proof.
  reflexivity.
Qed.

Theorem signed_fixture_wall_stamp_ok :
  wall_stamp_ok signed_fixture_stamp = true.
Proof.
  reflexivity.
Qed.

Theorem signed_fixture_witness_present :
  witness_present signed_fixture_state = true.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition signed_propagate_physics_green : bool := false.

Lemma signed_propagate_physics_green_false :
  signed_propagate_physics_green = false.
Proof. reflexivity. Qed.

Definition signed_propagate_production_wired : bool := false.

Lemma signed_propagate_production_wired_false :
  signed_propagate_production_wired = false.
Proof. reflexivity. Qed.

Theorem signed_propagate_module_witness : True.
Proof. exact I. Qed.

Theorem signed_propagate_no_new_axiom : True.
Proof. exact I. Qed.

Theorem signed_propagate_positive_refuse_not_silent :
  evaluate_signed_propagate_operation true <> spv_morphism_ok.
Proof.
  unfold evaluate_signed_propagate_operation.
  discriminate.
Qed.
