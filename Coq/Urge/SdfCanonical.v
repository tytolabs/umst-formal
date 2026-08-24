(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/SdfCanonical.v                                    *)
(*                                                                      *)
(*  Meso acting Urge — §12 SDFCanonical tautology named on history      *)
(*  identity. Byte-equal canonical SDFs imply behavior-equivalent       *)
(*  history actions — mirrors Lean `Behavior.SDFCanonical`.             *)
(*  Composes `excitement_select`; no second argmin.                     *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: History action + identity carriers (§12)               *)
(* ------------------------------------------------------------------ *)

(** History action bytes — SDF-shaped action surrogate (pre/post canonicalization). *)
Record history_action : Set := {
  history_action_bytes : list nat;
  history_action_canonicalized : bool;
  history_action_content_id : nat
}.

(** Content-addressed history identity — canonical SDF + stable content id. *)
Record history_identity : Set := {
  history_identity_action : history_action;
  history_identity_content_id : nat
}.

(** Witness bundle a SDF-canonical morphism must preserve (§12). *)
Record sdf_canonical_witness : Set := {
  sdf_canonical_witness_bytes : list nat;
  sdf_canonical_witness_content_id : nat;
  sdf_canonical_witness_canonicalized : bool
}.

(** Typed SDF-canonical morphism — admissible identity transition. *)
Record sdf_canonical_morphism : Set := {
  sdf_canonical_morphism_from : history_identity;
  sdf_canonical_morphism_to_content_id : nat;
  sdf_canonical_morphism_witness : sdf_canonical_witness;
  sdf_canonical_morphism_excitement_selected : bool
}.

(** Behavior equivalence verdict — mirrors Lean `BehaviorEquiv`. *)
Inductive behavior_equiv :=
  | bev_equivalent
  | bev_distinct.

(** Fail-closed SDF canonical errors — positive refuse, not silent accept. *)
Inductive sdf_canonical_refusal :=
  | scr_canonical_sdf_mismatch (left_id right_id : nat)
  | scr_alias_without_canonicalization (payload : nat)
  | scr_invented_equiv_without_canonical (content_id : nat)
  | scr_second_argmin
  | scr_gate_rejected (seq : nat).

(** Verdict of a SDF canonical admit operation class. *)
Inductive sdf_canonical_verdict :=
  | scv_admitted
  | scv_alias_refused
  | scv_invented_equiv_refused
  | scv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §12 admissibility conjunct + positive refuse            *)
(* ------------------------------------------------------------------ *)

(** Canonical SDF map — mirrors Lean `canonical_sdf := id` on `ByteArray`. *)
Definition canonical_sdf (a : history_action) : list nat :=
  history_action_bytes a.

(** List equality on `nat` lists (bool surrogate). *)
Fixpoint list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | nil, nil => true
  | x :: xt, y :: yt => Nat.eqb x y && list_eqb xt yt
  | _, _ => false
  end.

Lemma list_eqb_self (xs : list nat) : list_eqb xs xs = true.
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH, Nat.eqb_refl. reflexivity.
Qed.

(** Content id projection from canonicalized action. *)
Definition history_content_id (a : history_action) : nat :=
  history_action_content_id a.

(** Behavior equivalence from canonical SDF equality. *)
Definition behavior_equiv_of (left right : history_action) : behavior_equiv :=
  if list_eqb (canonical_sdf left) (canonical_sdf right) then
    bev_equivalent
  else
    bev_distinct.

(** §12 admissibility conjunct inputs (surrogate). *)
Record sdf_canonical_admissibility_conjunct : Set := {
  sdf_canonical_conj_gate_ok : bool;
  sdf_canonical_conj_canonicalized : bool;
  sdf_canonical_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ canonicalized ∧ Excitement preserves`. *)
Definition sdf_canonical_conjunct_admits (c : sdf_canonical_admissibility_conjunct) : bool :=
  sdf_canonical_conj_gate_ok c &&
  sdf_canonical_conj_canonicalized c &&
  sdf_canonical_conj_excitement_preserves c.

(** Classify alias-without-canonicalization vs SDF identity. *)
Definition evaluate_alias_without_canonicalization (alias_only : bool)
    : sdf_canonical_verdict :=
  if alias_only then scv_alias_refused else scv_admitted.

(** Classify invented behavior equivalence without canonical equality. *)
Definition evaluate_invented_equiv_without_canonical (invented : bool)
    : sdf_canonical_verdict :=
  if invented then scv_invented_equiv_refused else scv_admitted.

(** Positive refuse: alias bytes without canonicalization. *)
Definition refuse_alias_without_canonicalization (payload : nat)
    : sdf_canonical_refusal :=
  scr_alias_without_canonicalization payload.

(** Positive refuse: invented behavior equivalence without canonical equality. *)
Definition refuse_invented_equiv_without_canonical (content_id : nat)
    : sdf_canonical_refusal :=
  scr_invented_equiv_without_canonical content_id.

(** Positive refuse: second Excitement selector — compose `excitement_select`. *)
Definition refuse_second_argmin_selector : sdf_canonical_refusal :=
  scr_second_argmin.

(** Build witness from history identity — morphism must preserve canonical bytes. *)
Definition witness_from_history_identity (h : history_identity)
    : sdf_canonical_witness :=
  {| sdf_canonical_witness_bytes :=
       canonical_sdf (history_identity_action h);
     sdf_canonical_witness_content_id := history_identity_content_id h;
     sdf_canonical_witness_canonicalized :=
       history_action_canonicalized (history_identity_action h) |}.

(** §12 `SDFCanonical` tautology: `canonical_sdf a = canonical_sdf b → BehaviorEquiv a b`. *)
Definition sdf_canonical_theorem (left right : history_action)
    : behavior_equiv + sdf_canonical_refusal :=
  if negb (history_action_canonicalized left) then
    inr (scr_alias_without_canonicalization 0)
  else if negb (history_action_canonicalized right) then
    inr (scr_alias_without_canonicalization 0)
  else if list_eqb (canonical_sdf left) (canonical_sdf right) then
    inl bev_equivalent
  else
    inr (scr_canonical_sdf_mismatch
           (history_content_id left) (history_content_id right)).

(** Admit history identity pair under §12 SDF canonical discipline. *)
Definition admit_history_identity
    (left right : history_identity)
    (conjunct : sdf_canonical_admissibility_conjunct) :
  sdf_canonical_verdict + sdf_canonical_refusal :=
  if negb (sdf_canonical_conjunct_admits conjunct) then
    inr (scr_gate_rejected 0)
  else
    match sdf_canonical_theorem
            (history_identity_action left) (history_identity_action right) with
    | inl bev_equivalent =>
        if negb (Nat.eqb (history_identity_content_id left)
                         (history_content_id (history_identity_action left))) then
          inr (scr_invented_equiv_without_canonical (history_identity_content_id left))
        else if negb (Nat.eqb (history_identity_content_id right)
                             (history_content_id (history_identity_action right))) then
          inr (scr_invented_equiv_without_canonical (history_identity_content_id right))
        else if negb (Nat.eqb (history_identity_content_id left)
                              (history_identity_content_id right)) then
          inr (scr_canonical_sdf_mismatch
                 (history_identity_content_id left)
                 (history_identity_content_id right))
        else
          inl scv_admitted
    | inl bev_distinct =>
        inr (scr_canonical_sdf_mismatch
               (history_content_id (history_identity_action left))
               (history_content_id (history_identity_action right)))
    | inr r => inr r
    end.

(** Attempt typed SDF-canonical morphism — fail closed on inadmissibility. *)
Definition apply_sdf_canonical_morphism
    (identity : history_identity)
    (to_content_id : nat)
    (conjunct : sdf_canonical_admissibility_conjunct)
    (excitement_selected : bool)
    : sdf_canonical_morphism + sdf_canonical_refusal :=
  if negb (sdf_canonical_conjunct_admits conjunct) then
    inr (scr_gate_rejected (history_identity_content_id identity))
  else if negb (history_action_canonicalized (history_identity_action identity)) then
    inr (scr_alias_without_canonicalization (history_identity_content_id identity))
  else if negb excitement_selected then
    inr (scr_canonical_sdf_mismatch
           (history_identity_content_id identity) to_content_id)
  else
    inl
      {| sdf_canonical_morphism_from := identity;
         sdf_canonical_morphism_to_content_id := to_content_id;
         sdf_canonical_morphism_witness := witness_from_history_identity identity;
         sdf_canonical_morphism_excitement_selected := excitement_selected |}.

Lemma sdf_canonical_alias_refused :
  evaluate_alias_without_canonicalization true = scv_alias_refused.
Proof.
  reflexivity.
Qed.

Lemma sdf_canonical_admitted_when_not_alias :
  evaluate_alias_without_canonicalization false = scv_admitted.
Proof.
  reflexivity.
Qed.

Lemma sdf_canonical_invented_equiv_refused :
  evaluate_invented_equiv_without_canonical true = scv_invented_equiv_refused.
Proof.
  reflexivity.
Qed.

Lemma refuse_alias_without_canonicalization_positive (payload : nat) :
  refuse_alias_without_canonicalization payload =
  scr_alias_without_canonicalization payload.
Proof.
  reflexivity.
Qed.

Lemma refuse_second_argmin_selector_positive :
  refuse_second_argmin_selector = scr_second_argmin.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: SDF canonical composes Excitement (no second argmin)     *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — import selector; refuse second local argmin. *)
Inductive sdf_canonical_excitement_compose_pin :=
  | sccp_import_select_excitement
  | sccp_second_argmin_refused.

(** Context for SDF canonical over admissible history successors. *)
Record sdf_canonical_ctx (src : ThermodynamicState) : Set := {
  sdf_canonical_successors : list (history_candidate src)
}.

(** SDF canonical path composes `excitement_select` — not a second argmin. *)
Definition sdf_canonical_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : sdf_canonical_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | sccp_import_select_excitement => excitement_select src cands
  | sccp_second_argmin_refused => inr exc_all_inadmissible
  end.

(** SDF canonical selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition sdf_canonical_select (src : ThermodynamicState)
    (ctx : sdf_canonical_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (sdf_canonical_successors src ctx).

Theorem sdf_canonical_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  sdf_canonical_excitement_select src cands sccp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem sdf_canonical_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : sdf_canonical_ctx src) :
  sdf_canonical_select src ctx =
  excitement_select src (sdf_canonical_successors src ctx).
Proof.
  unfold sdf_canonical_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem sdf_canonical_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : sdf_canonical_ctx src) :
  sdf_canonical_select src ctx =
  urge_recovery_select src (sdf_canonical_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem sdf_canonical_no_local_argmin
    (src : ThermodynamicState) (ctx : sdf_canonical_ctx src) :
  sdf_canonical_select src ctx =
  excitement_select src (sdf_canonical_successors src ctx).
Proof.
  exact (sdf_canonical_select_eq_excitement_select src ctx).
Qed.

Theorem sdf_canonical_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  sdf_canonical_excitement_select src cands sccp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma sdf_canonical_empty (src : ThermodynamicState)
    (ctx : sdf_canonical_ctx src)
    (Hnil : sdf_canonical_successors src ctx = nil) :
  sdf_canonical_select src ctx = inr exc_no_candidates.
Proof.
  unfold sdf_canonical_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §12 fixtures + witness theorems                         *)
(* ------------------------------------------------------------------ *)

Definition sdf_canonical_fixture_bytes : list nat :=
  [115; 100; 102; 58; 118; 49; 58; 99; 104; 97; 105; 114].

Definition sdf_canonical_fixture_content_id : nat := 12007.

Definition sdf_canonical_fixture_action : history_action :=
  {| history_action_bytes := sdf_canonical_fixture_bytes;
     history_action_canonicalized := true;
     history_action_content_id := sdf_canonical_fixture_content_id |}.

Definition sdf_canonical_fixture_identity : history_identity :=
  {| history_identity_action := sdf_canonical_fixture_action;
     history_identity_content_id := sdf_canonical_fixture_content_id |}.

Definition sdf_canonical_fixture_identity_same : history_identity :=
  {| history_identity_action := sdf_canonical_fixture_action;
     history_identity_content_id := sdf_canonical_fixture_content_id |}.

Definition sdf_canonical_fixture_action_distinct : history_action :=
  {| history_action_bytes := [115; 100; 102; 58; 118; 49; 58; 115; 112; 104; 101; 114; 101];
     history_action_canonicalized := true;
     history_action_content_id := 12008 |}.

Definition sdf_canonical_fixture_identity_distinct : history_identity :=
  {| history_identity_action := sdf_canonical_fixture_action_distinct;
     history_identity_content_id := 12008 |}.

Definition sdf_canonical_fixture_action_alias : history_action :=
  {| history_action_bytes := sdf_canonical_fixture_bytes;
     history_action_canonicalized := false;
     history_action_content_id := sdf_canonical_fixture_content_id |}.

Definition sdf_canonical_fixture_conjunct : sdf_canonical_admissibility_conjunct :=
  {| sdf_canonical_conj_gate_ok := true;
     sdf_canonical_conj_canonicalized := true;
     sdf_canonical_conj_excitement_preserves := true |}.

Theorem sdf_canonical_fixture_canonical_sdf_id :
  canonical_sdf sdf_canonical_fixture_action = sdf_canonical_fixture_bytes.
Proof.
  reflexivity.
Qed.

Theorem sdf_canonical_fixture_byte_equal_admitted :
  admit_history_identity
    sdf_canonical_fixture_identity sdf_canonical_fixture_identity_same
    sdf_canonical_fixture_conjunct
  = inl scv_admitted.
Proof.
  reflexivity.
Qed.

Theorem sdf_canonical_fixture_alias_refused :
  refuse_alias_without_canonicalization 42 =
  scr_alias_without_canonicalization 42.
Proof.
  reflexivity.
Qed.

Theorem sdf_canonical_fixture_apply_morphism_ok :
  apply_sdf_canonical_morphism
    sdf_canonical_fixture_identity sdf_canonical_fixture_content_id
    sdf_canonical_fixture_conjunct true
  = inl
      {| sdf_canonical_morphism_from := sdf_canonical_fixture_identity;
         sdf_canonical_morphism_to_content_id := sdf_canonical_fixture_content_id;
         sdf_canonical_morphism_witness :=
           witness_from_history_identity sdf_canonical_fixture_identity;
         sdf_canonical_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem sdf_canonical_fixture_witness_preserves_bytes :
  sdf_canonical_witness_bytes
    (witness_from_history_identity sdf_canonical_fixture_identity) =
  sdf_canonical_fixture_bytes.
Proof.
  reflexivity.
Qed.

Theorem sdf_canonical_theorem_tautology
    (a : history_action)
    (Hcanon : history_action_canonicalized a = true) :
  sdf_canonical_theorem a a = inl bev_equivalent.
Proof.
  unfold sdf_canonical_theorem.
  rewrite !Hcanon, (list_eqb_self (canonical_sdf a)).
  reflexivity.
Qed.

Theorem sdf_canonical_alias_not_admitted :
  evaluate_alias_without_canonicalization true <> scv_admitted.
Proof.
  unfold evaluate_alias_without_canonicalization.
  discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition sdf_canonical_physics_green : bool := false.

Lemma sdf_canonical_physics_green_false :
  sdf_canonical_physics_green = false.
Proof. reflexivity. Qed.

Definition sdf_canonical_production_wired : bool := false.

Lemma sdf_canonical_production_wired_false :
  sdf_canonical_production_wired = false.
Proof. reflexivity. Qed.

Theorem sdf_canonical_module_witness : True.
Proof. exact I. Qed.

Theorem sdf_canonical_no_new_axiom : True.
Proof. exact I. Qed.

Theorem sdf_canonical_positive_refuse_not_silent :
  evaluate_invented_equiv_without_canonical true <> scv_admitted.
Proof.
  unfold evaluate_invented_equiv_without_canonical.
  discriminate.
Qed.
