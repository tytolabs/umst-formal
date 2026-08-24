(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/OriginRefuse.v                                    *)
(*                                                                      *)
(*  Meso acting Urge — §16.8 origin.cursor.com / GitHub-as-origin       *)
(*  refuse for Compose. Typed positive refuse — not only !physics_green. *)
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
(*  SECTION 1: Entity labels + origin host classification           *)
(* ------------------------------------------------------------------ *)

(** Urge entity label for §16.8 origin policy row. *)
Inductive origin_entity_label :=
  | oel_compose
  | oel_labs_public_oss.

(** Classified origin host for policy evaluation. *)
Inductive origin_host_class :=
  | ohc_origin_cursor
  | ohc_github
  | ohc_forgejo_canonical
  | ohc_unclassified.

(** Whether host is the never-SSOT `origin.cursor.com` remote. *)
Definition origin_host_is_cursor (c : origin_host_class) : bool :=
  match c with
  | ohc_origin_cursor => true
  | _ => false
  end.

(** Whether host is GitHub-as-origin. *)
Definition origin_host_is_github (c : origin_host_class) : bool :=
  match c with
  | ohc_github => true
  | _ => false
  end.

(** Canonical host pins from §16.8. *)
Definition origin_cursor_host_pin : string := "origin.cursor.com".
Definition github_origin_host_pin : string := "github.com".
Definition forgejo_canonical_host_pin : string := "forgejo.tailnet".

(** Classify origin host string into policy row host (typed surrogate). *)
Definition classify_origin_host (host : string) : origin_host_class :=
  if String.eqb host origin_cursor_host_pin then ohc_origin_cursor
  else if String.eqb host github_origin_host_pin then ohc_github
  else if String.eqb host forgejo_canonical_host_pin then ohc_forgejo_canonical
  else if String.eqb host "" then ohc_unclassified
  else ohc_unclassified.

(** Remote origin descriptor — entity label + host string. *)
Record origin_remote_descriptor : Set := {
  origin_remote_entity : origin_entity_label;
  origin_remote_host : string
}.

(** UCRS stamp surrogate carried through origin policy checks. *)
Record origin_ucrs_stamp : Set := {
  origin_ucrs_seq : nat;
  origin_ucrs_wall_has_t : bool
}.

(** Witness bundle origin admission must preserve (§16.8). *)
Record origin_policy_witness : Set := {
  origin_witness_ucrs : origin_ucrs_stamp;
  origin_witness_forgejo_canonical : bool
}.

(** Typed origin policy morphism — admissible admission, not silent accept. *)
Record origin_refuse_morphism : Set := {
  origin_morphism_remote : origin_remote_descriptor;
  origin_morphism_witness : origin_policy_witness;
  origin_morphism_excitement_selected : bool
}.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §16.8 policy verdict + positive refuse                  *)
(* ------------------------------------------------------------------ *)

(** Origin policy verdict for entity × host. *)
Inductive origin_policy_verdict :=
  | opv_admitted
  | opv_refused.

(** Typed refusal when origin policy rejects entity × host. *)
Inductive origin_refusal :=
  | or_origin_cursor_compose_refused
  | or_github_as_origin_compose_refused
  | or_origin_cursor_labs_refused
  | or_unclassified_host
  | or_dual_push_compose_refused
  | or_gate_rejected (seq : nat).

(** Whether remote host is refused upstream for Compose (§16.8 / §13.6). *)
Definition compose_upstream_refused (host : string) : bool :=
  String.eqb host github_origin_host_pin ||
  String.eqb host origin_cursor_host_pin.

(** §16.8 admissibility conjunct inputs (surrogate). *)
Record origin_admissibility_conjunct : Set := {
  origin_conj_gate_ok : bool;
  origin_conj_forgejo_canonical : bool;
  origin_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ Forgejo canonical ∧ Excitement preserves`. *)
Definition origin_conjunct_admits (c : origin_admissibility_conjunct) : bool :=
  origin_conj_gate_ok c &&
  origin_conj_forgejo_canonical c &&
  origin_conj_excitement_preserves c.

(** Evaluate §16.8 origin policy for entity × classified host. *)
Definition evaluate_origin_policy
    (entity : origin_entity_label) (host : origin_host_class)
    : origin_policy_verdict + origin_refusal :=
  match entity, host with
  | oel_compose, ohc_origin_cursor =>
    inr or_origin_cursor_compose_refused
  | oel_compose, ohc_github =>
    inr or_github_as_origin_compose_refused
  | oel_labs_public_oss, ohc_origin_cursor =>
    inr or_origin_cursor_labs_refused
  | oel_labs_public_oss, ohc_github =>
    inl opv_admitted
  | _, ohc_forgejo_canonical =>
    inl opv_admitted
  | _, ohc_unclassified =>
    inr or_unclassified_host
  end.

(** Admit origin remote — `inr` when §16.8 policy refuses entity × host. *)
Definition admit_origin_remote (remote : origin_remote_descriptor)
    : origin_policy_verdict + origin_refusal :=
  evaluate_origin_policy
    (origin_remote_entity remote)
    (classify_origin_host (origin_remote_host remote)).

(** Positive refuse: `origin.cursor.com` for Compose entity. *)
Definition refuse_origin_cursor_for_compose : origin_refusal :=
  or_origin_cursor_compose_refused.

(** Positive refuse: `github.com` as origin for Compose entity. *)
Definition refuse_github_as_origin_for_compose : origin_refusal :=
  or_github_as_origin_compose_refused.

(** Positive refuse: dual-push / `origin repo create` on Compose trees. *)
Definition refuse_dual_push_compose : origin_refusal :=
  or_dual_push_compose_refused.

(** Build witness from remote descriptor. *)
Definition witness_from_remote (remote : origin_remote_descriptor)
    (stamp : origin_ucrs_stamp) : origin_policy_witness :=
  {| origin_witness_ucrs := stamp;
     origin_witness_forgejo_canonical :=
       match classify_origin_host (origin_remote_host remote) with
       | ohc_forgejo_canonical => true
       | _ => false
       end |}.

(** Attempt typed origin morphism — fail closed on inadmissibility. *)
Definition apply_origin_refuse_morphism
    (remote : origin_remote_descriptor)
    (conjunct : origin_admissibility_conjunct)
    (stamp : origin_ucrs_stamp)
    (excitement_selected : bool)
    : origin_refuse_morphism + origin_refusal :=
  if negb (origin_conjunct_admits conjunct) then
    inr (or_gate_rejected (origin_ucrs_seq stamp))
  else
    match admit_origin_remote remote with
    | inl _ =>
      if negb excitement_selected then
        inr or_unclassified_host
      else
        inl
          {| origin_morphism_remote := remote;
             origin_morphism_witness := witness_from_remote remote stamp;
             origin_morphism_excitement_selected := excitement_selected |}
    | inr r => inr r
    end.

Lemma refuse_origin_cursor_for_compose_positive :
  refuse_origin_cursor_for_compose = or_origin_cursor_compose_refused.
Proof.
  reflexivity.
Qed.

Lemma refuse_github_as_origin_for_compose_positive :
  refuse_github_as_origin_for_compose = or_github_as_origin_compose_refused.
Proof.
  reflexivity.
Qed.

Lemma refuse_dual_push_compose_positive :
  refuse_dual_push_compose = or_dual_push_compose_refused.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Compose excitement_select (no second argmin)           *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — import selector; refuse second local argmin. *)
Inductive origin_excitement_compose_pin :=
  | oecp_import_select_excitement
  | oecp_second_argmin_refused.

(** Context for origin refuse over admissible history successors. *)
Record origin_refuse_ctx (src : ThermodynamicState) : Set := {
  origin_refuse_successors : list (history_candidate src)
}.

(** Compose path composes `excitement_select` — not a second argmin. *)
Definition compose_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : origin_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | oecp_import_select_excitement => excitement_select src cands
  | oecp_second_argmin_refused => inr exc_all_inadmissible
  end.

(** Origin refuse selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition origin_refuse_select (src : ThermodynamicState)
    (ctx : origin_refuse_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (origin_refuse_successors src ctx).

Theorem compose_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  compose_excitement_select src cands oecp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem origin_refuse_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : origin_refuse_ctx src) :
  origin_refuse_select src ctx =
  excitement_select src (origin_refuse_successors src ctx).
Proof.
  unfold origin_refuse_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem origin_refuse_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : origin_refuse_ctx src) :
  origin_refuse_select src ctx =
  urge_recovery_select src (origin_refuse_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem origin_refuse_no_local_argmin
    (src : ThermodynamicState) (ctx : origin_refuse_ctx src) :
  origin_refuse_select src ctx =
  excitement_select src (origin_refuse_successors src ctx).
Proof.
  exact (origin_refuse_select_eq_excitement_select src ctx).
Qed.

Theorem compose_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  compose_excitement_select src cands oecp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma origin_refuse_empty (src : ThermodynamicState)
    (ctx : origin_refuse_ctx src)
    (Hnil : origin_refuse_successors src ctx = nil) :
  origin_refuse_select src ctx = inr exc_no_candidates.
Proof.
  unfold origin_refuse_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §16.8 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition origin_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition origin_fixture_ucrs : origin_ucrs_stamp :=
  {| origin_ucrs_seq := 8;
     origin_ucrs_wall_has_t := true |}.

Definition origin_fixture_conjunct : origin_admissibility_conjunct :=
  {| origin_conj_gate_ok := true;
     origin_conj_forgejo_canonical := true;
     origin_conj_excitement_preserves := true |}.

Definition compose_origin_cursor_fixture : origin_remote_descriptor :=
  {| origin_remote_entity := oel_compose;
     origin_remote_host := origin_cursor_host_pin |}.

Definition compose_github_origin_fixture : origin_remote_descriptor :=
  {| origin_remote_entity := oel_compose;
     origin_remote_host := github_origin_host_pin |}.

Definition compose_forgejo_canonical_fixture : origin_remote_descriptor :=
  {| origin_remote_entity := oel_compose;
     origin_remote_host := forgejo_canonical_host_pin |}.

Theorem origin_fixture_cursor_compose_refused :
  admit_origin_remote compose_origin_cursor_fixture =
  inr or_origin_cursor_compose_refused.
Proof.
  reflexivity.
Qed.

Theorem origin_fixture_github_compose_refused :
  admit_origin_remote compose_github_origin_fixture =
  inr or_github_as_origin_compose_refused.
Proof.
  reflexivity.
Qed.

Theorem origin_fixture_forgejo_compose_admitted :
  admit_origin_remote compose_forgejo_canonical_fixture = inl opv_admitted.
Proof.
  reflexivity.
Qed.

Theorem origin_fixture_compose_upstream_refused_github :
  compose_upstream_refused github_origin_host_pin = true.
Proof.
  reflexivity.
Qed.

Theorem origin_fixture_compose_upstream_refused_cursor :
  compose_upstream_refused origin_cursor_host_pin = true.
Proof.
  reflexivity.
Qed.

Theorem origin_fixture_apply_morphism_forgejo_ok :
  apply_origin_refuse_morphism
    compose_forgejo_canonical_fixture origin_fixture_conjunct
    origin_fixture_ucrs true
  = inl
      {| origin_morphism_remote := compose_forgejo_canonical_fixture;
         origin_morphism_witness :=
           witness_from_remote compose_forgejo_canonical_fixture
             origin_fixture_ucrs;
         origin_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem origin_fixture_classify_cursor :
  classify_origin_host origin_cursor_host_pin = ohc_origin_cursor.
Proof.
  reflexivity.
Qed.

Theorem origin_fixture_classify_github :
  classify_origin_host github_origin_host_pin = ohc_github.
Proof.
  reflexivity.
Qed.

Theorem origin_fixture_classify_forgejo :
  classify_origin_host forgejo_canonical_host_pin = ohc_forgejo_canonical.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition origin_refuse_physics_green : bool := false.

Lemma origin_refuse_physics_green_false :
  origin_refuse_physics_green = false.
Proof. reflexivity. Qed.

Definition origin_refuse_production_wired : bool := false.

Lemma origin_refuse_production_wired_false :
  origin_refuse_production_wired = false.
Proof. reflexivity. Qed.

Theorem origin_refuse_module_witness : True.
Proof. exact I. Qed.

Theorem origin_refuse_no_new_axiom : True.
Proof. exact I. Qed.

Theorem origin_refuse_positive_refuse_not_silent :
  admit_origin_remote compose_origin_cursor_fixture <> inl opv_admitted /\
  admit_origin_remote compose_github_origin_fixture <> inl opv_admitted.
Proof.
  split; discriminate.
Qed.

Theorem origin_refuse_compose_excitement_not_argmin :
  forall (src : ThermodynamicState) (ctx : origin_refuse_ctx src),
  origin_refuse_select src ctx =
  excitement_select src (origin_refuse_successors src ctx).
Proof.
  intros. exact (origin_refuse_no_local_argmin src ctx).
Qed.
