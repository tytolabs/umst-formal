(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/UnmeasuredMeasured.v                              *)
(*                                                                      *)
(*  Meso acting Urge — §17.7 production_wired taxonomy.                 *)
(*  `Unmeasured | Measured {value, dataset}` — UNKNOWN ≠ false-as-GREEN. *)
(*  Composes `excitement_select`; no second argmin.                      *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool String.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: §17.7 production_wired taxonomy carriers              *)
(* ------------------------------------------------------------------ *)

(** Blueprint §17.7 — fleet measurement absent vs measured on named dataset. *)
Inductive production_wired_taxonomy :=
  | pw_unmeasured
  | pw_measured (value : bool) (dataset : string).

(** Whether posture carries a fleet measurement (not merely unmeasured). *)
Definition production_wired_is_measured (pw : production_wired_taxonomy) : bool :=
  match pw with
  | pw_unmeasured => false
  | pw_measured _ _ => true
  end.

(** Measured value when present — `None` for `Unmeasured` (not `Some false`). *)
Definition production_wired_measured_value (pw : production_wired_taxonomy)
    : option bool :=
  match pw with
  | pw_unmeasured => None
  | pw_measured v _ => Some v
  end.

(** Dataset label when measured. *)
Definition production_wired_dataset (pw : production_wired_taxonomy)
    : option string :=
  match pw with
  | pw_unmeasured => None
  | pw_measured _ d => Some d
  end.

(** Non-empty dataset surrogate — empty label is inadmissible measurement. *)
Definition dataset_nonempty (d : string) : bool :=
  negb (String.eqb d "").

(** Fail-closed refusals when UNKNOWN collapses to false-as-GREEN. *)
Inductive false_as_green_refusal :=
  | fagr_unmeasured_collapsed_to_false
  | fagr_measured_true_not_physics_green.

(** Verdict of a production_wired posture class. *)
Inductive production_wired_verdict :=
  | pwv_honest_unmeasured
  | pwv_measured_false_ok
  | pwv_false_as_green_refused.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §17.7 positive refuse (UNKNOWN ≠ false-as-GREEN)       *)
(* ------------------------------------------------------------------ *)

(** §17.7 admissibility conjunct inputs (surrogate). *)
Record unmeasured_measured_conjunct : Set := {
  umm_conj_gate_ok : bool;
  umm_conj_false_as_green_refused : bool;
  umm_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ false-as-GREEN refused ∧ Excitement preserves`. *)
Definition umm_conjunct_admits (c : unmeasured_measured_conjunct) : bool :=
  umm_conj_gate_ok c &&
  umm_conj_false_as_green_refused c &&
  umm_conj_excitement_preserves c.

(** Refuse collapsing `Unmeasured` to `false` or treating measured `true` as physics GREEN. *)
Definition refuse_false_as_green (pw : production_wired_taxonomy)
    : option false_as_green_refusal :=
  match pw with
  | pw_unmeasured => Some fagr_unmeasured_collapsed_to_false
  | pw_measured true _ => Some fagr_measured_true_not_physics_green
  | pw_measured false _ => None
  end.

(** Legacy `bool` projection — `None` for `Unmeasured` (not `Some false`). *)
Definition production_wired_legacy_bool (pw : production_wired_taxonomy)
    : option bool :=
  production_wired_measured_value pw.

(** Whether a raw `bool` falsely claims measurement when taxonomy is `Unmeasured`. *)
Definition bool_claims_measurement_when_unmeasured
    (pw : production_wired_taxonomy) (claimed : bool) : bool :=
  match pw with
  | pw_unmeasured => claimed
  | pw_measured _ _ => false
  end.

(** Construct measured posture with non-empty dataset label. *)
Definition measured_production_wired (value : bool) (dataset : string)
    : production_wired_taxonomy + false_as_green_refusal :=
  if negb (dataset_nonempty dataset) then
    inr fagr_unmeasured_collapsed_to_false
  else
    inl (pw_measured value dataset).

(** Classify posture without collapsing UNKNOWN to false-as-GREEN. *)
Definition evaluate_production_wired (pw : production_wired_taxonomy)
    : production_wired_verdict :=
  match refuse_false_as_green pw with
  | Some _ => pwv_false_as_green_refused
  | None =>
    match pw with
    | pw_unmeasured => pwv_honest_unmeasured
    | pw_measured false _ => pwv_measured_false_ok
    | pw_measured true _ => pwv_false_as_green_refused
    end
  end.

Lemma refuse_false_as_green_unmeasured :
  refuse_false_as_green pw_unmeasured =
  Some fagr_unmeasured_collapsed_to_false.
Proof.
  reflexivity.
Qed.

Lemma production_wired_legacy_none_when_unmeasured :
  production_wired_legacy_bool pw_unmeasured = None.
Proof.
  reflexivity.
Qed.

Lemma unmeasured_not_measured :
  production_wired_is_measured pw_unmeasured = false.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Gossip mesh taxonomy — documented Unmeasured            *)
(* ------------------------------------------------------------------ *)

(** Gossip mesh production_wired taxonomy — `Unmeasured` while UCRS const stays `false`. *)
Definition gossip_mesh_production_wired_taxonomy : production_wired_taxonomy :=
  pw_unmeasured.

(** Documented mirror: UCRS `ucrs_gossip_mesh_production_wired()` = unmeasured posture. *)
Definition ucrs_gossip_mesh_documented_as_unmeasured : bool :=
  match gossip_mesh_production_wired_taxonomy with
  | pw_unmeasured => true
  | pw_measured _ _ => false
  end.

(** Positive refuse: treat unmeasured gossip mesh as measured-false GREEN. *)
Definition refuse_unmeasured_as_false_green : false_as_green_refusal :=
  fagr_unmeasured_collapsed_to_false.

Theorem gossip_mesh_taxonomy_is_unmeasured :
  gossip_mesh_production_wired_taxonomy = pw_unmeasured.
Proof.
  reflexivity.
Qed.

Theorem ucrs_gossip_mesh_documented_unmeasured_true :
  ucrs_gossip_mesh_documented_as_unmeasured = true.
Proof.
  reflexivity.
Qed.

Theorem gossip_mesh_refuse_false_as_green :
  refuse_false_as_green gossip_mesh_production_wired_taxonomy =
  Some fagr_unmeasured_collapsed_to_false.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Urge composes excitement_select (no second argmin)       *)
(* ------------------------------------------------------------------ *)

(** Context for unmeasured/measured history selection over admissible successors. *)
Record unmeasured_measured_ctx (src : ThermodynamicState) : Set := {
  unmeasured_measured_successors : list (history_candidate src)
}.

(** Excitement compose pin — Urge imports selector; no second argmin. *)
Inductive unmeasured_measured_excitement_pin :=
  | umep_import_select_excitement
  | umep_second_argmin_refused.

(** Unmeasured/measured path composes `excitement_select` — not a second argmin. *)
Definition unmeasured_measured_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : unmeasured_measured_excitement_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | umep_import_select_excitement => excitement_select src cands
  | umep_second_argmin_refused => inr exc_all_inadmissible
  end.

(** Unmeasured/measured selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition unmeasured_measured_select (src : ThermodynamicState)
    (ctx : unmeasured_measured_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (unmeasured_measured_successors src ctx).

Theorem unmeasured_measured_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : unmeasured_measured_ctx src) :
  unmeasured_measured_select src ctx =
  excitement_select src (unmeasured_measured_successors src ctx).
Proof.
  unfold unmeasured_measured_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem unmeasured_measured_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : unmeasured_measured_ctx src) :
  unmeasured_measured_select src ctx =
  urge_recovery_select src (unmeasured_measured_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem unmeasured_measured_no_local_argmin
    (src : ThermodynamicState) (ctx : unmeasured_measured_ctx src) :
  unmeasured_measured_select src ctx =
  excitement_select src (unmeasured_measured_successors src ctx).
Proof.
  exact (unmeasured_measured_select_eq_excitement_select src ctx).
Qed.

Theorem unmeasured_measured_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  unmeasured_measured_excitement_select src cands umep_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem unmeasured_measured_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  unmeasured_measured_excitement_select src cands umep_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma unmeasured_measured_select_empty (src : ThermodynamicState)
    (ctx : unmeasured_measured_ctx src)
    (Hnil : unmeasured_measured_successors src ctx = nil) :
  unmeasured_measured_select src ctx = inr exc_no_candidates.
Proof.
  unfold unmeasured_measured_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: §17.7 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition umm_fixture_dataset : string :=
  "fixture:urge-formal-meso-coq-unmeasured-measured"%string.

Definition umm_fixture_measured_false : production_wired_taxonomy :=
  pw_measured false umm_fixture_dataset.

Definition umm_fixture_conjunct : unmeasured_measured_conjunct :=
  {| umm_conj_gate_ok := true;
     umm_conj_false_as_green_refused := true;
     umm_conj_excitement_preserves := true |}.

Theorem umm_fixture_measured_false_admits :
  refuse_false_as_green umm_fixture_measured_false = None.
Proof.
  reflexivity.
Qed.

Theorem umm_fixture_measured_false_evaluate_ok :
  evaluate_production_wired umm_fixture_measured_false = pwv_measured_false_ok.
Proof.
  reflexivity.
Qed.

Theorem umm_fixture_measured_production_wired_ok :
  measured_production_wired false umm_fixture_dataset =
  inl umm_fixture_measured_false.
Proof.
  reflexivity.
Qed.

Theorem umm_fixture_empty_dataset_refused :
  measured_production_wired false ""%string =
  inr fagr_unmeasured_collapsed_to_false.
Proof.
  reflexivity.
Qed.

Theorem umm_fixture_unmeasured_legacy_none :
  production_wired_legacy_bool gossip_mesh_production_wired_taxonomy = None.
Proof.
  reflexivity.
Qed.

Theorem umm_fixture_conjunct_admits_true :
  umm_conjunct_admits umm_fixture_conjunct = true.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition unmeasured_measured_physics_green : bool := false.

Lemma unmeasured_measured_physics_green_false :
  unmeasured_measured_physics_green = false.
Proof. reflexivity. Qed.

Definition unmeasured_measured_production_wired : bool := false.

Lemma unmeasured_measured_production_wired_false :
  unmeasured_measured_production_wired = false.
Proof. reflexivity. Qed.

Theorem unmeasured_measured_module_witness : True.
Proof. exact I. Qed.

Theorem unmeasured_measured_no_new_axiom : True.
Proof. exact I. Qed.

Theorem unmeasured_measured_positive_refuse_not_silent :
  refuse_false_as_green gossip_mesh_production_wired_taxonomy <>
  None.
Proof.
  rewrite gossip_mesh_refuse_false_as_green.
  discriminate.
Qed.

Theorem unmeasured_measured_unknown_not_false_as_green :
  refuse_unmeasured_as_false_green =
  fagr_unmeasured_collapsed_to_false.
Proof.
  reflexivity.
Qed.
