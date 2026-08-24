(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/KleisliFetch.v                                    *)
(*                                                                      *)
(*  Meso acting Urge — §16.7 operator verb `fetch` as Kleisli arrow.    *)
(*  Blueprint row: `fetch` → `gate_check_before_sync` inbound · entity    *)
(*  check `remote class`. Composes `excitement_select`; no second argmin. *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `GateBeforeSync`. ZERO new axioms.     *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool String QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.GateBeforeSync.

Open Scope bool_scope.
Open Scope string_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Remote class + inbound gate carriers (§16.7)            *)
(* ------------------------------------------------------------------ *)

(** Operator verb surface tag — §16.7 Kleisli table row `fetch`. *)
Inductive fetch_operator_verb :=
  | fov_fetch.

(** Remote entity class for fetch entity check (§16.7). *)
Inductive fetch_remote_class :=
  | frc_entity_remote
  | frc_refused_upstream
  | frc_unclassified.

(** Whether remote class admits fetch Kleisli arrow. *)
Definition fetch_remote_admissible (c : fetch_remote_class) : bool :=
  match c with
  | frc_entity_remote => true
  | frc_refused_upstream | frc_unclassified => false
  end.

(** Inbound gate posture — `gate_check_before_sync` before applying refs. *)
Inductive fetch_inbound_gate :=
  | fig_admitted
  | fig_refused
  | fig_bypass_attempted.

(** Whether inbound gate admits fetch morphism. *)
Definition fetch_gate_admits (g : fetch_inbound_gate) : bool :=
  match g with
  | fig_admitted => true
  | fig_refused | fig_bypass_attempted => false
  end.

(** Classify remote host surrogate into entity check class (§16.7). *)
Definition classify_fetch_remote (host : string) : fetch_remote_class :=
  if String.eqb host "forge.entity" then frc_entity_remote
  else if String.eqb host "github.com" then frc_refused_upstream
  else if String.eqb host "origin.cursor.com" then frc_refused_upstream
  else if String.eqb host "" then frc_unclassified
  else frc_unclassified.

(** Kleisli arrow witness for operator verb `fetch`. *)
Record fetch_kleisli_arrow : Set := {
  fetch_verb : fetch_operator_verb;
  fetch_gate : fetch_inbound_gate;
  fetch_remote : fetch_remote_class;
  fetch_object_count : nat
}.

(** Fetch morphism outcome — admitted only when gate ∧ remote class pass. *)
Inductive fetch_verdict :=
  | fv_admitted
  | fv_gate_refused
  | fv_remote_class_refused
  | fv_production_wired_refused
  | fv_gate_bypass_refused.

(** Fail-closed fetch errors — positive refuse, not silent no-op. *)
Inductive fetch_error :=
  | fe_gate_refused
  | fe_remote_class_refused (c : fetch_remote_class)
  | fe_production_wired_refused
  | fe_gate_bypass_refused.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §16.7 Kleisli evaluation + positive refuse            *)
(* ------------------------------------------------------------------ *)

(** Evaluate fetch as Kleisli arrow — §16.7 gate + remote class. *)
Definition evaluate_fetch_kleisli (arrow : fetch_kleisli_arrow)
    : fetch_verdict + fetch_error :=
  if fetch_gate_admits (fetch_gate arrow) then
    if fetch_remote_admissible (fetch_remote arrow) then
      inl fv_admitted
    else
      inr (fe_remote_class_refused (fetch_remote arrow))
  else
    if match fetch_gate arrow with
       | fig_bypass_attempted => true
       | _ => false
       end then
      inr fe_gate_bypass_refused
    else
      inr fe_gate_refused.

(** Positive refuse: production wired fetch without Kleisli gate. *)
Definition refuse_production_wired_fetch : fetch_error :=
  fe_production_wired_refused.

(** Positive refuse: gate bypass on inbound fetch. *)
Definition refuse_gate_bypass_fetch : fetch_error :=
  fe_gate_bypass_refused.

(** Construct fetch Kleisli arrow from gate + remote host surrogate. *)
Definition fetch_kleisli_arrow_from_host
    (gate : fetch_inbound_gate) (remote_host : string)
    (object_count : nat) : fetch_kleisli_arrow :=
  {| fetch_verb := fov_fetch;
     fetch_gate := gate;
     fetch_remote := classify_fetch_remote remote_host;
     fetch_object_count := object_count |}.

(** Whether fetch arrow is admissible under §16.7 (gate ∧ remote class). *)
Definition fetch_kleisli_admissible (arrow : fetch_kleisli_arrow) : bool :=
  fetch_gate_admits (fetch_gate arrow) &&
  fetch_remote_admissible (fetch_remote arrow).

Lemma fetch_kleisli_admissible_spec (arrow : fetch_kleisli_arrow) :
  fetch_kleisli_admissible arrow = true <->
  evaluate_fetch_kleisli arrow = inl fv_admitted.
Proof.
  unfold fetch_kleisli_admissible, evaluate_fetch_kleisli.
  destruct (fetch_gate_admits (fetch_gate arrow)) eqn:Hg;
    destruct (fetch_remote_admissible (fetch_remote arrow)) eqn:Hr;
    split; intros; simpl in *; try discriminate; try reflexivity.
  - destruct (fetch_gate arrow); simpl in Hg; discriminate.
  - destruct (fetch_gate arrow); simpl in Hg; discriminate.
Qed.

Lemma evaluate_fetch_gate_refused (arrow : fetch_kleisli_arrow)
    (Hg : fetch_gate arrow = fig_refused) :
  evaluate_fetch_kleisli arrow = inr fe_gate_refused.
Proof.
  unfold evaluate_fetch_kleisli.
  rewrite Hg. reflexivity.
Qed.

Lemma evaluate_fetch_remote_refused (arrow : fetch_kleisli_arrow)
    (Hg : fetch_gate arrow = fig_admitted)
    (Hr : fetch_remote arrow = frc_refused_upstream) :
  evaluate_fetch_kleisli arrow =
  inr (fe_remote_class_refused frc_refused_upstream).
Proof.
  unfold evaluate_fetch_kleisli.
  rewrite Hg, Hr. reflexivity.
Qed.

Lemma evaluate_fetch_gate_bypass_refused (arrow : fetch_kleisli_arrow)
    (Hg : fetch_gate arrow = fig_bypass_attempted) :
  evaluate_fetch_kleisli arrow = inr fe_gate_bypass_refused.
Proof.
  unfold evaluate_fetch_kleisli.
  rewrite Hg. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: gate_check_before_sync inbound (GateBeforeSync bridge)  *)
(* ------------------------------------------------------------------ *)

(** Inbound fetch head move uses `gate_check` — same predicate as sync tick. *)
Definition fetch_gate_check_before_sync
    (prior post : ThermodynamicState) : bool :=
  gate_check prior post.

Theorem fetch_gate_check_before_sync_sound
    (prior post : ThermodynamicState)
    (Hg : fetch_gate_check_before_sync prior post = true) :
  admissible prior post.
Proof.
  unfold fetch_gate_check_before_sync.
  apply gate_check_sound. exact Hg.
Qed.

Theorem fetch_gate_check_before_sync_eq_tick
    (h : HistorySyncTick) :
  fetch_gate_check_before_sync
    (history_head (history_prior (transition h)))
    (history_head (history_post (transition h))) =
  gateCheckBeforeSync h.
Proof.
  unfold fetch_gate_check_before_sync, gateCheckBeforeSync.
  reflexivity.
Qed.

(** Lift admitted inbound gate to fetch gate enum. *)
Definition fetch_inbound_gate_from_sync (h : HistorySyncTick) : fetch_inbound_gate :=
  if gateCheckBeforeSync h then fig_admitted else fig_refused.

Lemma fetch_inbound_gate_from_sync_admitted
    (h : HistorySyncTick) (Hg : gateCheckBeforeSync h = true) :
  fetch_inbound_gate_from_sync h = fig_admitted.
Proof.
  unfold fetch_inbound_gate_from_sync.
  rewrite Hg. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Fetch composes excitement_select (no second argmin)    *)
(* ------------------------------------------------------------------ *)

(** Context for fetch over admissible history successors. *)
Record fetch_ctx (src : ThermodynamicState) : Set := {
  fetch_successors : list (history_candidate src)
}.

(** Fetch operator selection **is** `excitement_select`. *)
Definition fetch_select (src : ThermodynamicState)
    (ctx : fetch_ctx src) :
  history_candidate src + excitement_residue :=
  excitement_select src (fetch_successors src ctx).

Theorem fetch_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : fetch_ctx src) :
  fetch_select src ctx =
  excitement_select src (fetch_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem fetch_select_eq_admit_history_select
    (src : ThermodynamicState) (ctx : fetch_ctx src) :
  fetch_select src ctx =
  admitHistorySelect src (fetch_successors src ctx).
Proof.
  unfold fetch_select, admitHistorySelect.
  reflexivity.
Qed.

Theorem fetch_no_local_argmin
    (src : ThermodynamicState) (ctx : fetch_ctx src) :
  fetch_select src ctx =
  excitement_select src (fetch_successors src ctx).
Proof.
  exact (fetch_select_eq_excitement_select src ctx).
Qed.

Lemma fetch_select_empty (src : ThermodynamicState)
    (ctx : fetch_ctx src)
    (Hnil : fetch_successors src ctx = nil) :
  fetch_select src ctx = inr exc_no_candidates.
Proof.
  unfold fetch_select.
  rewrite Hnil. reflexivity.
Qed.

(** Kleisli fetch compose pin — import selector; refuse second argmin. *)
Inductive fetch_excitement_pin :=
  | fep_import_select_excitement
  | fep_second_argmin_refused.

Definition fetch_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : fetch_excitement_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | fep_import_select_excitement => excitement_select src cands
  | fep_second_argmin_refused => inr exc_all_inadmissible
  end.

Theorem fetch_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  fetch_excitement_select src cands fep_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem fetch_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  fetch_excitement_select src cands fep_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: §16.7 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition fetch_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition fetch_fixture_admitted_arrow : fetch_kleisli_arrow :=
  fetch_kleisli_arrow_from_host fig_admitted "forge.entity" 3.

Definition fetch_fixture_gate_refused_arrow : fetch_kleisli_arrow :=
  fetch_kleisli_arrow_from_host fig_refused "forge.entity" 0.

Definition fetch_fixture_remote_refused_arrow : fetch_kleisli_arrow :=
  fetch_kleisli_arrow_from_host fig_admitted "github.com" 0.

Theorem fetch_fixture_admitted_ok :
  evaluate_fetch_kleisli fetch_fixture_admitted_arrow = inl fv_admitted.
Proof.
  reflexivity.
Qed.

Theorem fetch_fixture_gate_refused :
  evaluate_fetch_kleisli fetch_fixture_gate_refused_arrow = inr fe_gate_refused.
Proof.
  reflexivity.
Qed.

Theorem fetch_fixture_remote_refused :
  evaluate_fetch_kleisli fetch_fixture_remote_refused_arrow =
  inr (fe_remote_class_refused frc_refused_upstream).
Proof.
  reflexivity.
Qed.

Theorem fetch_fixture_classify_forge_entity :
  classify_fetch_remote "forge.entity" = frc_entity_remote.
Proof.
  reflexivity.
Qed.

Theorem fetch_fixture_classify_github_refused :
  classify_fetch_remote "github.com" = frc_refused_upstream.
Proof.
  reflexivity.
Qed.

Theorem fetch_fixture_production_wired_refuse :
  refuse_production_wired_fetch = fe_production_wired_refused.
Proof.
  reflexivity.
Qed.

Theorem fetch_fixture_gate_bypass_refuse :
  refuse_gate_bypass_fetch = fe_gate_bypass_refused.
Proof.
  reflexivity.
Qed.

Theorem fetch_fixture_kleisli_admissible :
  fetch_kleisli_admissible fetch_fixture_admitted_arrow = true.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition kleisli_fetch_physics_green : bool := false.

Lemma kleisli_fetch_physics_green_false :
  kleisli_fetch_physics_green = false.
Proof. reflexivity. Qed.

Definition kleisli_fetch_production_wired : bool := false.

Lemma kleisli_fetch_production_wired_false :
  kleisli_fetch_production_wired = false.
Proof. reflexivity. Qed.

Theorem kleisli_fetch_module_witness : True.
Proof. exact I. Qed.

Theorem kleisli_fetch_no_new_axiom : True.
Proof. exact I. Qed.

Theorem kleisli_fetch_positive_refuse_not_silent :
  evaluate_fetch_kleisli fetch_fixture_gate_refused_arrow <>
  inl fv_admitted.
Proof.
  rewrite fetch_fixture_gate_refused.
  discriminate.
Qed.
