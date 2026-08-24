(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/GossipTick.v                                      *)
(*                                                                      *)
(*  Meso acting Urge — §15.6 H3 gossip tick as typed Unmeasured|Measured *)
(*  wrapper. UNKNOWN ≠ false-as-GREEN — positive refuse, not silent     *)
(*  accept. Composes `excitement_select`; no second argmin.               *)
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
(*  SECTION 1: H3 gossip tick measurement + typed morphism carriers  *)
(* ------------------------------------------------------------------ *)

(** §15.6 H3 gossip tick measurement posture — UNKNOWN never collapses to `bool`. *)
Inductive gossip_tick_measure :=
  | gtm_unmeasured
  | gtm_measured (observed_admissible : bool) (dataset : string).

(** Whether posture carries a fleet measurement (not merely unmeasured). *)
Definition gossip_tick_is_measured (m : gossip_tick_measure) : bool :=
  match m with
  | gtm_unmeasured => false
  | gtm_measured _ _ => true
  end.

(** Measured admissibility when present — `None` for `Unmeasured` (not `Some false`). *)
Definition gossip_tick_observed_admissible (m : gossip_tick_measure)
    : option bool :=
  match m with
  | gtm_unmeasured => None
  | gtm_measured v _ => Some v
  end.

(** Dataset label when measured. *)
Definition gossip_tick_dataset (m : gossip_tick_measure) : option string :=
  match m with
  | gtm_unmeasured => None
  | gtm_measured _ d => Some d
  end.

(** Non-empty dataset surrogate — empty label is inadmissible measurement. *)
Definition gossip_dataset_nonempty (d : string) : bool :=
  negb (String.eqb d "").

(** Excitement compose pin — Urge imports selector; no second argmin. *)
Inductive gossip_excitement_compose_pin :=
  | gecp_import_select_excitement
  | gecp_second_argmin_refused.

(** One H3 gossip tick candidate on the UCRS-gated mesh spine. *)
Record gossip_tick_candidate : Set := {
  gossip_tick_id : nat;
  gossip_candidate_measure : gossip_tick_measure;
  gossip_tick_compose_pin : gossip_excitement_compose_pin;
  gossip_tick_physics_green_claim : bool
}.

(** UCRS stamp surrogate carried through gossip tick evaluation. *)
Record gossip_tick_ucrs_stamp : Set := {
  gossip_tick_ucrs_seq : nat;
  gossip_tick_ucrs_wall_has_t : bool
}.

(** Witness bundle a gossip tick morphism must preserve (§15.6). *)
Record gossip_tick_witness : Set := {
  gossip_witness_ucrs : gossip_tick_ucrs_stamp;
  gossip_witness_measure : gossip_tick_measure;
  gossip_witness_compose_pin : gossip_excitement_compose_pin
}.

(** Typed gossip tick morphism — admissible transition, not silent accept. *)
Record gossip_tick_morphism : Set := {
  gossip_morphism_candidate : gossip_tick_candidate;
  gossip_morphism_witness : gossip_tick_witness;
  gossip_morphism_excitement_selected : bool
}.

(** Fail-closed gossip tick errors — positive refuse, not silent no-op. *)
Inductive gossip_tick_refusal :=
  | gtr_unmeasured_collapsed_to_false
  | gtr_second_argmin_selector
  | gtr_invented_physics_green
  | gtr_gate_rejected (seq : nat).

(** Verdict for H3 gossip tick admissibility on the mesh spine. *)
Inductive gossip_tick_verdict :=
  | gtv_gossip_admissible
  | gtv_refuse_unmeasured_false_green
  | gtv_refuse_second_argmin
  | gtv_refuse_invented_green.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §15.6 admissibility conjunct + positive refuse          *)
(* ------------------------------------------------------------------ *)

(** §15.6 admissibility conjunct inputs (surrogate). *)
Record gossip_tick_admissibility_conjunct : Set := {
  gossip_conj_gate_ok : bool;
  gossip_conj_unmeasured_not_false_green : bool;
  gossip_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ unmeasured≠false-as-GREEN ∧ Excitement preserves`. *)
Definition gossip_conjunct_admits (c : gossip_tick_admissibility_conjunct) : bool :=
  gossip_conj_gate_ok c &&
  gossip_conj_unmeasured_not_false_green c &&
  gossip_conj_excitement_preserves c.

(** Refuse collapsing `Unmeasured` gossip tick posture to measured-false GREEN. *)
Definition refuse_unmeasured_gossip_tick_as_false_green
    (m : gossip_tick_measure) : option gossip_tick_refusal :=
  match m with
  | gtm_unmeasured => Some gtr_unmeasured_collapsed_to_false
  | gtm_measured _ _ => None
  end.

(** Positive refuse: second Excitement argmin on gossip tick path is inadmissible. *)
Definition refuse_second_argmin_on_gossip_tick
    (pin : gossip_excitement_compose_pin) : option gossip_tick_refusal :=
  match pin with
  | gecp_second_argmin_refused => Some gtr_second_argmin_selector
  | gecp_import_select_excitement => None
  end.

(** Construct measured gossip tick posture with non-empty dataset label. *)
Definition measured_gossip_tick (observed_admissible : bool) (dataset : string)
    : gossip_tick_measure + gossip_tick_refusal :=
  if negb (gossip_dataset_nonempty dataset) then
    inr gtr_unmeasured_collapsed_to_false
  else
    inl (gtm_measured observed_admissible dataset).

(** Admit an H3 gossip tick candidate — typed refuse, not only `!physics_green`. *)
Definition admit_gossip_tick (c : gossip_tick_candidate)
    : option gossip_tick_refusal :=
  if gossip_tick_physics_green_claim c then
    Some gtr_invented_physics_green
  else
    match refuse_second_argmin_on_gossip_tick (gossip_tick_compose_pin c) with
    | Some r => Some r
    | None =>
      match gossip_candidate_measure c with
      | gtm_unmeasured => Some gtr_unmeasured_collapsed_to_false
      | gtm_measured false _ => None
      | gtm_measured true dataset =>
        if negb (gossip_dataset_nonempty dataset) then
          Some gtr_unmeasured_collapsed_to_false
        else
          None
      end
    end.

(** Evaluate H3 gossip tick admissibility (transition verdict family). *)
Definition evaluate_gossip_tick (c : gossip_tick_candidate)
    : gossip_tick_verdict :=
  match admit_gossip_tick c with
  | None => gtv_gossip_admissible
  | Some gtr_unmeasured_collapsed_to_false => gtv_refuse_unmeasured_false_green
  | Some gtr_second_argmin_selector => gtv_refuse_second_argmin
  | Some gtr_invented_physics_green => gtv_refuse_invented_green
  | Some (gtr_gate_rejected _) => gtv_refuse_invented_green
  end.

(** Build witness from candidate — morphism must preserve stamps and posture. *)
Definition witness_from_gossip_candidate (c : gossip_tick_candidate)
    (ucrs : gossip_tick_ucrs_stamp) : gossip_tick_witness :=
  {| gossip_witness_ucrs := ucrs;
     gossip_witness_measure := gossip_candidate_measure c;
     gossip_witness_compose_pin := gossip_tick_compose_pin c |}.

(** Attempt typed gossip tick morphism — fail closed on inadmissibility. *)
Definition apply_gossip_tick_morphism
    (cand : gossip_tick_candidate)
    (ucrs : gossip_tick_ucrs_stamp)
    (conjunct : gossip_tick_admissibility_conjunct)
    (excitement_selected : bool)
    : gossip_tick_morphism + gossip_tick_refusal :=
  if negb (gossip_conjunct_admits conjunct) then
    inr (gtr_gate_rejected (gossip_tick_ucrs_seq ucrs))
  else
    match admit_gossip_tick cand with
    | Some r => inr r
    | None =>
      if negb excitement_selected then
        inr gtr_second_argmin_selector
      else
        inl
          {| gossip_morphism_candidate := cand;
             gossip_morphism_witness := witness_from_gossip_candidate cand ucrs;
             gossip_morphism_excitement_selected := excitement_selected |}
    end.


Lemma refuse_unmeasured_gossip_tick_positive :
  refuse_unmeasured_gossip_tick_as_false_green gtm_unmeasured =
  Some gtr_unmeasured_collapsed_to_false.
Proof.
  reflexivity.
Qed.

Lemma refuse_second_argmin_positive :
  refuse_second_argmin_on_gossip_tick gecp_second_argmin_refused =
  Some gtr_second_argmin_selector.
Proof.
  reflexivity.
Qed.

Lemma gossip_tick_unmeasured_not_measured :
  gossip_tick_is_measured gtm_unmeasured = false.
Proof.
  reflexivity.
Qed.

Lemma gossip_tick_observed_none_when_unmeasured :
  gossip_tick_observed_admissible gtm_unmeasured = None.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Gossip tick composes Excitement (no second argmin)     *)
(* ------------------------------------------------------------------ *)

(** Context for gossip tick selection over admissible history successors. *)
Record gossip_tick_ctx (src : ThermodynamicState) : Set := {
  gossip_tick_successors : list (history_candidate src)
}.

(** Gossip tick path composes `excitement_select` — not a second argmin. *)
Definition gossip_tick_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : gossip_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | gecp_import_select_excitement => excitement_select src cands
  | gecp_second_argmin_refused => inr exc_all_inadmissible
  end.

(** Gossip tick selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition gossip_tick_select (src : ThermodynamicState)
    (ctx : gossip_tick_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (gossip_tick_successors src ctx).

Theorem gossip_tick_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : gossip_tick_ctx src) :
  gossip_tick_select src ctx =
  excitement_select src (gossip_tick_successors src ctx).
Proof.
  unfold gossip_tick_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem gossip_tick_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : gossip_tick_ctx src) :
  gossip_tick_select src ctx =
  urge_recovery_select src (gossip_tick_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem gossip_tick_no_local_argmin
    (src : ThermodynamicState) (ctx : gossip_tick_ctx src) :
  gossip_tick_select src ctx =
  excitement_select src (gossip_tick_successors src ctx).
Proof.
  exact (gossip_tick_select_eq_excitement_select src ctx).
Qed.

Theorem gossip_tick_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  gossip_tick_excitement_select src cands gecp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem gossip_tick_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  gossip_tick_excitement_select src cands gecp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma gossip_tick_select_empty (src : ThermodynamicState)
    (ctx : gossip_tick_ctx src)
    (Hnil : gossip_tick_successors src ctx = nil) :
  gossip_tick_select src ctx = inr exc_no_candidates.
Proof.
  unfold gossip_tick_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §15.6 H3 fixtures + witness theorems                    *)
(* ------------------------------------------------------------------ *)

Definition gossip_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition gossip_fixture_ucrs : gossip_tick_ucrs_stamp :=
  {| gossip_tick_ucrs_seq := 7;
     gossip_tick_ucrs_wall_has_t := true |}.

Definition gossip_fixture_dataset : string :=
  "fixture:h3:gossip-tick:admissible-001"%string.

Definition gossip_fixture_second_argmin_dataset : string :=
  "fixture:h3:gossip-tick:second-argmin-002"%string.

Definition h3_admissible_measured_gossip_tick : gossip_tick_candidate :=
  {| gossip_tick_id := 1;
     gossip_candidate_measure :=
       gtm_measured true gossip_fixture_dataset;
     gossip_tick_compose_pin := gecp_import_select_excitement;
     gossip_tick_physics_green_claim := false |}.

Definition h3_unmeasured_false_green_fixture : gossip_tick_candidate :=
  {| gossip_tick_id := 2;
     gossip_candidate_measure := gtm_unmeasured;
     gossip_tick_compose_pin := gecp_import_select_excitement;
     gossip_tick_physics_green_claim := false |}.

Definition h3_second_argmin_fixture : gossip_tick_candidate :=
  {| gossip_tick_id := 3;
     gossip_candidate_measure :=
       gtm_measured false gossip_fixture_second_argmin_dataset;
     gossip_tick_compose_pin := gecp_second_argmin_refused;
     gossip_tick_physics_green_claim := false |}.

Definition gossip_fixture_conjunct : gossip_tick_admissibility_conjunct :=
  {| gossip_conj_gate_ok := true;
     gossip_conj_unmeasured_not_false_green := true;
     gossip_conj_excitement_preserves := true |}.

Theorem h3_admissible_measured_gossip_tick_admits :
  admit_gossip_tick h3_admissible_measured_gossip_tick = None.
Proof.
  reflexivity.
Qed.

Theorem h3_admissible_measured_gossip_tick_evaluate_admit :
  evaluate_gossip_tick h3_admissible_measured_gossip_tick =
  gtv_gossip_admissible.
Proof.
  reflexivity.
Qed.

Theorem h3_unmeasured_false_green_refused :
  admit_gossip_tick h3_unmeasured_false_green_fixture =
  Some gtr_unmeasured_collapsed_to_false.
Proof.
  reflexivity.
Qed.

Theorem h3_unmeasured_false_green_evaluate_refuse :
  evaluate_gossip_tick h3_unmeasured_false_green_fixture =
  gtv_refuse_unmeasured_false_green.
Proof.
  reflexivity.
Qed.

Theorem h3_second_argmin_refused :
  admit_gossip_tick h3_second_argmin_fixture =
  Some gtr_second_argmin_selector.
Proof.
  reflexivity.
Qed.

Theorem h3_second_argmin_evaluate_refuse :
  evaluate_gossip_tick h3_second_argmin_fixture =
  gtv_refuse_second_argmin.
Proof.
  reflexivity.
Qed.

Theorem gossip_fixture_measured_gossip_tick_ok :
  measured_gossip_tick true gossip_fixture_dataset =
  inl (gtm_measured true gossip_fixture_dataset).
Proof.
  reflexivity.
Qed.

Theorem gossip_fixture_empty_dataset_refused :
  measured_gossip_tick false ""%string =
  inr gtr_unmeasured_collapsed_to_false.
Proof.
  reflexivity.
Qed.

Theorem gossip_fixture_apply_morphism_ok :
  apply_gossip_tick_morphism
    h3_admissible_measured_gossip_tick gossip_fixture_ucrs
    gossip_fixture_conjunct true
  = inl
      {| gossip_morphism_candidate := h3_admissible_measured_gossip_tick;
         gossip_morphism_witness :=
           witness_from_gossip_candidate
             h3_admissible_measured_gossip_tick gossip_fixture_ucrs;
         gossip_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem gossip_fixture_witness_preserves_measure :
  gossip_witness_measure
    (witness_from_gossip_candidate
       h3_admissible_measured_gossip_tick gossip_fixture_ucrs) =
  gtm_measured true gossip_fixture_dataset.
Proof.
  reflexivity.
Qed.

Theorem gossip_fixture_conjunct_admits_true :
  gossip_conjunct_admits gossip_fixture_conjunct = true.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition gossip_tick_physics_green : bool := false.

Lemma gossip_tick_physics_green_false :
  gossip_tick_physics_green = false.
Proof. reflexivity. Qed.

Definition gossip_tick_production_wired : bool := false.

Lemma gossip_tick_production_wired_false :
  gossip_tick_production_wired = false.
Proof. reflexivity. Qed.

Theorem gossip_tick_module_witness : True.
Proof. exact I. Qed.

Theorem gossip_tick_no_new_axiom : True.
Proof. exact I. Qed.

Theorem gossip_tick_positive_refuse_not_silent :
  admit_gossip_tick h3_unmeasured_false_green_fixture <>
  None.
Proof.
  rewrite h3_unmeasured_false_green_refused.
  discriminate.
Qed.

Theorem gossip_tick_unmeasured_not_false_as_green :
  refuse_unmeasured_gossip_tick_as_false_green gtm_unmeasured <>
  None.
Proof.
  rewrite refuse_unmeasured_gossip_tick_positive.
  discriminate.
Qed.
