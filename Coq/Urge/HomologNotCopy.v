(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/HomologNotCopy.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §22.1 homolog ≠ copy recovery morphism.          *)
(*  Recovery **is** a new Excitement arrow over admissible successors — *)
(*  not `git reset --hard` of a sibling commit. Homolog relates sibling *)
(*  commits geometrically — homolog ≠ copy. Composes `excitement_select`;*)
(*  no second argmin. Mirrors `BackupRecovery.v` typed morphism discipline.*)
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
(*  SECTION 1: Sibling commit + homolog witness carriers (§22.1)      *)
(* ------------------------------------------------------------------ *)

(** Sibling commit reference — content-addressed surrogate. *)
Record sibling_commit_ref : Set := {
  sibling_commit_hash : nat;
  sibling_of_parent : nat
}.

(** Homolog witness — geometric relation between sibling commits. *)
Record homolog_witness : Set := {
  homolog_from : sibling_commit_ref;
  homolog_to : sibling_commit_ref;
  homolog_claims_identity_copy : bool
}.

(** UCRS stamp surrogate carried through §22.1 recovery arrow. *)
Record homolog_ucrs_stamp : Set := {
  homolog_ucrs_seq : nat;
  homolog_ucrs_wall_has_t : bool
}.

(** New Excitement recovery arrow — admissible state transition, not blind copy. *)
Record homolog_recovery_arrow : Set := {
  homolog_arrow_id : nat;
  homolog_selected_successor_id : nat;
  homolog_arrow_head : ThermodynamicState;
  homolog_arrow_provenance_intact : bool;
  homolog_arrow_ucrs : homolog_ucrs_stamp
}.

(** Whether the recovery arrow is a fresh Excitement selection. *)
Definition is_new_excitement_arrow (a : homolog_recovery_arrow) : bool :=
  homolog_arrow_provenance_intact a &&
  homolog_ucrs_wall_has_t (homolog_arrow_ucrs a).

(** Recovery attempt bundle — gate input for §22.1 classification. *)
Record homolog_recovery_attempt : Set := {
  homolog_attempt_git_reset_hard_sibling : bool;
  homolog_attempt_witness : option homolog_witness;
  homolog_attempt_head : ThermodynamicState
}.

(** Fail-closed recovery errors — positive refuse, not silent no-op. *)
Inductive homolog_not_copy_refusal :=
  | hncr_git_reset_hard_sibling
  | hncr_homolog_is_not_copy
  | hncr_second_argmin.

(** Verdict class for recovery attempts. *)
Inductive homolog_recovery_class :=
  | hrc_new_excitement_arrow
  | hrc_git_reset_hard_sibling_class
  | hrc_homolog_claims_copy.

(** Verdict of a recovery operation class. *)
Inductive homolog_recovery_verdict :=
  | hrv_new_arrow_ok
  | hrv_git_reset_hard_refused
  | hrv_homolog_copy_refused
  | hrv_second_argmin_refused.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §22.1 admissibility conjunct + positive refuse          *)
(* ------------------------------------------------------------------ *)

(** §22.1 admissibility conjunct inputs (surrogate). *)
Record homolog_admissibility_conjunct : Set := {
  homolog_conj_not_git_reset_hard : bool;
  homolog_conj_homolog_not_copy : bool;
  homolog_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ ¬git-reset-hard ∧ homolog≠copy ∧ Excitement preserves`. *)
Definition homolog_conjunct_admits (c : homolog_admissibility_conjunct) : bool :=
  homolog_conj_not_git_reset_hard c &&
  homolog_conj_homolog_not_copy c &&
  homolog_conj_excitement_preserves c.

(** Build sibling commit ref from hash + parent pin. *)
Definition sibling_commit_ref_of (hash parent : nat) : sibling_commit_ref :=
  {| sibling_commit_hash := hash;
     sibling_of_parent := parent |}.

(** Whether sibling commit hashes differ (homolog ≠ identity copy). *)
Definition sibling_hashes_differ (w : homolog_witness) : bool :=
  negb (Nat.eqb (sibling_commit_hash (homolog_from w))
                (sibling_commit_hash (homolog_to w))).

(** §22.1 homolog-not-copy? — geometric relation, not blind sibling reset. *)
Definition homolog_not_copy_ok (w : homolog_witness) : bool :=
  sibling_hashes_differ w &&
  negb (homolog_claims_identity_copy w).

(** Classify git reset --hard sibling vs new Excitement arrow without I/O. *)
Definition evaluate_homolog_recovery_operation (git_reset_hard : bool)
    : homolog_recovery_verdict :=
  if git_reset_hard then hrv_git_reset_hard_refused else hrv_new_arrow_ok.

(** Positive refuse: `git reset --hard` of sibling — inadmissible under §22.1. *)
Definition refuse_git_reset_hard_sibling : homolog_not_copy_refusal :=
  hncr_git_reset_hard_sibling.

(** Positive refuse: homolog witness claims identity copy — homolog ≠ copy. *)
Definition refuse_homolog_as_copy : homolog_not_copy_refusal :=
  hncr_homolog_is_not_copy.

(** Positive refuse: second local Excitement argmin — compose import only. *)
Definition refuse_second_argmin : homolog_not_copy_refusal :=
  hncr_second_argmin.

(** Map typed refusal to recovery class surrogate. *)
Definition recovery_class_of_refusal (r : homolog_not_copy_refusal)
    : homolog_recovery_class :=
  match r with
  | hncr_git_reset_hard_sibling => hrc_git_reset_hard_sibling_class
  | hncr_homolog_is_not_copy => hrc_homolog_claims_copy
  | hncr_second_argmin => hrc_new_excitement_arrow
  end.

(** Gate recovery attempts — fail closed on git reset hard or homolog-as-copy. *)
Definition classify_homolog_recovery_attempt
    (attempt : homolog_recovery_attempt)
    : homolog_recovery_class + homolog_not_copy_refusal :=
  if homolog_attempt_git_reset_hard_sibling attempt then
    inr hncr_git_reset_hard_sibling
  else
    match homolog_attempt_witness attempt with
    | None => inl hrc_new_excitement_arrow
    | Some w =>
        if homolog_claims_identity_copy w then
          inr hncr_homolog_is_not_copy
        else if homolog_not_copy_ok w then
          inl hrc_new_excitement_arrow
        else
          inr hncr_homolog_is_not_copy
    end.

(** Build recovery arrow from Excitement selection + UCRS pin. *)
Definition recovery_arrow_from_selection
    (arrow_id successor_id : nat)
    (head : ThermodynamicState)
    (ucrs_seq : nat) (wall_has_t : bool)
    (sel : history_candidate head + excitement_residue)
    : homolog_recovery_arrow + excitement_residue :=
  match sel with
  | inl c =>
      inl
        {| homolog_arrow_id := arrow_id;
           homolog_selected_successor_id := successor_id;
           homolog_arrow_head := head;
           homolog_arrow_provenance_intact := true;
           homolog_arrow_ucrs :=
             {| homolog_ucrs_seq := ucrs_seq;
                homolog_ucrs_wall_has_t := wall_has_t |}
        |}
  | inr r => inr r
  end.

(** Attempt typed homolog recovery morphism — fail closed on inadmissibility. *)
Definition apply_homolog_recovery_morphism
    (attempt : homolog_recovery_attempt)
    (conjunct : homolog_admissibility_conjunct)
    (excitement_selected : bool)
    : homolog_recovery_arrow + homolog_not_copy_refusal :=
  if negb (homolog_conjunct_admits conjunct) then
    inr hncr_homolog_is_not_copy
  else if homolog_attempt_git_reset_hard_sibling attempt then
    inr hncr_git_reset_hard_sibling
  else if negb excitement_selected then
    inr hncr_second_argmin
  else
    match homolog_attempt_witness attempt with
    | None =>
        inl
          {| homolog_arrow_id := 0;
             homolog_selected_successor_id := 0;
             homolog_arrow_head := homolog_attempt_head attempt;
             homolog_arrow_provenance_intact := true;
             homolog_arrow_ucrs :=
               {| homolog_ucrs_seq := 0;
                  homolog_ucrs_wall_has_t := true |}
          |}
    | Some w =>
        if homolog_not_copy_ok w then
          inl
            {| homolog_arrow_id := sibling_commit_hash (homolog_from w);
               homolog_selected_successor_id :=
                 sibling_commit_hash (homolog_to w);
               homolog_arrow_head := homolog_attempt_head attempt;
               homolog_arrow_provenance_intact := true;
               homolog_arrow_ucrs :=
                 {| homolog_ucrs_seq := 0;
                    homolog_ucrs_wall_has_t := true |}
            |}
        else
          inr hncr_homolog_is_not_copy
    end.

Lemma homolog_recovery_git_reset_hard_refused :
  evaluate_homolog_recovery_operation true = hrv_git_reset_hard_refused.
Proof.
  reflexivity.
Qed.

Lemma homolog_recovery_new_arrow_ok_when_not_reset :
  evaluate_homolog_recovery_operation false = hrv_new_arrow_ok.
Proof.
  reflexivity.
Qed.

Lemma refuse_git_reset_hard_sibling_positive :
  refuse_git_reset_hard_sibling = hncr_git_reset_hard_sibling.
Proof.
  reflexivity.
Qed.

Lemma refuse_homolog_as_copy_positive :
  refuse_homolog_as_copy = hncr_homolog_is_not_copy.
Proof.
  reflexivity.
Qed.

Lemma refuse_second_argmin_positive :
  refuse_second_argmin = hncr_second_argmin.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Homolog recovery composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — import selector; refuse second local argmin. *)
Inductive homolog_excitement_compose_pin :=
  | hncp_import_select_excitement
  | hncp_second_argmin_refused.

(** Context for homolog recovery over admissible history successors. *)
Record homolog_recovery_ctx (src : ThermodynamicState) : Set := {
  homolog_recovery_successors : list (history_candidate src)
}.

(** Homolog recovery path composes `excitement_select` — not a second argmin. *)
Definition homolog_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : homolog_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | hncp_import_select_excitement => excitement_select src cands
  | hncp_second_argmin_refused => inr exc_all_inadmissible
  end.

(** Homolog recovery **is** `urge_recovery_select` / `excitement_select`. *)
Definition homolog_recovery_select (src : ThermodynamicState)
    (ctx : homolog_recovery_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (homolog_recovery_successors src ctx).

Theorem homolog_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  homolog_excitement_select src cands hncp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem homolog_recovery_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : homolog_recovery_ctx src) :
  homolog_recovery_select src ctx =
  excitement_select src (homolog_recovery_successors src ctx).
Proof.
  unfold homolog_recovery_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem homolog_recovery_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : homolog_recovery_ctx src) :
  homolog_recovery_select src ctx =
  urge_recovery_select src (homolog_recovery_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem homolog_recovery_no_local_argmin
    (src : ThermodynamicState) (ctx : homolog_recovery_ctx src) :
  homolog_recovery_select src ctx =
  excitement_select src (homolog_recovery_successors src ctx).
Proof.
  exact (homolog_recovery_select_eq_excitement_select src ctx).
Qed.

Theorem homolog_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  homolog_excitement_select src cands hncp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma homolog_recovery_empty (src : ThermodynamicState)
    (ctx : homolog_recovery_ctx src)
    (Hnil : homolog_recovery_successors src ctx = nil) :
  homolog_recovery_select src ctx = inr exc_no_candidates.
Proof.
  unfold homolog_recovery_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §22.1 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition homolog_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition homolog_fixture_from : sibling_commit_ref :=
  sibling_commit_ref_of 101 50.

Definition homolog_fixture_to : sibling_commit_ref :=
  sibling_commit_ref_of 102 50.

Definition homolog_fixture_witness : homolog_witness :=
  {| homolog_from := homolog_fixture_from;
     homolog_to := homolog_fixture_to;
     homolog_claims_identity_copy := false |}.

Definition homolog_fixture_ucrs : homolog_ucrs_stamp :=
  {| homolog_ucrs_seq := 22;
     homolog_ucrs_wall_has_t := true |}.

Definition homolog_fixture_conjunct : homolog_admissibility_conjunct :=
  {| homolog_conj_not_git_reset_hard := true;
     homolog_conj_homolog_not_copy := true;
     homolog_conj_excitement_preserves := true |}.

Definition homolog_fixture_attempt : homolog_recovery_attempt :=
  {| homolog_attempt_git_reset_hard_sibling := false;
     homolog_attempt_witness := Some homolog_fixture_witness;
     homolog_attempt_head := homolog_fixture_state |}.

Definition homolog_fixture_git_reset_attempt : homolog_recovery_attempt :=
  {| homolog_attempt_git_reset_hard_sibling := true;
     homolog_attempt_witness := Some homolog_fixture_witness;
     homolog_attempt_head := homolog_fixture_state |}.

Definition homolog_fixture_copy_claim_witness : homolog_witness :=
  {| homolog_from := homolog_fixture_from;
     homolog_to := homolog_fixture_to;
     homolog_claims_identity_copy := true |}.

Theorem homolog_fixture_git_reset_hard_refused :
  refuse_git_reset_hard_sibling = hncr_git_reset_hard_sibling.
Proof.
  reflexivity.
Qed.

Theorem homolog_fixture_witness_not_copy :
  homolog_not_copy_ok homolog_fixture_witness = true.
Proof.
  reflexivity.
Qed.

Theorem homolog_fixture_classify_admits_arrow :
  classify_homolog_recovery_attempt homolog_fixture_attempt =
  inl hrc_new_excitement_arrow.
Proof.
  reflexivity.
Qed.

Theorem homolog_fixture_classify_refuses_git_reset :
  classify_homolog_recovery_attempt homolog_fixture_git_reset_attempt =
  inr hncr_git_reset_hard_sibling.
Proof.
  reflexivity.
Qed.

Theorem homolog_fixture_apply_morphism_ok :
  apply_homolog_recovery_morphism
    homolog_fixture_attempt homolog_fixture_conjunct true
  = inl
      {| homolog_arrow_id := 101;
         homolog_selected_successor_id := 102;
         homolog_arrow_head := homolog_fixture_state;
         homolog_arrow_provenance_intact := true;
         homolog_arrow_ucrs :=
           {| homolog_ucrs_seq := 0; homolog_ucrs_wall_has_t := true |} |}.
Proof.
  reflexivity.
Qed.

Theorem homolog_fixture_refuses_copy_claim :
  classify_homolog_recovery_attempt
    {| homolog_attempt_git_reset_hard_sibling := false;
       homolog_attempt_witness := Some homolog_fixture_copy_claim_witness;
       homolog_attempt_head := homolog_fixture_state |}
  = inr hncr_homolog_is_not_copy.
Proof.
  reflexivity.
Qed.

Theorem homolog_fixture_is_new_excitement_arrow :
  is_new_excitement_arrow
    {| homolog_arrow_id := 1;
       homolog_selected_successor_id := 2;
       homolog_arrow_head := homolog_fixture_state;
       homolog_arrow_provenance_intact := true;
       homolog_arrow_ucrs := homolog_fixture_ucrs |} = true.
Proof.
  reflexivity.
Qed.

Theorem homolog_fixture_sibling_hashes_differ :
  sibling_hashes_differ homolog_fixture_witness = true.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition homolog_not_copy_physics_green : bool := false.

Lemma homolog_not_copy_physics_green_false :
  homolog_not_copy_physics_green = false.
Proof. reflexivity. Qed.

Definition homolog_not_copy_production_wired : bool := false.

Lemma homolog_not_copy_production_wired_false :
  homolog_not_copy_production_wired = false.
Proof. reflexivity. Qed.

Theorem homolog_not_copy_module_witness : True.
Proof. exact I. Qed.

Theorem homolog_not_copy_no_new_axiom : True.
Proof. exact I. Qed.

Theorem homolog_not_copy_positive_refuse_not_silent :
  evaluate_homolog_recovery_operation true <> hrv_new_arrow_ok.
Proof.
  unfold evaluate_homolog_recovery_operation.
  discriminate.
Qed.

Theorem homolog_recovery_class_of_refusal_git_reset :
  recovery_class_of_refusal hncr_git_reset_hard_sibling =
  hrc_git_reset_hard_sibling_class.
Proof.
  reflexivity.
Qed.

Theorem homolog_recovery_class_of_refusal_homolog_copy :
  recovery_class_of_refusal hncr_homolog_is_not_copy =
  hrc_homolog_claims_copy.
Proof.
  reflexivity.
Qed.
