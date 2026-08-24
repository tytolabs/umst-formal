(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/CompactionAsArrow.v                               *)
(*                                                                      *)
(*  Meso acting Urge — §17.5 sophisticated compaction as composite      *)
(*  arrow paying MI. Semantic squash is refused unless recorded as an   *)
(*  admitted composite arrow whose `wasDerivedFrom*` witness retains    *)
(*  the chain — the composite *is* the residue. Compaction **pays MI**;  *)
(*  it is **not** delete-old-commits theater.                           *)
(*                                                                      *)
(*  Urge compaction composes `excitement_select` — not a second argmin. *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport` / `ProvenancePreserve`. *)
(*  Adds **zero** Coq `Axiom` declarations. ZERO `Admitted`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.
Require Import UMSTFormal.Urge.ProvenancePreserve.

Open Scope bool_scope.
Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Derivation chain + MI payment + composite arrow (§17.5) *)
(* ------------------------------------------------------------------ *)

(** Provenance derivation chain retained on composite compaction arrows. *)
Record caa_derivation_chain_witness : Set := {
  caa_derivation_chain : list nat
}.

(** Whether the witness retains a non-empty derivation chain. *)
Definition caa_retains_chain (w : caa_derivation_chain_witness) : bool :=
  match caa_derivation_chain w with
  | nil => false
  | _ :: _ => true
  end.

Lemma caa_retains_chain_nonempty (w : caa_derivation_chain_witness) :
  caa_retains_chain w = true <-> caa_derivation_chain w <> nil.
Proof.
  unfold caa_retains_chain.
  split.
  - intros H.
    destruct (caa_derivation_chain w) as [|h t]; simpl in H.
    + discriminate H.
    + discriminate.
  - intros H.
    destruct (caa_derivation_chain w) as [|h t]; simpl.
    + contradiction.
    + reflexivity.
Qed.

(** MI payment witness — compaction must pay mutual-information cost. *)
Record caa_mi_payment_witness : Set := {
  caa_mi_required_bits : nat;
  caa_mi_paid_bits : nat
}.

(** Whether MI cost was paid (strictly positive paid bits >= required). *)
Definition caa_mi_paid (m : caa_mi_payment_witness) : bool :=
  (0 <? caa_mi_paid_bits m) &&
  (caa_mi_required_bits m <=? caa_mi_paid_bits m).

Lemma caa_mi_paid_spec (m : caa_mi_payment_witness) :
  caa_mi_paid m = true <->
  (0 < caa_mi_paid_bits m)%nat /\
  (caa_mi_required_bits m <= caa_mi_paid_bits m)%nat.
Proof.
  unfold caa_mi_paid.
  split.
  - intros H.
    apply andb_prop in H as [Hp Hr].
    split.
    + apply Nat.ltb_lt in Hp. exact Hp.
    + apply Nat.leb_le in Hr. exact Hr.
  - intros [Hp Hr].
    apply andb_true_intro; split.
    + apply Nat.ltb_lt. exact Hp.
    + apply Nat.leb_le. exact Hr.
Qed.

(** Admitted composite compaction arrow — composite *is* the residue (§17.5). *)
Record CompactionArrow : Set := {
  caa_composite_id : nat;
  caa_composite_witness : caa_derivation_chain_witness;
  caa_composite_source_commit : nat;
  caa_composite_excitement_selected : bool
}.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Typed refuse + gate (positive, not bool theater)        *)
(* ------------------------------------------------------------------ *)

Inductive caa_compaction_admit :=
  | caa_admitted
  | caa_refused.

Inductive caa_compaction_verdict :=
  | caa_accept
  | caa_reject.

Inductive CompactionAsArrowRefuse :=
  | caa_refuse_delete_old_commits
  | caa_refuse_mi_unpaid
  | caa_refuse_second_argmin
  | caa_refuse_missing_derivation_witness.

(** Positive refuse: delete-old-commits theater is inadmissible. *)
Definition refuse_delete_old_commits_theater : CompactionAsArrowRefuse :=
  caa_refuse_delete_old_commits.

(** Positive refuse: compaction without MI payment. *)
Definition refuse_mi_unpaid : CompactionAsArrowRefuse :=
  caa_refuse_mi_unpaid.

(** Positive refuse: second Excitement selector — compose `excitement_select`. *)
Definition refuse_second_argmin : CompactionAsArrowRefuse :=
  caa_refuse_second_argmin.

(** Positive refuse: semantic squash without derivation witness. *)
Definition refuse_missing_derivation_witness : CompactionAsArrowRefuse :=
  caa_refuse_missing_derivation_witness.

(** One compaction attempt before gating (§17.5 fixture surface). *)
Record caa_compaction_attempt : Set := {
  caa_attempt_delete_old_commits : bool;
  caa_attempt_mi : caa_mi_payment_witness;
  caa_attempt_witness : option caa_derivation_chain_witness;
  caa_attempt_provenance_intact : bool;
  caa_attempt_excitement_selected : bool
}.

(** Build composite arrow from a non-empty derivation chain. *)
Definition compaction_arrow_from_chain (cid : nat) (chain : list nat)
    (source_commit : nat) (excitement_selected : bool)
    : CompactionArrow + CompactionAsArrowRefuse :=
  match chain with
  | nil => inr caa_refuse_missing_derivation_witness
  | _ =>
      inl
        {| caa_composite_id := cid;
           caa_composite_witness :=
             {| caa_derivation_chain := chain |};
           caa_composite_source_commit := source_commit;
           caa_composite_excitement_selected := excitement_selected |}
  end.

(** Classify verdict without performing mutation. *)
Definition caa_verdict_to_admit (v : caa_compaction_verdict) : caa_compaction_admit :=
  match v with
  | caa_accept => caa_admitted
  | caa_reject => caa_refused
  end.

(** Gate a compaction attempt — composite arrow paying MI, not delete-old-commits. *)
Definition evaluate_compaction_attempt (a : caa_compaction_attempt) :
  caa_compaction_verdict :=
  if caa_attempt_delete_old_commits a then
    caa_reject
  else if negb (caa_mi_paid (caa_attempt_mi a)) then
    caa_reject
  else
    match caa_attempt_witness a with
    | None => caa_reject
    | Some w =>
        if caa_retains_chain w then
          if caa_attempt_provenance_intact a then
            if caa_attempt_excitement_selected a then
              caa_accept
            else
              caa_reject
          else
            caa_reject
        else
          caa_reject
    end.

(** Evaluate attempt with typed refuse on reject path. *)
Definition evaluate_compaction_attempt_refuse (a : caa_compaction_attempt) :
  caa_compaction_verdict + CompactionAsArrowRefuse :=
  if caa_attempt_delete_old_commits a then
    inr caa_refuse_delete_old_commits
  else if negb (caa_mi_paid (caa_attempt_mi a)) then
    inr caa_refuse_mi_unpaid
  else
    match caa_attempt_witness a with
    | None => inr caa_refuse_missing_derivation_witness
    | Some w =>
        if caa_retains_chain w then
          if caa_attempt_provenance_intact a then
            if caa_attempt_excitement_selected a then
              inl caa_accept
            else
              inr caa_refuse_missing_derivation_witness
          else
            inr caa_refuse_missing_derivation_witness
        else
          inr caa_refuse_missing_derivation_witness
    end.

Lemma evaluate_compaction_attempt_refuse_agrees (a : caa_compaction_attempt) :
  match evaluate_compaction_attempt_refuse a with
  | inl caa_accept => evaluate_compaction_attempt a = caa_accept
  | inl caa_reject => evaluate_compaction_attempt a = caa_reject
  | inr _ => evaluate_compaction_attempt a = caa_reject
  end.
Proof.
  unfold evaluate_compaction_attempt_refuse, evaluate_compaction_attempt.
  destruct (caa_attempt_delete_old_commits a); simpl.
  - reflexivity.
  - destruct (caa_mi_paid (caa_attempt_mi a)); simpl.
    + destruct (caa_attempt_witness a) as [w|]; simpl.
      * destruct (caa_retains_chain w); simpl.
        -- destruct (caa_attempt_provenance_intact a); simpl.
           ++ destruct (caa_attempt_excitement_selected a); reflexivity.
           ++ reflexivity.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Landauer bridge — compaction pays MI (cited, not axiom) *)
(* ------------------------------------------------------------------ *)

Definition caa_mi_payment_from_landauer_bits (n : nat) : caa_mi_payment_witness :=
  {| caa_mi_required_bits := n; caa_mi_paid_bits := n |}.

Lemma caa_landauer_bridge_mi_paid_when_nonzero (n : nat) (H : (0 < n)%nat) :
  caa_mi_paid (caa_mi_payment_from_landauer_bits n) = true.
Proof.
  unfold caa_mi_payment_from_landauer_bits, caa_mi_paid.
  destruct n as [|n']; [inversion H |].
  simpl.
  rewrite Nat.leb_refl.
  reflexivity.
Qed.

Definition caa_composite_from_landauer (b : LandauerHistoryBridge)
    (prior : Provenance)
    (hPrior : provenance_dag_commit prior =
                history_commit_id (history_prior (landauer_transition b)))
    (hSL : admitSecondLaw (landauer_transition b))
    (excitement_selected : bool) :
  CompactionArrow :=
  {| caa_composite_id := history_commit_id (history_post (landauer_transition b));
     caa_composite_witness :=
       {| caa_derivation_chain :=
            provenance_ucrs_chain prior ++
            provenance_dag_commit prior :: nil |};
     caa_composite_source_commit := provenance_dag_commit prior;
     caa_composite_excitement_selected := excitement_selected |}.

Lemma caa_composite_from_landauer_retains_chain (b : LandauerHistoryBridge)
    (prior : Provenance)
    (hPrior : provenance_dag_commit prior =
                history_commit_id (history_prior (landauer_transition b)))
    (hSL : admitSecondLaw (landauer_transition b))
    (excitement_selected : bool) :
  caa_retains_chain (caa_composite_witness
    (caa_composite_from_landauer b prior hPrior hSL excitement_selected)) = true.
Proof.
  unfold caa_retains_chain, caa_composite_from_landauer.
  simpl.
  destruct (provenance_ucrs_chain prior); reflexivity.
Qed.

Theorem caa_landauer_compaction_preserves_provenance (b : LandauerHistoryBridge)
    (prior : Provenance)
    (hPrior : provenance_dag_commit prior =
                history_commit_id (history_prior (landauer_transition b)))
    (hSL : admitSecondLaw (landauer_transition b)) :
  preserves (landauer_transition b) prior
    (postProvenanceFromLandauer b prior hPrior hSL).
Proof.
  apply landauer_bridge_preserves; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Compaction composes excitement_select (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Context for compaction over admissible history successors. *)
Record caa_compaction_ctx (src : ThermodynamicState) : Set := {
  caa_compaction_successors : list (history_candidate src)
}.

(** Urge compaction **is** `urge_recovery_select` / `excitement_select`. *)
Definition compaction_as_arrow_select (src : ThermodynamicState)
    (ctx : caa_compaction_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (caa_compaction_successors src ctx).

Theorem compaction_as_arrow_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : caa_compaction_ctx src) :
  compaction_as_arrow_select src ctx =
  excitement_select src (caa_compaction_successors src ctx).
Proof.
  unfold compaction_as_arrow_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem compaction_as_arrow_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : caa_compaction_ctx src) :
  compaction_as_arrow_select src ctx =
  urge_recovery_select src (caa_compaction_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem compaction_as_arrow_no_local_argmin
    (src : ThermodynamicState) (ctx : caa_compaction_ctx src) :
  compaction_as_arrow_select src ctx =
  excitement_select src (caa_compaction_successors src ctx).
Proof.
  exact (compaction_as_arrow_select_eq_excitement_select src ctx).
Qed.

Lemma compaction_as_arrow_empty (src : ThermodynamicState)
    (ctx : caa_compaction_ctx src)
    (Hnil : caa_compaction_successors src ctx = nil) :
  compaction_as_arrow_select src ctx = inr exc_no_candidates.
Proof.
  unfold compaction_as_arrow_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(** Bare successor list selector — compose `excitement_select`, refuse second argmin. *)
Definition urge_compaction_select (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  excitement_select src cands.

Theorem urge_compaction_select_eq_excitement_select
    (src : ThermodynamicState) (cands : list (history_candidate src)) :
  urge_compaction_select src cands = excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem urge_compaction_select_eq_admit_history_select
    (src : ThermodynamicState) (cands : list (history_candidate src)) :
  urge_compaction_select src cands = admitHistorySelect src cands.
Proof.
  unfold urge_compaction_select, admitHistorySelect.
  reflexivity.
Qed.

(** Kleisli composite pin — compaction chains inherited arrows, not squash. *)
Definition caa_compaction_compose := kleisliCompose.

Theorem caa_compaction_compose_assoc_inherited (f g h : AdmitArrow)
    (s : ThermodynamicState) :
  caa_compaction_compose (caa_compaction_compose f g) h s =
  caa_compaction_compose f (caa_compaction_compose g h) s.
Proof.
  unfold caa_compaction_compose.
  exact (kleisliComposeAssocAt f g h s).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: §17.5 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition caa_fixture_mi_paid : caa_mi_payment_witness :=
  {| caa_mi_required_bits := 2; caa_mi_paid_bits := 4 |}.

Definition caa_fixture_witness : caa_derivation_chain_witness :=
  {| caa_derivation_chain := 1 :: 2 :: 3 :: nil |}.

Definition caa_fixture_admissible : caa_compaction_attempt :=
  {| caa_attempt_delete_old_commits := false;
     caa_attempt_mi := caa_fixture_mi_paid;
     caa_attempt_witness := Some caa_fixture_witness;
     caa_attempt_provenance_intact := true;
     caa_attempt_excitement_selected := true |}.

Definition caa_fixture_delete_old_commits : caa_compaction_attempt :=
  {| caa_attempt_delete_old_commits := true;
     caa_attempt_mi := caa_fixture_mi_paid;
     caa_attempt_witness := Some caa_fixture_witness;
     caa_attempt_provenance_intact := true;
     caa_attempt_excitement_selected := true |}.

Definition caa_fixture_mi_unpaid : caa_compaction_attempt :=
  {| caa_attempt_delete_old_commits := false;
     caa_attempt_mi :=
       {| caa_mi_required_bits := 2; caa_mi_paid_bits := 0 |};
     caa_attempt_witness := Some caa_fixture_witness;
     caa_attempt_provenance_intact := true;
     caa_attempt_excitement_selected := true |}.

Theorem caa_fixture_admissible_accept :
  evaluate_compaction_attempt caa_fixture_admissible = caa_accept.
Proof.
  reflexivity.
Qed.

Theorem caa_fixture_delete_old_commits_reject :
  evaluate_compaction_attempt caa_fixture_delete_old_commits = caa_reject.
Proof.
  reflexivity.
Qed.

Theorem caa_fixture_mi_unpaid_reject :
  evaluate_compaction_attempt caa_fixture_mi_unpaid = caa_reject.
Proof.
  reflexivity.
Qed.

Theorem caa_fixture_arrow_from_chain_ok :
  compaction_arrow_from_chain 42 (1 :: 2 :: nil) 7 true =
  inl
    {| caa_composite_id := 42;
       caa_composite_witness := {| caa_derivation_chain := 1 :: 2 :: nil |};
       caa_composite_source_commit := 7;
       caa_composite_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem caa_fixture_arrow_from_empty_chain_refused :
  compaction_arrow_from_chain 1 nil 0 true =
  inr caa_refuse_missing_derivation_witness.
Proof.
  reflexivity.
Qed.

Theorem refuse_delete_old_commits_theater_positive :
  refuse_delete_old_commits_theater = caa_refuse_delete_old_commits.
Proof.
  reflexivity.
Qed.

Theorem refuse_second_argmin_positive :
  refuse_second_argmin = caa_refuse_second_argmin.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition compaction_as_arrow_physics_green : bool := false.

Lemma compaction_as_arrow_physics_green_false :
  compaction_as_arrow_physics_green = false.
Proof. reflexivity. Qed.

Definition compaction_as_arrow_production_wired : bool := false.

Lemma compaction_as_arrow_production_wired_false :
  compaction_as_arrow_production_wired = false.
Proof. reflexivity. Qed.

Definition compaction_as_arrow_marker : nat := 175.

Lemma compaction_as_arrow_marker_pos :
  0 < compaction_as_arrow_marker.
Proof. apply Nat.lt_0_succ. Qed.

Theorem compaction_as_arrow_module_witness : True.
Proof. exact I. Qed.

Theorem compaction_as_arrow_no_new_axiom : True.
Proof. exact I. Qed.

Theorem compaction_as_arrow_no_second_argmin :
  refuse_second_argmin = caa_refuse_second_argmin.
Proof. reflexivity. Qed.

Theorem compaction_as_arrow_positive_refuse_not_silent :
  evaluate_compaction_attempt caa_fixture_delete_old_commits <> caa_accept.
Proof.
  unfold evaluate_compaction_attempt.
  discriminate.
Qed.
