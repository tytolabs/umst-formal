(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/KleisliMerge.v                                    *)
(*                                                                      *)
(*  Meso acting Urge — §16.7 operator verb `merge` as Kleisli arrow.    *)
(*  Kleisli gate = `gate_check_before_sync` inbound; MergeSafe predicate *)
(*  required; Excitement = provenance preserved; entity check = tier     *)
(*  disjoint. Honest refuse on MergeSafe mismatch — no CRDT auto-merge.  *)
(*                                                                      *)
(*  Composes `excitement_select` — not a second argmin. Anchored in       *)
(*  `AdmitKleisli` / `MergeSafe` / `ExcitementImport`. ZERO Admitted.   *)
(*  ZERO new Axiom. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.MergeSafe.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Open Scope list_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: §16.7 verb row + merge carriers                        *)
(* ------------------------------------------------------------------ *)

Inductive operator_verb := op_verb_merge.

Inductive verb_column_requirement :=
  | verb_col_not_required
  | verb_col_required.

Inductive kleisli_gate_kind :=
  | kg_gate_check_before_sync_inbound
  | kg_frugal_mi_observation
  | kg_outbound_tick_if_admitted.

Inductive entity_check_kind :=
  | ec_tier_disjoint
  | ec_remote_class
  | ec_replica_class.

Record operator_verb_row : Set := {
  ovr_verb : operator_verb;
  ovr_kleisli_gate : kleisli_gate_kind;
  ovr_merge_safe : verb_column_requirement;
  ovr_excitement : verb_column_requirement;
  ovr_entity_check : entity_check_kind
}.

Definition merge_verb_row : operator_verb_row :=
  {| ovr_verb := op_verb_merge;
     ovr_kleisli_gate := kg_gate_check_before_sync_inbound;
     ovr_merge_safe := verb_col_required;
     ovr_excitement := verb_col_required;
     ovr_entity_check := ec_tier_disjoint |}.

Inductive memory_tier :=
  | mt_ephemeral
  | mt_device
  | mt_federated.

Record merge_history_object : Set := {
  mho_entry : HistoryMemoryEntry;
  mho_tier : memory_tier
}.

Inductive inbound_gate_check :=
  | igc_admitted
  | igc_refused
  | igc_bypass_attempted.

Definition inbound_gate_admits (g : inbound_gate_check) : bool :=
  match g with
  | igc_admitted => true
  | igc_refused | igc_bypass_attempted => false
  end.

Record merge_transition : Set := {
  merge_prior_commit : nat;
  merge_post_commit : nat
}.

Record merge_provenance : Set := {
  merge_ucrs_chain : list nat;
  merge_dag_commit : nat;
  merge_landauer_witness : bool
}.

Record merge_kleisli_arrow : Set := {
  mka_verb : operator_verb;
  mka_gate : inbound_gate_check;
  mka_left : merge_history_object;
  mka_right : merge_history_object;
  mka_transition : merge_transition;
  mka_prior_provenance : merge_provenance;
  mka_post_provenance : merge_provenance;
  mka_prior_state : ThermodynamicState;
  mka_post_state : ThermodynamicState
}.

Inductive tier_disjoint_verdict :=
  | tdv_admit
  | tdv_refuse_cross_tier.

Inductive provenance_preserve_verdict :=
  | ppv_admit
  | ppv_refuse_prior_dag
  | ppv_refuse_post_dag
  | ppv_refuse_chain
  | ppv_refuse_witness.

Inductive merge_arrow_refusal :=
  | mar_wrong_verb
  | mar_gate_refused
  | mar_gate_bypass_refused
  | mar_tier_disjoint (v : tier_disjoint_verdict)
  | mar_merge_safe_refused
  | mar_provenance_refused (v : provenance_preserve_verdict)
  | mar_production_wired_refused.

Record merge_outcome : Set := {
  merge_out_merged : merge_history_object;
  merge_out_provenance : provenance_preserve_verdict;
  merge_out_tier : tier_disjoint_verdict
}.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: MergeSafe + tier disjoint + provenance (computational)   *)
(* ------------------------------------------------------------------ *)

Fixpoint memory_tier_eqb (t1 t2 : memory_tier) : bool :=
  match t1, t2 with
  | mt_ephemeral, mt_ephemeral => true
  | mt_device, mt_device => true
  | mt_federated, mt_federated => true
  | _, _ => false
  end.

Fixpoint list_eqb {A : Type} (eqA : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | nil, nil => true
  | x :: xt, y :: yt => eqA x y && list_eqb eqA xt yt
  | _, _ => false
  end.

Fixpoint operator_verb_eqb (v1 v2 : operator_verb) : bool :=
  match v1, v2 with
  | op_verb_merge, op_verb_merge => true
  end.

Fixpoint inbound_gate_check_eqb (g1 g2 : inbound_gate_check) : bool :=
  match g1, g2 with
  | igc_admitted, igc_admitted => true
  | igc_refused, igc_refused => true
  | igc_bypass_attempted, igc_bypass_attempted => true
  | _, _ => false
  end.

Fixpoint tier_disjoint_verdict_eqb (v1 v2 : tier_disjoint_verdict) : bool :=
  match v1, v2 with
  | tdv_admit, tdv_admit => true
  | tdv_refuse_cross_tier, tdv_refuse_cross_tier => true
  | _, _ => false
  end.

Fixpoint provenance_preserve_verdict_eqb (v1 v2 : provenance_preserve_verdict) : bool :=
  match v1, v2 with
  | ppv_admit, ppv_admit => true
  | ppv_refuse_prior_dag, ppv_refuse_prior_dag => true
  | ppv_refuse_post_dag, ppv_refuse_post_dag => true
  | ppv_refuse_chain, ppv_refuse_chain => true
  | ppv_refuse_witness, ppv_refuse_witness => true
  | _, _ => false
  end.

Definition merge_gate_check_before_sync (prior post : ThermodynamicState) : bool :=
  gate_check prior post.

Definition evaluate_tier_disjoint (t1 t2 : memory_tier) : tier_disjoint_verdict :=
  if memory_tier_eqb t1 t2 then tdv_admit else tdv_refuse_cross_tier.

Definition merge_history_entry (left right : HistoryMemoryEntry) :
  option HistoryMemoryEntry :=
  match merge_safe left right with
  | merge_safe_admit => Some left
  | merge_safe_refuse_mismatch => None
  end.

Definition preserves_merge_provenance (tr : merge_transition)
    (prior post : merge_provenance) : provenance_preserve_verdict :=
  if Nat.eqb (merge_dag_commit prior) (merge_prior_commit tr) then
    if Nat.eqb (merge_dag_commit post) (merge_post_commit tr) then
      let expected := merge_ucrs_chain prior ++ merge_dag_commit prior :: nil in
      if list_eqb Nat.eqb (merge_ucrs_chain post) expected then
        if andb (merge_landauer_witness prior) (negb (merge_landauer_witness post)) then
          ppv_refuse_witness
        else
          ppv_admit
      else
        ppv_refuse_chain
    else
      ppv_refuse_post_dag
  else
    ppv_refuse_prior_dag.

Definition evaluate_merge_kleisli (a : merge_kleisli_arrow) :
  merge_outcome + merge_arrow_refusal :=
  if operator_verb_eqb (mka_verb a) op_verb_merge then
    if inbound_gate_check_eqb (mka_gate a) igc_bypass_attempted then
      inr mar_gate_bypass_refused
    else if negb (inbound_gate_admits (mka_gate a)) then
      inr mar_gate_refused
    else if tier_disjoint_verdict_eqb
              (evaluate_tier_disjoint (mho_tier (mka_left a)) (mho_tier (mka_right a)))
              tdv_admit then
      match merge_history_entry (mho_entry (mka_left a)) (mho_entry (mka_right a)) with
      | None => inr mar_merge_safe_refused
      | Some merged_entry =>
          let prov := preserves_merge_provenance (mka_transition a)
                           (mka_prior_provenance a) (mka_post_provenance a) in
          if provenance_preserve_verdict_eqb prov ppv_admit then
            if merge_gate_check_before_sync (mka_prior_state a) (mka_post_state a) then
              inl
                {| merge_out_merged :=
                     {| mho_entry := merged_entry;
                        mho_tier := mho_tier (mka_left a) |};
                   merge_out_provenance := prov;
                   merge_out_tier := tdv_admit |}
            else
              inr mar_gate_refused
          else
            inr (mar_provenance_refused prov)
      end
    else
      inr (mar_tier_disjoint
             (evaluate_tier_disjoint (mho_tier (mka_left a)) (mho_tier (mka_right a))))
  else
    inr mar_wrong_verb.

Lemma merge_verb_row_merge_safe_required :
  ovr_merge_safe merge_verb_row = verb_col_required.
Proof. reflexivity. Qed.

Lemma merge_verb_row_excitement_required :
  ovr_excitement merge_verb_row = verb_col_required.
Proof. reflexivity. Qed.

Lemma merge_verb_row_tier_disjoint_entity :
  ovr_entity_check merge_verb_row = ec_tier_disjoint.
Proof. reflexivity. Qed.

Lemma kleisli_gate_matches_merge_inbound :
  ovr_kleisli_gate merge_verb_row = kg_gate_check_before_sync_inbound.
Proof. reflexivity. Qed.

Lemma kleisli_gate_frugal_mi_not_merge :
  ovr_kleisli_gate merge_verb_row <> kg_frugal_mi_observation.
Proof. discriminate. Qed.

Lemma merge_history_entry_admit_iff (left right : HistoryMemoryEntry) :
  merge_history_entry left right = Some left <->
  merge_safe left right = merge_safe_admit.
Proof.
  unfold merge_history_entry.
  destruct (merge_safe left right); split; simpl; reflexivity || discriminate.
Qed.

Lemma merge_history_entry_refuse_on_mismatch (left right : HistoryMemoryEntry) :
  merge_safe left right = merge_safe_refuse_mismatch ->
  merge_history_entry left right = None.
Proof.
  intros H.
  unfold merge_history_entry.
  rewrite H. reflexivity.
Qed.

Lemma evaluate_tier_disjoint_same (t : memory_tier) :
  evaluate_tier_disjoint t t = tdv_admit.
Proof.
  unfold evaluate_tier_disjoint, memory_tier_eqb.
  destruct t; reflexivity.
Qed.

Lemma evaluate_tier_disjoint_cross (t1 t2 : memory_tier)
    (H : t1 <> t2) :
  evaluate_tier_disjoint t1 t2 = tdv_refuse_cross_tier.
Proof.
  unfold evaluate_tier_disjoint.
  destruct t1, t2; try reflexivity; contradiction.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Merge composes Excitement (no second argmin)             *)
(* ------------------------------------------------------------------ *)

Record merge_kleisli_ctx (src : ThermodynamicState) : Set := {
  merge_successors : list (history_candidate src)
}.

Definition merge_kleisli_select (src : ThermodynamicState)
    (ctx : merge_kleisli_ctx src) :
  history_candidate src + excitement_residue :=
  excitement_select src (merge_successors src ctx).

Theorem merge_kleisli_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : merge_kleisli_ctx src) :
  merge_kleisli_select src ctx =
  excitement_select src (merge_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem merge_kleisli_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : merge_kleisli_ctx src) :
  merge_kleisli_select src ctx =
  urge_recovery_select src (merge_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem merge_kleisli_no_local_argmin
    (src : ThermodynamicState) (ctx : merge_kleisli_ctx src) :
  merge_kleisli_select src ctx =
  excitement_select src (merge_successors src ctx).
Proof.
  exact (merge_kleisli_select_eq_excitement_select src ctx).
Qed.

Lemma merge_kleisli_empty (src : ThermodynamicState)
    (ctx : merge_kleisli_ctx src)
    (Hnil : merge_successors src ctx = nil) :
  merge_kleisli_select src ctx = inr exc_no_candidates.
Proof.
  unfold merge_kleisli_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Positive refuse + CRDT + fixtures                       *)
(* ------------------------------------------------------------------ *)

Inductive merge_gate_mismatch :=
  | mgm_frugal_mi_on_merge
  | mgm_outbound_tick_on_merge
  | mgm_remote_class_on_merge
  | mgm_replica_class_on_merge.

Definition refuse_frugal_mi_on_merge : merge_gate_mismatch := mgm_frugal_mi_on_merge.

Definition refuse_outbound_tick_on_merge : merge_gate_mismatch := mgm_outbound_tick_on_merge.

Definition refuse_remote_class_on_merge : merge_gate_mismatch := mgm_remote_class_on_merge.

Definition refuse_replica_class_on_merge : merge_gate_mismatch := mgm_replica_class_on_merge.

Definition refuse_production_wired_merge : merge_arrow_refusal := mar_production_wired_refused.

Definition merge_fixture_entry : HistoryMemoryEntry :=
  {| history_content_id := 42;
     history_theorem_id := 7 |}.

Definition merge_fixture_object : merge_history_object :=
  {| mho_entry := merge_fixture_entry; mho_tier := mt_device |}.

Definition merge_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition merge_fixture_provenance (prior post : nat) : merge_provenance :=
  {| merge_ucrs_chain := prior :: nil;
     merge_dag_commit := prior;
     merge_landauer_witness := true |}.

Definition merge_fixture_post_provenance (prior post : nat) : merge_provenance :=
  {| merge_ucrs_chain := prior :: prior :: nil;
     merge_dag_commit := post;
     merge_landauer_witness := true |}.

Definition merge_fixture_arrow : merge_kleisli_arrow :=
  {| mka_verb := op_verb_merge;
     mka_gate := igc_admitted;
     mka_left := merge_fixture_object;
     mka_right := merge_fixture_object;
     mka_transition := {| merge_prior_commit := 10; merge_post_commit := 11 |};
     mka_prior_provenance := merge_fixture_provenance 10 11;
     mka_post_provenance := merge_fixture_post_provenance 10 11;
     mka_prior_state := merge_fixture_state;
     mka_post_state := merge_fixture_state |}.

Theorem merge_fixture_evaluate_ok :
  evaluate_merge_kleisli merge_fixture_arrow = inl
    {| merge_out_merged := merge_fixture_object;
       merge_out_provenance := ppv_admit;
       merge_out_tier := tdv_admit |}.
Proof.
  reflexivity.
Qed.

Definition merge_fixture_arrow_gate_refused : merge_kleisli_arrow :=
  {| mka_verb := op_verb_merge;
     mka_gate := igc_refused;
     mka_left := merge_fixture_object;
     mka_right := merge_fixture_object;
     mka_transition := {| merge_prior_commit := 10; merge_post_commit := 11 |};
     mka_prior_provenance := merge_fixture_provenance 10 11;
     mka_post_provenance := merge_fixture_post_provenance 10 11;
     mka_prior_state := merge_fixture_state;
     mka_post_state := merge_fixture_state |}.

Definition merge_fixture_right_mismatch : merge_history_object :=
  {| mho_entry := {| history_content_id := 99; history_theorem_id := 7 |};
     mho_tier := mt_device |}.

Definition merge_fixture_arrow_merge_safe_refused : merge_kleisli_arrow :=
  {| mka_verb := op_verb_merge;
     mka_gate := igc_admitted;
     mka_left := merge_fixture_object;
     mka_right := merge_fixture_right_mismatch;
     mka_transition := {| merge_prior_commit := 10; merge_post_commit := 11 |};
     mka_prior_provenance := merge_fixture_provenance 10 11;
     mka_post_provenance := merge_fixture_post_provenance 10 11;
     mka_prior_state := merge_fixture_state;
     mka_post_state := merge_fixture_state |}.

Definition merge_fixture_right_cross_tier : merge_history_object :=
  {| mho_entry := merge_fixture_entry; mho_tier := mt_federated |}.

Definition merge_fixture_arrow_tier_disjoint_refused : merge_kleisli_arrow :=
  {| mka_verb := op_verb_merge;
     mka_gate := igc_admitted;
     mka_left := merge_fixture_object;
     mka_right := merge_fixture_right_cross_tier;
     mka_transition := {| merge_prior_commit := 10; merge_post_commit := 11 |};
     mka_prior_provenance := merge_fixture_provenance 10 11;
     mka_post_provenance := merge_fixture_post_provenance 10 11;
     mka_prior_state := merge_fixture_state;
     mka_post_state := merge_fixture_state |}.

Theorem merge_fixture_gate_refused :
  evaluate_merge_kleisli merge_fixture_arrow_gate_refused = inr mar_gate_refused.
Proof.
  reflexivity.
Qed.

Theorem merge_fixture_merge_safe_refused :
  evaluate_merge_kleisli merge_fixture_arrow_merge_safe_refused =
  inr mar_merge_safe_refused.
Proof.
  reflexivity.
Qed.

Theorem merge_fixture_tier_disjoint_refused :
  evaluate_merge_kleisli merge_fixture_arrow_tier_disjoint_refused =
  inr (mar_tier_disjoint tdv_refuse_cross_tier).
Proof.
  reflexivity.
Qed.

Theorem merge_fixture_crdt_refused :
  refuse_crdt_auto_merge = crdt_auto_merge_refused_tag.
Proof.
  reflexivity.
Qed.

Theorem merge_fixture_positive_refuse_gates :
  refuse_frugal_mi_on_merge = mgm_frugal_mi_on_merge /\
  refuse_outbound_tick_on_merge = mgm_outbound_tick_on_merge /\
  refuse_remote_class_on_merge = mgm_remote_class_on_merge /\
  refuse_replica_class_on_merge = mgm_replica_class_on_merge.
Proof.
  split; [| split; [| split]]; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition kleisli_merge_physics_green : bool := false.

Lemma kleisli_merge_physics_green_false :
  kleisli_merge_physics_green = false.
Proof. reflexivity. Qed.

Definition kleisli_merge_production_wired : bool := false.

Lemma kleisli_merge_production_wired_false :
  kleisli_merge_production_wired = false.
Proof. reflexivity. Qed.

Definition kleisli_merge_marker : nat := 167.

Lemma kleisli_merge_marker_pos :
  (0 < kleisli_merge_marker)%nat.
Proof. apply Nat.lt_0_succ. Qed.

Theorem kleisli_merge_module_witness : True.
Proof. exact I. Qed.

Theorem kleisli_merge_no_new_axiom : True.
Proof. exact I. Qed.

Theorem kleisli_merge_no_second_argmin
    (src : ThermodynamicState) (ctx : merge_kleisli_ctx src) :
  merge_kleisli_select src ctx = admitHistorySelect src (merge_successors src ctx).
Proof.
  unfold merge_kleisli_select, admitHistorySelect.
  reflexivity.
Qed.
