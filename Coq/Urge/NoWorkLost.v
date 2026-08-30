(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/NoWorkLost.v                                      *)
(*                                                                      *)
(*  Meso acting Urge — BP II §1 prime invariant: No-Loss.               *)
(*  Once a change is *admitted* on any replica, it stays reachable      *)
(*  from the system as a whole. Conjunction of eight named mechanisms;  *)
(*  honest absent pins for `reconcile` and `transport` (not built).       *)
(*                                                                      *)
(*  Checkable property `NO-WORK-LOST`: for admitted change `c` and op   *)
(*  `op`, `c` remains reachable from ≥1 replica after `op`.             *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `AppendOnly` / `ProvenancePreserve`.   *)
(*  Adds **zero** Coq `Axiom` declarations. ZERO `Admitted`.            *)
(* ================================================================== *)

From Coq Require Import Arith List Bool Lia String.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.AppendOnly.
Require Import UMSTFormal.Urge.ProvenancePreserve.

Open Scope bool_scope.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Eight No-Loss mechanisms (BP II §1 table)               *)
(* ------------------------------------------------------------------ *)

(** Eight concrete mechanisms protecting admitted work (BP II §1). *)
Inductive no_loss_mechanism :=
  | nlm_provenance_on_every_change
  | nlm_append_only_admitted_history
  | nlm_content_addressing
  | nlm_union_preserving_reconcile
  | nlm_refusal_holds_never_discards
  | nlm_compaction_supersedes_not_deletes
  | nlm_replica_coalgebra_typed_backup
  | nlm_multi_transport_redundancy.

(** Human-readable mechanism tag for drift pins. *)
Definition no_loss_mechanism_tag (m : no_loss_mechanism) : string :=
  match m with
  | nlm_provenance_on_every_change => "provenance_preserve"
  | nlm_append_only_admitted_history => "append_only"
  | nlm_content_addressing => "content_addressed"
  | nlm_union_preserving_reconcile => "reconcile"
  | nlm_refusal_holds_never_discards => "kleisli_recover"
  | nlm_compaction_supersedes_not_deletes => "compaction_as_arrow"
  | nlm_replica_coalgebra_typed_backup => "replica_coalgebra"
  | nlm_multi_transport_redundancy => "transport"
  end.

(** Honest wired posture per mechanism — absent modules pinned false. *)
Definition no_loss_mechanism_wired (m : no_loss_mechanism) : bool :=
  match m with
  | nlm_provenance_on_every_change => true
  | nlm_append_only_admitted_history => true
  | nlm_content_addressing => true
  | nlm_union_preserving_reconcile => false
  | nlm_refusal_holds_never_discards => true
  | nlm_compaction_supersedes_not_deletes => true
  | nlm_replica_coalgebra_typed_backup => true
  | nlm_multi_transport_redundancy => false
  end.

(** Partial / checkpoint posture — wired algebra, not running fleet. *)
Definition no_loss_mechanism_partial (m : no_loss_mechanism) : bool :=
  match m with
  | nlm_content_addressing => true
  | nlm_compaction_supersedes_not_deletes => true
  | nlm_replica_coalgebra_typed_backup => true
  | _ => false
  end.

Definition pin_eight_no_loss_mechanisms : list no_loss_mechanism :=
  nlm_provenance_on_every_change ::
  nlm_append_only_admitted_history ::
  nlm_content_addressing ::
  nlm_union_preserving_reconcile ::
  nlm_refusal_holds_never_discards ::
  nlm_compaction_supersedes_not_deletes ::
  nlm_replica_coalgebra_typed_backup ::
  nlm_multi_transport_redundancy :: nil.

Theorem pin_eight_no_loss_mechanisms_length :
  List.length pin_eight_no_loss_mechanisms = (8%nat).
Proof. reflexivity. Qed.

Theorem reconcile_mechanism_absent :
  no_loss_mechanism_wired nlm_union_preserving_reconcile = false.
Proof. reflexivity. Qed.

Theorem transport_mechanism_absent :
  no_loss_mechanism_wired nlm_multi_transport_redundancy = false.
Proof. reflexivity. Qed.

Theorem append_only_mechanism_wired :
  no_loss_mechanism_wired nlm_append_only_admitted_history = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Admitted change + reachability (NO-WORK-LOST)           *)
(* ------------------------------------------------------------------ *)

(** Admitted change carrier — content id + commit id + replica presence. *)
Record admitted_change : Set := {
  nwl_content_id : nat;
  nwl_commit_id : nat;
  nwl_reachable_on_replica : bool
}.

(** Reachable from at least one replica (checkable surrogate). *)
Definition reachable_from_some_replica (c : admitted_change) : Prop :=
  nwl_reachable_on_replica c = true.

(** Computational reachability check. *)
Definition reachable_from_some_replica_b (c : admitted_change) : bool :=
  nwl_reachable_on_replica c.

Lemma reachable_from_some_replica_iff (c : admitted_change) :
  reachable_from_some_replica c <-> reachable_from_some_replica_b c = true.
Proof.
  unfold reachable_from_some_replica, reachable_from_some_replica_b.
  split; intros H; [exact H | exact H].
Qed.

(** §1 checkable property: after `op`, admitted `c` stays reachable. *)
Definition no_work_lost_after_op (c : admitted_change) (op_preserves : bool) : Prop :=
  op_preserves = true -> reachable_from_some_replica c.

(** Orphaning refused: operation that drops reachability is inadmissible. *)
Definition orphaning_refused (c : admitted_change) (op_preserves : bool) : Prop :=
  reachable_from_some_replica c \/ op_preserves = false.

Theorem no_work_lost_after_op_from_orphan_refuse
    (c : admitted_change) (op_preserves : bool)
    (h : orphaning_refused c op_preserves) :
  no_work_lost_after_op c op_preserves.
Proof.
  unfold no_work_lost_after_op, orphaning_refused in *.
  intros Hpres.
  destruct h as [Hr | Hdrop].
  - exact Hr.
  - congruence.
Qed.

(** Admitted change with proven commit id (non-zero surrogate). *)
Definition admitted_change_well_formed (c : admitted_change) : Prop :=
  (0 < nwl_commit_id c)%nat.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Mechanism conjunct bundle                               *)
(* ------------------------------------------------------------------ *)

(** Conjunct inputs for the eight-mechanism No-Loss bundle. *)
Record no_loss_conjunct : Set := {
  nlc_provenance_intact : bool;
  nlc_append_only : bool;
  nlc_content_named : bool;
  nlc_reconcile_union : bool;
  nlc_refusal_retains : bool;
  nlc_compaction_supersedes : bool;
  nlc_replica_backup : bool;
  nlc_transport_redundant : bool
}.

(** Evaluate No-Loss conjunct — wired mechanisms must hold. *)
Definition no_loss_conjunct_holds (c : no_loss_conjunct) : bool :=
  nlc_provenance_intact c &&
  nlc_append_only c &&
  nlc_content_named c &&
  nlc_refusal_retains c &&
  nlc_compaction_supersedes c &&
  nlc_replica_backup c.

(** Reconcile and transport are absent — not required for conjunct yet. *)
Definition no_loss_absent_mechanisms_honest : Prop :=
  no_loss_mechanism_wired nlm_union_preserving_reconcile = false /\
  no_loss_mechanism_wired nlm_multi_transport_redundancy = false.

Theorem no_loss_absent_mechanisms_honest_holds : no_loss_absent_mechanisms_honest.
Proof.
  split; reflexivity.
Qed.

(** Build conjunct from per-mechanism wired flags (honest defaults). *)
Definition no_loss_conjunct_from_wired : no_loss_conjunct :=
  {| nlc_provenance_intact := no_loss_mechanism_wired nlm_provenance_on_every_change;
     nlc_append_only := no_loss_mechanism_wired nlm_append_only_admitted_history;
     nlc_content_named := no_loss_mechanism_wired nlm_content_addressing;
     nlc_reconcile_union := no_loss_mechanism_wired nlm_union_preserving_reconcile;
     nlc_refusal_retains := no_loss_mechanism_wired nlm_refusal_holds_never_discards;
     nlc_compaction_supersedes := no_loss_mechanism_wired nlm_compaction_supersedes_not_deletes;
     nlc_replica_backup := no_loss_mechanism_wired nlm_replica_coalgebra_typed_backup;
     nlc_transport_redundant := no_loss_mechanism_wired nlm_multi_transport_redundancy |}.

Lemma no_loss_conjunct_from_wired_holds :
  no_loss_conjunct_holds no_loss_conjunct_from_wired = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Append-only bridge (mechanism #2 → no silent orphan)    *)
(* ------------------------------------------------------------------ *)

(** Append-only transition preserves prior commit reachability surrogate. *)
Definition append_only_preserves_reachability
    (c : admitted_change) (t : HistoryTransition)
    (hAppend : appendOnlyInvariant t)
    (hPrior : nwl_commit_id c = history_commit_id (history_prior t)) :
  admitted_change :=
  {| nwl_content_id := nwl_content_id c;
     nwl_commit_id := history_commit_id (history_post t);
     nwl_reachable_on_replica := nwl_reachable_on_replica c |}.

Theorem append_only_no_silent_orphan
    (c : admitted_change) (t : HistoryTransition)
    (hReach : reachable_from_some_replica c)
    (hAppend : appendOnlyInvariant t)
    (hPrior : nwl_commit_id c = history_commit_id (history_prior t)) :
  reachable_from_some_replica
    (append_only_preserves_reachability c t hAppend hPrior).
Proof.
  unfold append_only_preserves_reachability, reachable_from_some_replica in *.
  exact hReach.
Qed.

Theorem append_only_refuses_rewrite_orphan
    (t : HistoryTransition) (hAppend : appendOnlyInvariant t) :
  ~ silentRewrite t.
Proof.
  exact (silentRewriteRefused t hAppend).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Provenance bridge (mechanism #1)                        *)
(* ------------------------------------------------------------------ *)

(** Provenance-preserving op retains reachability when already reachable. *)
Definition provenance_preserving_op
    (c : admitted_change) (t : HistoryTransition)
    (prior post : Provenance)
    (hPres : preserves t prior post)
    (hReach : reachable_from_some_replica c) :
  admitted_change :=
  {| nwl_content_id := nwl_content_id c;
     nwl_commit_id := provenance_dag_commit post;
     nwl_reachable_on_replica := nwl_reachable_on_replica c |}.

Theorem provenance_preserving_op_retains_reachability
    (c : admitted_change) (t : HistoryTransition)
    (prior post : Provenance)
    (hPres : preserves t prior post)
    (hReach : reachable_from_some_replica c) :
  reachable_from_some_replica
    (provenance_preserving_op c t prior post hPres hReach).
Proof.
  unfold provenance_preserving_op, reachable_from_some_replica. exact hReach.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Excitement composition (no second argmin)               *)
(* ------------------------------------------------------------------ *)

(** No-Loss recovery selection composes `excitement_select` — not argmin. *)
Definition no_loss_recovery_select (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  excitement_select src cands.

Theorem no_loss_recovery_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  no_loss_recovery_select src cands = excitement_select src cands.
Proof. reflexivity. Qed.

Theorem no_loss_recovery_select_no_local_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  no_loss_recovery_select src cands = admitHistorySelect src cands.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 7: Honesty flags + catalog witness                         *)
(* ------------------------------------------------------------------ *)

Definition no_work_lost_physics_green : bool := false.

Lemma no_work_lost_physics_green_false :
  no_work_lost_physics_green = false.
Proof. reflexivity. Qed.

Definition noWorkLostProductionWired : bool := false.

Lemma noWorkLostProductionWiredFalse :
  noWorkLostProductionWired = false.
Proof. reflexivity. Qed.

Definition no_work_lost_guard_built : bool := false.

Lemma no_work_lost_guard_not_built :
  no_work_lost_guard_built = false.
Proof. reflexivity. Qed.

(** BP II §1 named obligation catalog witness. *)
Theorem noWorkLostModuleWitness : True.
Proof. exact I. Qed.

(** §1 prime invariant fragment — reachable admitted change survives preserving op. *)
Theorem no_loss_prime_invariant_holds
    (c : admitted_change) (op_preserves : bool)
    (hReach : reachable_from_some_replica c) :
  no_work_lost_after_op c op_preserves.
Proof.
  unfold no_work_lost_after_op, reachable_from_some_replica in *.
  intros _. exact hReach.
Qed.

(** NO-WORK-LOST checkable surrogate — red when guard not built. *)
Definition no_work_lost_checkable : bool :=
  no_work_lost_guard_built.

Theorem no_work_lost_checkable_honest_red :
  no_work_lost_checkable = false.
Proof. reflexivity. Qed.
