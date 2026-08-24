(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/AppendOnly.v                                    *)
(*                                                                      *)
(*  Meso acting Urge — §17.6 append-only admitted history invariant.   *)
(*  Admitted history is append-only; silent rewrite refused as a `Prop`. *)
(*  Self-healing adds an Excitement arrow; it does not mutate prior      *)
(*  admitted objects. Compose `excitement_select` — no second argmin.  *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli.admitSecondLaw` via Landauer bridge.    *)
(*  Adds **zero** Coq `Axiom` declarations. ZERO `Admitted`.           *)
(* ================================================================== *)

From Stdlib Require Import Arith List Lia.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Append-only commit moves (§17.6)                        *)
(* ------------------------------------------------------------------ *)

(** Monotone commit-id move: prior strictly before post (append-only head). *)
Definition appendOnlyCommitMove (t : HistoryTransition) : Prop :=
  (history_commit_id (history_prior t) <
   history_commit_id (history_post t))%nat.

(** §17.6 append-only invariant on a single admitted transition. *)
Definition appendOnlyInvariant (t : HistoryTransition) : Prop :=
  appendOnlyCommitMove t.

(** Silent rewrite: post does not strictly extend prior commit id. *)
Definition silentRewrite (t : HistoryTransition) : Prop :=
  (history_commit_id (history_post t) <=
   history_commit_id (history_prior t))%nat.

(** Silent rewrite refused when append-only discipline holds. *)
Theorem silentRewriteRefused (t : HistoryTransition)
    (h : appendOnlyCommitMove t) :
  ~ silentRewrite t.
Proof.
  unfold appendOnlyCommitMove, silentRewrite in *.
  lia.
Qed.

(** Append-only and silent rewrite are mutually exclusive. *)
Theorem appendOnly_not_silentRewrite (t : HistoryTransition) :
  appendOnlyCommitMove t <-> ~ silentRewrite t.
Proof.
  split.
  - exact (silentRewriteRefused t).
  - intros Hnot.
    unfold appendOnlyCommitMove, silentRewrite in *.
    lia.
Qed.

(** Admitted history transition with append-only discipline (§17.6). *)
Definition appendOnlyAdmittedTransition (t : HistoryTransition) : Prop :=
  admissibleHistoryTransition t /\ appendOnlyInvariant t.

(** Every transition in a chain respects append-only commit moves. *)
Definition appendOnlyHistoryChain (ts : list HistoryTransition) : Prop :=
  forall t, In t ts -> appendOnlyCommitMove t.

(** Chain append-only ⇒ no transition in the chain is a silent rewrite. *)
Theorem appendOnlyHistoryChain_refusesSilentRewrite
    (ts : list HistoryTransition) (h : appendOnlyHistoryChain ts)
    (t : HistoryTransition) (ht : In t ts) :
  ~ silentRewrite t.
Proof.
  exact (silentRewriteRefused t (h t ht)).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Recovery / self-heal append-only                        *)
(* ------------------------------------------------------------------ *)

(** Recovery snapshot must strictly extend prior commit id (new arrow, not rewrite). *)
Definition recoveryAppendOnly (prior post : HistorySnapshot) : Prop :=
  (history_commit_id prior < history_commit_id post)%nat.

(** Silent rewrite on bare snapshots (no thermodynamic accounting). *)
Definition silentRewriteSnapshots (prior post : HistorySnapshot) : Prop :=
  (history_commit_id post <= history_commit_id prior)%nat.

(** Recovery append-only refuses silent rewrite on snapshots. *)
Theorem recoveryAppendOnly_refusesSilentRewrite
    (prior post : HistorySnapshot) (h : recoveryAppendOnly prior post) :
  ~ silentRewriteSnapshots prior post.
Proof.
  unfold recoveryAppendOnly, silentRewriteSnapshots in *.
  lia.
Qed.

(** Self-heal discipline: recovery transition obeys append-only when modeled as HistoryTransition. *)
Definition selfHealAppendOnly (t : HistoryTransition) : Prop :=
  recoveryAppendOnly (history_prior t) (history_post t).

Theorem selfHealAppendOnly_eq_appendOnlyInvariant (t : HistoryTransition) :
  selfHealAppendOnly t = appendOnlyInvariant t.
Proof. reflexivity. Qed.

(** Self-heal transition refuses snapshot-level silent rewrite. *)
Theorem selfHeal_not_silentRewrite (t : HistoryTransition)
    (h : selfHealAppendOnly t) :
  ~ silentRewriteSnapshots (history_prior t) (history_post t).
Proof.
  exact (recoveryAppendOnly_refusesSilentRewrite
           (history_prior t) (history_post t) h).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Landauer bridge (derived — zero new axioms)             *)
(* ------------------------------------------------------------------ *)

(** Landauer-bridged transition is append-only admitted. *)
Theorem appendOnlyAdmitted_from_landauer (b : LandauerHistoryBridge)
    (hAppend : appendOnlyCommitMove (landauer_transition b))
    (hSL : admitSecondLaw (landauer_transition b)) :
  appendOnlyAdmittedTransition (landauer_transition b).
Proof.
  split.
  - exact (admissibleHistoryTransition_from_landauer_bridge b hSL).
  - exact hAppend.
Qed.

(** Landauer bridge forbids silent rewrite on the bridged transition. *)
Theorem silentRewriteRefused_from_landauer (b : LandauerHistoryBridge)
    (hAppend : appendOnlyCommitMove (landauer_transition b))
    (_hSL : admitSecondLaw (landauer_transition b)) :
  ~ silentRewrite (landauer_transition b).
Proof.
  exact (silentRewriteRefused (landauer_transition b) hAppend).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Excitement composition (no second argmin)               *)
(* ------------------------------------------------------------------ *)

(** Self-heal recovery composes `excitement_select` — not a second argmin. *)
Definition appendOnlyRecoverySelect (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  excitement_select src cands.

Theorem appendOnlyRecoverySelect_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  appendOnlyRecoverySelect src cands = excitement_select src cands.
Proof. reflexivity. Qed.

Theorem appendOnlyRecoverySelect_no_local_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  appendOnlyRecoverySelect src cands = admitHistorySelect src cands.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition append_only_physics_green : bool := false.

Lemma append_only_physics_green_false :
  append_only_physics_green = false.
Proof. reflexivity. Qed.

Definition appendOnlyProductionWired : bool := false.

Lemma appendOnlyProductionWiredFalse :
  appendOnlyProductionWired = false.
Proof. reflexivity. Qed.

Theorem appendOnlyModuleWitness : True.
Proof. exact I. Qed.

(** §17.6 named obligation: admitted history append-only; silent rewrite refused. *)
Theorem appendOnly_silentRewrite_refused (t : HistoryTransition)
    (h : appendOnlyInvariant t) :
  ~ silentRewrite t.
Proof.
  exact (silentRewriteRefused t h).
Qed.
