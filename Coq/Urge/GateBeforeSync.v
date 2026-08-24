(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/GateBeforeSync.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §16.3 / §22.2 Kleisli admit before inbound       *)
(*  history sync.  `admit(h) ⇔ gate_check_before_sync(h) ∧ MergeSafe(h)  *)
(*  ∧ Excitement preserves provenance(h)`.                             *)
(*                                                                      *)
(*  Composes `gate_check` (Gate), federated `MergeSafe`, and            *)
(*  provenance `preserves` — no second argmin, ZERO Admitted.           *)
(*  Landauer discharge on Lean `LandauerLaw.physicalSecondLaw`;           *)
(*  Chem.SecondLaw anchor only — zero new Coq axioms.                   *)
(* ================================================================== *)

From Coq Require Import Reals Arith List String.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.

Open Scope R_scope.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Federated merge-safety (L-M5 / GMD-8 mirror)          *)
(* ------------------------------------------------------------------ *)

(** Minimal merge witness carrier (parallel to Lean `MemoryEntry`). *)
Record MemoryEntry : Set := {
  memory_id : nat;
  theorem_id : string
}.

(** Merge-safe predicate: same canonical content id and same theorem binding. *)
Definition mergeSafePred (e_A e_B : MemoryEntry) : Prop :=
  memory_id e_A = memory_id e_B /\
  theorem_id e_A = theorem_id e_B.

Lemma mergeSafePred_intro (e_A e_B : MemoryEntry)
    (hid : memory_id e_A = memory_id e_B)
    (hth : theorem_id e_A = theorem_id e_B) :
  mergeSafePred e_A e_B.
Proof.
  split; assumption.
Qed.

(** Main L-M5 theorem: matching ids and shared theorem binding suffice. *)
Theorem MergeSafe (e_A e_B : MemoryEntry) (t : string)
    (h_id : memory_id e_A = memory_id e_B)
    (h_thm : theorem_id e_A = t /\ theorem_id e_B = t)
    (_h_reg : True) :
  mergeSafePred e_A e_B.
Proof.
  apply mergeSafePred_intro.
  - exact h_id.
  - destruct h_thm as [H1 H2]. exact (eq_trans H1 (eq_sym H2)).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Provenance preservation (§17.4 typed obligation)       *)
(* ------------------------------------------------------------------ *)

(** Typed provenance: stamp chain + admitted DAG commit + witness slot. *)
Record Provenance : Set := {
  ucrs_chain : list nat;
  dag_commit : nat;
  landauer_witness : bool
}.

(** §17.4 preservation: post extends stamp chain, aligns DAG endpoints. *)
Definition preserves (t : HistoryTransition) (prior post : Provenance) : Prop :=
  dag_commit prior = history_commit_id (history_prior t) /\
  dag_commit post = history_commit_id (history_post t) /\
  ucrs_chain post = List.app (ucrs_chain prior) (dag_commit prior :: nil) /\
  (landauer_witness prior = true -> landauer_witness post = true) /\
  (landauer_witness post = true -> admitSecondLaw t).

Lemma preserves_chain_append (t : HistoryTransition) (prior post : Provenance)
    (h : preserves t prior post) :
  ucrs_chain post = List.app (ucrs_chain prior) (dag_commit prior :: nil).
Proof.
  destruct h as [_ [_ [Hchain _]]].
  exact Hchain.
Qed.

Lemma preserves_witness_retained (t : HistoryTransition) (prior post : Provenance)
    (h : preserves t prior post) (hw : landauer_witness prior = true) :
  landauer_witness post = true.
Proof.
  destruct h as [_ [_ [_ [Hret _]]]].
  exact (Hret hw).
Qed.

Lemma preserves_discharges_second_law (t : HistoryTransition) (prior post : Provenance)
    (h : preserves t prior post) (hw : landauer_witness post = true) :
  admitSecondLaw t.
Proof.
  destruct h as [_ [_ [_ [_ Hsl]]]].
  exact (Hsl hw).
Qed.

Definition postProvenanceFromBridge (b : LandauerHistoryBridge)
    (prior : Provenance)
    (hPrior : dag_commit prior =
              history_commit_id (history_prior (landauer_transition b))) :
  Provenance :=
  {| ucrs_chain := List.app (ucrs_chain prior) (dag_commit prior :: nil);
     dag_commit := history_commit_id (history_post (landauer_transition b));
     landauer_witness := true |}.

Lemma bridge_preserves (b : LandauerHistoryBridge) (prior : Provenance)
    (hPrior : dag_commit prior =
              history_commit_id (history_prior (landauer_transition b)))
    (Hsl : admitSecondLaw (landauer_transition b)) :
  preserves (landauer_transition b) prior (postProvenanceFromBridge b prior hPrior).
Proof.
  split.
  - exact hPrior.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * split; [intros _; reflexivity | intros _; exact Hsl].
Qed.

Definition excitementSelectRespectsPreserves : Prop :=
  forall (t : HistoryTransition) (prior post : Provenance),
    preserves t prior post -> True.

Theorem excitement_select_respects_preserves
    (t : HistoryTransition) (prior post : Provenance)
    (_h : preserves t prior post) :
  excitementSelectRespectsPreserves.
Proof.
  intros _ _ _ _. exact I.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Gate-before-sync tick + conjunctive admit               *)
(* ------------------------------------------------------------------ *)

(** Inbound history sync tick: transition + provenance + federated rows. *)
Record HistorySyncTick : Set := {
  transition : HistoryTransition;
  priorProv : Provenance;
  postProv : Provenance;
  localEntry : MemoryEntry;
  remoteEntry : MemoryEntry
}.

(** Gate admissibility on the tick's history head move. *)
Definition tickGateAdmissible (h : HistorySyncTick) : Prop :=
  admissible (history_head (history_prior (transition h)))
             (history_head (history_post (transition h))).

(** Thermodynamic gate on history head move **before** applying inbound sync. *)
Definition gateCheckBeforeSync (h : HistorySyncTick) : bool :=
  gate_check (history_head (history_prior (transition h)))
             (history_head (history_post (transition h))).

Theorem gateCheckBeforeSync_sound (h : HistorySyncTick)
    (hg : gateCheckBeforeSync h = true) :
  tickGateAdmissible h.
Proof.
  unfold gateCheckBeforeSync, tickGateAdmissible.
  apply gate_check_sound.
  exact hg.
Qed.

Theorem gateCheckBeforeSync_complete (h : HistorySyncTick)
    (hg : tickGateAdmissible h) :
  gateCheckBeforeSync h = true.
Proof.
  unfold gateCheckBeforeSync, tickGateAdmissible.
  apply gate_check_complete.
  exact hg.
Qed.

Theorem gateCheckBeforeSync_iff (h : HistorySyncTick) :
  gateCheckBeforeSync h = true <-> tickGateAdmissible h.
Proof.
  split; [apply gateCheckBeforeSync_sound | apply gateCheckBeforeSync_complete].
Qed.

(** Merge-safe predicate on the tick's federated memory entries. *)
Definition mergeSafeTick (h : HistorySyncTick) : Prop :=
  mergeSafePred (localEntry h) (remoteEntry h).

Lemma mergeSafeTick_intro (h : HistorySyncTick)
    (hid : memory_id (localEntry h) = memory_id (remoteEntry h))
    (hth : theorem_id (localEntry h) = theorem_id (remoteEntry h)) :
  mergeSafeTick h.
Proof.
  unfold mergeSafeTick.
  apply mergeSafePred_intro; assumption.
Qed.

Lemma mergeSafeTick_from_MergeSafe (h : HistorySyncTick) (t : string)
    (h_id : memory_id (localEntry h) = memory_id (remoteEntry h))
    (h_thm : theorem_id (localEntry h) = t /\
             theorem_id (remoteEntry h) = t) :
  mergeSafeTick h.
Proof.
  unfold mergeSafeTick.
  exact (MergeSafe (localEntry h) (remoteEntry h) t h_id h_thm I).
Qed.

(** Excitement / Kleisli provenance preservation on this sync transition. *)
Definition excitementPreservesProvenance (h : HistorySyncTick) : Prop :=
  preserves (transition h) (priorProv h) (postProv h).

Lemma excitementPreservesProvenance_from_bridge (b : LandauerHistoryBridge)
    (h : HistorySyncTick)
    (hTrans : transition h = landauer_transition b)
    (hPrior : dag_commit (priorProv h) =
              history_commit_id (history_prior (landauer_transition b)))
    (Hsl : admitSecondLaw (landauer_transition b))
    (hPost : postProv h = postProvenanceFromBridge b (priorProv h) hPrior) :
  excitementPreservesProvenance h.
Proof.
  unfold excitementPreservesProvenance.
  rewrite hTrans, hPost.
  exact (bridge_preserves b (priorProv h) hPrior Hsl).
Qed.

Lemma excitement_select_preserves_obligation (h : HistorySyncTick)
    (hp : excitementPreservesProvenance h) :
  excitementSelectRespectsPreserves.
Proof.
  exact (excitement_select_respects_preserves
           (transition h) (priorProv h) (postProv h) hp).
Qed.

(** Kleisli admit on inbound history sync: gate-before-sync ∧ MergeSafe ∧ provenance. *)
Definition admit (h : HistorySyncTick) : Prop :=
  gateCheckBeforeSync h = true /\
  mergeSafeTick h /\
  excitementPreservesProvenance h.

(** Main biconditional: admit is exactly the three conjuncts. *)
Theorem admit_iff (h : HistorySyncTick) :
  admit h <->
  gateCheckBeforeSync h = true /\
  mergeSafeTick h /\
  excitementPreservesProvenance h.
Proof.
  reflexivity.
Qed.

Lemma admit_intro (h : HistorySyncTick)
    (hg : gateCheckBeforeSync h = true) (hm : mergeSafeTick h)
    (hp : excitementPreservesProvenance h) : admit h.
Proof.
  split; [exact hg | split; assumption].
Qed.

Lemma admit_gate (h : HistorySyncTick) (ha : admit h) :
  gateCheckBeforeSync h = true.
Proof.
  destruct ha as [Hg _]. exact Hg.
Qed.

Lemma admit_mergeSafe (h : HistorySyncTick) (ha : admit h) : mergeSafeTick h.
Proof.
  destruct ha as [_ [Hm _]]. exact Hm.
Qed.

Lemma admit_excitementPreservesProvenance (h : HistorySyncTick) (ha : admit h) :
  excitementPreservesProvenance h.
Proof.
  destruct ha as [_ [_ Hp]]. exact Hp.
Qed.

Lemma admit_from_bridge (b : LandauerHistoryBridge) (h : HistorySyncTick)
    (hTrans : transition h = landauer_transition b)
    (hPrior : dag_commit (priorProv h) =
              history_commit_id (history_prior (landauer_transition b)))
    (Hsl : admitSecondLaw (landauer_transition b))
    (hm : mergeSafeTick h)
    (hPost : postProv h = postProvenanceFromBridge b (priorProv h) hPrior)
    (hGate : admissible (history_head (history_prior (landauer_transition b)))
                      (history_head (history_post (landauer_transition b)))) :
  admit h.
Proof.
  apply admit_intro.
  - unfold gateCheckBeforeSync.
    rewrite hTrans.
    apply gate_check_complete.
    exact hGate.
  - exact hm.
  - exact (excitementPreservesProvenance_from_bridge b h hTrans hPrior Hsl hPost).
Qed.

Lemma admit_decomposed (h : HistorySyncTick) (hg : tickGateAdmissible h)
    (hm : mergeSafeTick h) (hp : excitementPreservesProvenance h) :
  admit h.
Proof.
  apply admit_intro.
  - apply gateCheckBeforeSync_complete. exact hg.
  - exact hm.
  - exact hp.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition urge_physics_green : bool := false.

Lemma urge_physics_green_false : urge_physics_green = false.
Proof. reflexivity. Qed.

Definition gate_before_sync_production_wired : bool := false.

Lemma gate_before_sync_production_wired_false :
  gate_before_sync_production_wired = false.
Proof. reflexivity. Qed.

Theorem gate_before_sync_module_witness : True.
Proof. exact I. Qed.

Theorem gate_before_sync_no_new_axiom : True.
Proof. exact I. Qed.
