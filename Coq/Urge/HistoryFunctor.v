(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/HistoryFunctor.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — Admissible HistoryFunctor (§5.1).               *)
(*  identity: history_functor                                            *)
(*  Git-style content-addressed bytes → typed gate-checked history with *)
(*  second-law preservation (Prop — not a Coq Axiom).                  *)
(*                                                                      *)
(*  Mirrors umst-meta `evaluate_transition` provenance gate; thermo-    *)
(*  dynamic head moves reuse `AdmitKleisli` carriers. History recovery  *)
(*  composes `ExcitementImport.urge_recovery` — no second argmin.       *)
(*  Adds **zero** Coq `Axiom` declarations. ZERO `Admitted`.           *)
(* ================================================================== *)

From Coq Require Import Arith Bool String QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope string_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Git-style raw commit bytes → typed history carriers     *)
(* ------------------------------------------------------------------ *)

(** Content-addressed byte payload (git-style opaque blob). *)
Definition RawCommitBytes := list nat.

Record RawGitCommit : Set := {
  commitHash : nat;
  payload : RawCommitBytes
}.

Record RepoStateSlice : Set := {
  repo_provenance_intact : bool;
  repo_physics_green_claim : bool;
  repo_witness_present : bool
}.

Record RepoTransitionStep : Set := {
  repo_before : RepoStateSlice;
  repo_after : RepoStateSlice;
  repo_provenance_stamp : option string;
  repo_drops_provenance : bool;
  repo_invents_green : bool
}.

Inductive TransitionVerdict :=
  | transition_accept
  | transition_reject.

Record TypedHistory : Set := {
  typed_snapshot : HistorySnapshot;
  typed_provenance_intact : bool
}.

Record AdmissibleHistoryFunctor : Set := {
  history_decode : RawGitCommit -> option TypedHistory;
  history_preserve_commit_id :
    forall c h, history_decode c = Some h ->
      commitHash c = history_commit_id (typed_snapshot h)
}.

Definition history_functor_identity : string := "history_functor"%string.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Second-law preservation on typed history transitions    *)
(* ------------------------------------------------------------------ *)

Definition gateAdmissibleHead (t : HistoryTransition) : Prop :=
  admissible (history_head (history_prior t)) (history_head (history_post t)).

Definition preservationProp (t : HistoryTransition) : Prop :=
  admitSecondLaw t /\ gateAdmissibleHead t.

Theorem preservationProp_of_admissible (t : HistoryTransition)
    (h : admissibleHistoryTransition t) : preservationProp t.
Proof.
  split.
  - exact h.
  - unfold gateAdmissibleHead. exact (history_gate_admissible t).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Provenance gate on repository transitions (meta mirror) *)
(* ------------------------------------------------------------------ *)

Definition provenancedOkStep : RepoTransitionStep :=
  {| repo_before :=
       {| repo_provenance_intact := true;
          repo_physics_green_claim := false;
          repo_witness_present := false |};
     repo_after :=
       {| repo_provenance_intact := true;
          repo_physics_green_claim := false;
          repo_witness_present := false |};
     repo_provenance_stamp := Some "ucrs:t"%string;
     repo_drops_provenance := false;
     repo_invents_green := false |}.

Definition evaluateTransition (step : RepoTransitionStep) : TransitionVerdict :=
  if repo_invents_green step then transition_reject
  else if repo_physics_green_claim (repo_after step) &&
          negb (repo_witness_present (repo_after step)) then transition_reject
  else if repo_drops_provenance step then transition_reject
  else if repo_provenance_intact (repo_before step) &&
          negb (repo_provenance_intact (repo_after step)) then transition_reject
  else
    match repo_provenance_stamp step with
    | None => transition_reject
    | Some stamp =>
      if String.eqb stamp ""%string then transition_reject
      else if repo_provenance_intact (repo_after step) &&
              negb (repo_physics_green_claim (repo_after step)) then
        transition_accept
      else transition_reject
    end.

Theorem evaluateTransition_rejects_invents_green (step : RepoTransitionStep)
    (h : repo_invents_green step = true) :
  evaluateTransition step = transition_reject.
Proof.
  intros. unfold evaluateTransition. rewrite h. reflexivity.
Qed.

Theorem evaluateTransition_rejects_physics_green_without_witness
    (step : RepoTransitionStep)
    (hg : repo_physics_green_claim (repo_after step) = true)
    (hw : repo_witness_present (repo_after step) = false)
    (hi : repo_invents_green step = false) :
  evaluateTransition step = transition_reject.
Proof.
  intros. unfold evaluateTransition. rewrite hi, hg, hw.
  simpl. reflexivity.
Qed.

Theorem evaluateTransition_rejects_drops_provenance (step : RepoTransitionStep)
    (hd : repo_drops_provenance step = true) (hi : repo_invents_green step = false)
    (hn : repo_physics_green_claim (repo_after step) = false) :
  evaluateTransition step = transition_reject.
Proof.
  intros. unfold evaluateTransition. rewrite hi, hn, hd.
  simpl. reflexivity.
Qed.

Theorem provenancedOkStep_evaluates_accept :
  evaluateTransition provenancedOkStep = transition_accept.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Catalog decode fixture (git bytes → typed history)        *)
(* ------------------------------------------------------------------ *)

Definition fixtureState : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition fixtureCommitHash : nat := 42.

Definition fixturePayload : RawCommitBytes := nil.

Definition fixtureRawCommit : RawGitCommit :=
  {| commitHash := fixtureCommitHash; payload := fixturePayload |}.

Definition fixtureTypedHistory : TypedHistory :=
  {| typed_snapshot :=
       {| history_commit_id := fixtureCommitHash;
          history_head := fixtureState |};
     typed_provenance_intact := true |}.

Definition catalogDecode (c : RawGitCommit) : option TypedHistory :=
  if Nat.eqb (commitHash c) fixtureCommitHash then
    Some fixtureTypedHistory
  else
    None.

Theorem catalogDecode_fixture :
  catalogDecode fixtureRawCommit = Some fixtureTypedHistory.
Proof.
  unfold catalogDecode, fixtureRawCommit, fixtureCommitHash, fixtureTypedHistory.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem catalogDecode_preserveCommitId (c : RawGitCommit) (h : TypedHistory)
    (hd : catalogDecode c = Some h) :
  commitHash c = history_commit_id (typed_snapshot h).
Proof.
  intros. unfold catalogDecode in hd.
  destruct (Nat.eqb (commitHash c) fixtureCommitHash) eqn:Hc.
  - apply Nat.eqb_eq in Hc.
    injection hd as Heq. subst h.
    unfold fixtureTypedHistory. simpl. exact Hc.
  - discriminate hd.
Qed.

Definition catalogHistoryFunctor : AdmissibleHistoryFunctor :=
  {| history_decode := catalogDecode;
     history_preserve_commit_id := catalogDecode_preserveCommitId |}.

Theorem catalog_decode_fixture :
  history_decode catalogHistoryFunctor fixtureRawCommit = Some fixtureTypedHistory.
Proof.
  exact catalogDecode_fixture.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Landauer bridge discharge (zero new axioms)              *)
(* ------------------------------------------------------------------ *)

Theorem preservationProp_from_landauer (b : LandauerHistoryBridge)
    (hSL : admitSecondLaw (landauer_transition b)) :
  preservationProp (landauer_transition b).
Proof.
  split.
  - exact hSL.
  - unfold gateAdmissibleHead. exact (history_gate_admissible (landauer_transition b)).
Qed.

Theorem admissible_preserves_second_law (t : HistoryTransition)
    (h : admissibleHistoryTransition t) : admitSecondLaw t.
Proof.
  exact h.
Qed.

Theorem historyFunctor_noNewAxiom (b : LandauerHistoryBridge)
    (hSL : admitSecondLaw (landauer_transition b)) :
  preservationProp (landauer_transition b).
Proof.
  exact (preservationProp_from_landauer b hSL).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Excitement composition (no second argmin)               *)
(* ------------------------------------------------------------------ *)

(** Typed-history recovery on gate-checked head — aliases `urge_recovery_select`. *)
Definition historyFunctorSelect (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src successors.

Theorem historyFunctorSelect_eq_excitement_select
    (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  historyFunctorSelect src successors = excitement_select src successors.
Proof.
  unfold historyFunctorSelect.
  exact (urge_recovery_select_eq_excitement_select src successors).
Qed.

Theorem historyFunctorSelect_eq_urge_recovery
    (src : ThermodynamicState) (ctx : history_recovery_ctx src) :
  historyFunctorSelect src (recovery_successors src ctx) =
  urge_recovery src ctx.
Proof.
  unfold historyFunctorSelect.
  exact (urge_recovery_eq_urge_recovery_select src ctx).
Qed.

Theorem historyFunctor_no_local_argmin
    (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  historyFunctorSelect src successors = excitement_select src successors.
Proof.
  exact (historyFunctorSelect_eq_excitement_select src successors).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 7: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition urgePhysicsGreen : bool := false.

Lemma urgePhysicsGreenFalse : urgePhysicsGreen = false.
Proof. reflexivity. Qed.

Definition historyFunctorProductionWired : bool := false.

Lemma historyFunctorProductionWiredFalse :
  historyFunctorProductionWired = false.
Proof. reflexivity. Qed.

Theorem historyFunctorModuleWitness : True.
Proof. exact I. Qed.
