(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: Process.v                                                *)
(*                                                                        *)
(*  The one second law, twin of Lean/Process.lean and Lean/LandauerLaw:   *)
(*  a process family (erasure, measurement with feedback, gate            *)
(*  transition) and one predicate SecondLaw : Process -> Prior -> Prop.   *)
(*  A prior of the wrong kind for its process yields False.               *)
(*                                                                        *)
(*    erase            S(prior) - S(Dirac) <= W / T  (entropy in nats,    *)
(*                     work in units of k_B times kelvin)                 *)
(*    measureFeedback  W_ext <= -dF + k_B T I  (joules; I in nats)        *)
(*    transition       the gate's admissibility of the state move         *)
(*                                                                        *)
(*  Consequences proved here: the Landauer bound T ln 2 <= W for a        *)
(*  uniform bit, the tight erasure attaining it, and the SI bound         *)
(*  k_B T ln 2 <= W with the exact k_B of Constants/SI.v. Zero Axiom,     *)
(*  Parameter or Admitted.                                                *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra QArith Qreals.
Require Import UMSTFormal.Compat.Gate.
Require Import UMSTFormal.Constants.SI.

Open Scope R_scope.

(** A heat bath at a positive temperature (kelvin). *)
Record HeatBath : Type := mkHeatBath {
  bathTemp : R;
  bathTemp_pos : 0 < bathTemp
}.

(** An erasure: its bath and the work it dissipates (units of k_B times kelvin). *)
Record ErasureProcess : Type := mkErasure {
  erasureBath : HeatBath;
  work : R
}.

(** A distribution on two states, given by the probability of the first. *)
Record ProbDist2 : Type := mkProbDist2 {
  p0 : R;
  p0_nonneg : 0 <= p0;
  p0_le_one : p0 <= 1
}.

(** x ln x with the continuous extension 0 ln 0 = 0. *)
Definition xlnx (x : R) : R := if Rle_dec x 0 then 0 else x * ln x.

(** Shannon entropy in nats. *)
Definition shannon2 (p : ProbDist2) : R := - (xlnx (p0 p) + xlnx (1 - p0 p)).

Definition dirac0 : ProbDist2 := mkProbDist2 1 ltac:(lra) ltac:(lra).
Definition uniform2 : ProbDist2 := mkProbDist2 (1 / 2) ltac:(lra) ltac:(lra).

Lemma shannon2_dirac0 : shannon2 dirac0 = 0.
Proof.
  unfold shannon2, dirac0, xlnx; simpl.
  destruct (Rle_dec 1 0) as [h | _]; [lra |].
  destruct (Rle_dec (1 - 1) 0) as [_ | h]; [| lra].
  rewrite ln_1. lra.
Qed.

Lemma shannon2_uniform2 : shannon2 uniform2 = ln 2.
Proof.
  unfold shannon2, uniform2, xlnx; simpl.
  replace (1 - 1 / 2) with (1 / 2) by lra.
  destruct (Rle_dec (1 / 2) 0) as [h | _]; [lra |].
  replace (1 / 2) with (/ 2) by lra.
  rewrite ln_Rinv by lra. lra.
Qed.

(** The erase instance (Clausius form): erasing [prior] to the Dirac state lowers the entropy by at most W / T. *)
Definition eraseSecondLaw (proc : ErasureProcess) (prior : ProbDist2) : Prop :=
  shannon2 prior - shannon2 dirac0 <= work proc / bathTemp (erasureBath proc).

(** Measurement and feedback: external work, free-energy change, bath. *)
Record FeedbackProcess : Type := mkFeedback {
  feedbackBath : HeatBath;
  extWork : R;
  deltaFreeEnergy : R
}.

(** The exact SI Boltzmann constant of Constants/SI.v. *)
Definition kB : R := Q2R boltzmann.

Lemma kB_pos : 0 < kB.
Proof.
  unfold kB, Q2R, boltzmann; simpl.
  apply Rmult_lt_0_compat; [apply IZR_lt; reflexivity | apply Rinv_0_lt_compat; apply IZR_lt; reflexivity].
Qed.

Inductive Process : Type :=
  | erase (proc : ErasureProcess)
  | measureFeedback (proc : FeedbackProcess)
  | transition.

(** The prior a process is judged against: a distribution to erase, the mutual information (nats) a measurement
    acquired, or the two states of a gate move. *)
Inductive Prior : Type :=
  | erasure (p : ProbDist2)
  | feedback (mutualInformation : R)
  | thermodynamic (old new : ThermodynamicState).

(** **The second law**: one predicate over the process family. *)
Definition SecondLaw (proc : Process) (prior : Prior) : Prop :=
  match proc, prior with
  | erase e, erasure p => eraseSecondLaw e p
  | measureFeedback f, feedback mi =>
      extWork f <= - deltaFreeEnergy f + kB * bathTemp (feedbackBath f) * mi
  | transition, thermodynamic old new => admissible old new
  | _, _ => False
  end.

(** A prior of the wrong kind is refused. *)
Lemma SecondLaw_erase_feedback (e : ErasureProcess) (mi : R) : ~ SecondLaw (erase e) (feedback mi).
Proof. simpl. tauto. Qed.

(** **Landauer bound**: erasing a uniform bit at temperature T costs at least T ln 2. *)
Theorem landauerBound (e : ErasureProcess) :
  SecondLaw (erase e) (erasure uniform2) -> bathTemp (erasureBath e) * ln 2 <= work e.
Proof.
  simpl. unfold eraseSecondLaw. rewrite shannon2_uniform2, shannon2_dirac0.
  intro h. pose proof (bathTemp_pos (erasureBath e)) as hT.
  apply Rmult_le_compat_r with (r := bathTemp (erasureBath e)) in h; [| lra].
  unfold Rdiv in h. rewrite Rmult_assoc, Rinv_l, Rmult_1_r in h by lra. lra.
Qed.

(** The bound is attained: the erasure that dissipates exactly T ln 2 obeys the second law. *)
Definition landauerTightErasure (b : HeatBath) : ErasureProcess := mkErasure b (bathTemp b * ln 2).

Theorem landauerTight (b : HeatBath) : SecondLaw (erase (landauerTightErasure b)) (erasure uniform2).
Proof.
  simpl. unfold eraseSecondLaw, landauerTightErasure. simpl.
  rewrite shannon2_uniform2, shannon2_dirac0.
  pose proof (bathTemp_pos b) as hT.
  replace (bathTemp b * ln 2 / bathTemp b) with (ln 2) by (field; lra). lra.
Qed.

(** SI Clausius form: an entropy drop dS (nats) with work W in joules at T obeys dS <= W / (k_B T). *)
Definition eraseSecondLawSI (T dS W : R) : Prop := dS <= W / (kB * T).

(** **SI Landauer bound**: under the SI form, erasing one bit at T costs at least k_B T ln 2 joules. *)
Theorem landauerBoundSI (T W : R) : 0 < T -> eraseSecondLawSI T (ln 2) W -> kB * T * ln 2 <= W.
Proof.
  unfold eraseSecondLawSI. intros hT h. pose proof kB_pos as hk.
  assert (hkT : 0 < kB * T) by (apply Rmult_lt_0_compat; lra).
  apply Rmult_le_compat_r with (r := kB * T) in h; [| lra].
  unfold Rdiv in h. rewrite Rmult_assoc, Rinv_l, Rmult_1_r in h by lra. lra.
Qed.
