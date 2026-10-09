(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: FluctuationTheorem.v                                     *)
(*                                                                        *)
(*  Twin of Lean/FluctuationTheorem.lean. The Jarzynski integral          *)
(*  fluctuation theorem on a finite state space {0, ..., n} and the       *)
(*  measureFeedback case of SecondLaw derived from it by Jensen.          *)
(*                                                                        *)
(*  Stage k+1 switches the energy from E k to E (k+1) (work               *)
(*  E (k+1) x - E k x at the current state x) and relaxes with a kernel   *)
(*  M k that leaves the Boltzmann weight g (k+1) = exp (-beta E (k+1))    *)
(*  invariant. The work-tilted forward vector                             *)
(*    u 0 = g 0,  u (k+1) y = sum_x u k x * exp(-beta dE_k x) * M k x y   *)
(*  equals g k after k stages (Jarzynski, PRL 78, 2690 (1997); finite      *)
(*  Markov form after Crooks, J. Stat. Phys. 90, 1481 (1998)), so          *)
(*  <exp(-beta W)> = Z K / Z 0. The Jensen bridge turns the integral       *)
(*  fluctuation theorem into <W> >= dF from 1 + t <= exp t.               *)
(*  Zero Axiom, Parameter or Admitted.                                    *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra.
Require Import UMSTFormal.Process.

Open Scope R_scope.

(** Sums over the finite state space {0, ..., n}: sum_f_R0 f n. *)

Section Protocol.

Variable n : nat.
Variable beta : R.
Variable E : nat -> nat -> R.
Variable M : nat -> nat -> nat -> R.

(** Boltzmann weight of stage k. *)
Definition weight (k x : nat) : R := exp (- beta * E k x).

(** Exponentiated work of the switch into stage k+1 at state x. *)
Definition tilt (k x : nat) : R := exp (- beta * (E (S k) x - E k x)).

(** The kernel of stage k+1 leaves the weight of that stage invariant. *)
Definition KernelBalance : Prop :=
  forall k y, sum_f_R0 (fun x => weight (S k) x * M k x y) n = weight (S k) y.

Lemma weight_tilt : forall k x, weight k x * tilt k x = weight (S k) x.
Proof.
  intros k x. unfold weight, tilt. rewrite <- exp_plus. f_equal. ring.
Qed.

(** One stage: tilting the weight of stage k by the work of the switch and relaxing gives the weight of stage k+1. *)
Theorem gibbs_tilt_stage :
  KernelBalance -> forall k y,
    sum_f_R0 (fun x => weight k x * tilt k x * M k x y) n = weight (S k) y.
Proof.
  intros hb k y. rewrite <- (hb k y). apply sum_eq. intros x _. rewrite weight_tilt. reflexivity.
Qed.

(** Unnormalised work-tilted forward vector. *)
Fixpoint tiltedForward (k : nat) (y : nat) : R :=
  match k with
  | O => weight 0 y
  | S k' => sum_f_R0 (fun x => tiltedForward k' x * tilt k' x * M k' x y) n
  end.

(** Transfer form of the Jarzynski identity: after k stages the tilted forward vector is the weight of stage k. *)
Theorem tiltedForward_eq : KernelBalance -> forall k y, tiltedForward k y = weight k y.
Proof.
  intros hb k. induction k as [| k IH]; intro y.
  - reflexivity.
  - simpl. rewrite <- (gibbs_tilt_stage hb k y). apply sum_eq. intros x _. rewrite IH. reflexivity.
Qed.

Definition partition (k : nat) : R := sum_f_R0 (weight k) n.

(** Jarzynski equality, unnormalised: sum_y u K y = Z K. *)
Theorem jarzynski_transfer :
  KernelBalance -> forall K, sum_f_R0 (tiltedForward K) n = partition K.
Proof.
  intros hb K. unfold partition. apply sum_eq. intros y _. apply tiltedForward_eq. exact hb.
Qed.

End Protocol.

(** Affine expansion of a weighted sum. *)
Lemma sum_affine (P W : nat -> R) (b dF : R) (m : nat) :
  sum_f_R0 (fun i => P i * (1 + - b * (W i - dF))) m =
    sum_f_R0 P m - b * sum_f_R0 (fun i => P i * W i) m + b * dF * sum_f_R0 P m.
Proof.
  induction m as [| m IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** Jensen bridge: on a finite ensemble {0, ..., m} with weights P >= 0 summing to one, the integral fluctuation
    theorem <exp(-beta (W - dF))> = 1 at beta > 0 forces <W> >= dF. *)
Theorem jensen_bridge (P W : nat -> R) (b dF : R) (m : nat) :
  0 < b ->
  (forall i, (i <= m)%nat -> 0 <= P i) ->
  sum_f_R0 P m = 1 ->
  sum_f_R0 (fun i => P i * exp (- b * (W i - dF))) m = 1 ->
  dF <= sum_f_R0 (fun i => P i * W i) m.
Proof.
  intros hb hP hsum hift.
  assert (hlin : sum_f_R0 (fun i => P i * (1 + - b * (W i - dF))) m <=
                 sum_f_R0 (fun i => P i * exp (- b * (W i - dF))) m).
  { apply sum_Rle. intros i hi. apply Rmult_le_compat_l; [apply hP; exact hi | apply exp_ineq1_le]. }
  rewrite sum_affine, hsum, hift in hlin.
  set (w := sum_f_R0 (fun i => P i * W i) m) in *.
  destruct (Rle_or_lt dF w) as [hle | hlt]; [exact hle |].
  exfalso. assert (0 < b * (dF - w)) by (apply Rmult_lt_0_compat; lra).
  lra.
Qed.

(** measureFeedback case of SecondLaw from the fluctuation theorem: a protocol whose ensemble satisfies the integral
    fluctuation theorem at beta = 1 / (k_B T), read as a feedback process extracting -<W>, obeys the second law
    against any measurement whose mutual information is non-negative. *)
Theorem jarzynski_secondLaw_feedback (bath : HeatBath) (P W : nat -> R) (dF mi : R) (m : nat) :
  (forall i, (i <= m)%nat -> 0 <= P i) ->
  sum_f_R0 P m = 1 ->
  sum_f_R0 (fun i => P i * exp (- (/ (kB * bathTemp bath)) * (W i - dF))) m = 1 ->
  0 <= mi ->
  SecondLaw (measureFeedback (mkFeedback bath (- sum_f_R0 (fun i => P i * W i) m) dF)) (feedback mi).
Proof.
  intros hP hsum hift hmi. simpl.
  pose proof kB_pos as hk. pose proof (bathTemp_pos bath) as hT.
  assert (hb : 0 < / (kB * bathTemp bath)) by (apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; lra).
  pose proof (jensen_bridge P W _ dF m hb hP hsum hift) as hj.
  assert (0 <= kB * bathTemp bath * mi) by (apply Rmult_le_pos; [apply Rmult_le_pos; lra | exact hmi]).
  lra.
Qed.
