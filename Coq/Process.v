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
(*    transition       mass within delta_mass and free energy not rising *)
(*                     (the universal core; cement constraints compose     *)
(*                     over it in Concrete/SecondLaw.v)                    *)
(*                                                                        *)
(*  Consequences proved here: the Landauer bound T ln 2 <= W for a        *)
(*  uniform bit, the tight erasure attaining it, and the SI bound         *)
(*  k_B T ln 2 <= W with the exact k_B of Constants/SI.v. Zero Axiom,     *)
(*  Parameter or Admitted.                                                *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra QArith Qreals List.
Import ListNotations.
Require Import UMSTFormal.Compat.Gate.
Require Import UMSTFormal.Constitutional.
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

(** A distribution on finitely many states: nonnegative masses summing to one. *)
Record ProbDist : Type := mkProbDist {
  mass : list R;
  mass_nonneg : Forall (fun x => 0 <= x) mass;
  mass_sum : fold_right Rplus 0 mass = 1
}.

(** Shannon entropy in nats of an n-state distribution. *)
Definition shannon (p : ProbDist) : R := - fold_right (fun x acc => xlnx x + acc) 0 (mass p).

(** A two-state distribution as an n-state one; its entropy is the binary entropy. *)
Definition asProbDist (p : ProbDist2) : ProbDist :=
  mkProbDist [p0 p; 1 - p0 p]
    ltac:(pose proof (p0_nonneg p); pose proof (p0_le_one p); constructor; [lra | constructor; [lra | constructor]])
    ltac:(simpl; lra).

Lemma shannon_asProbDist (p : ProbDist2) : shannon (asProbDist p) = shannon2 p.
Proof. unfold shannon, shannon2, asProbDist; simpl. lra. Qed.

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
  | thermodynamic (old new : ThermodynamicState)
  | transformation (prior post : ProbDist).

(** **The second law**: one predicate over the process family. *)
Definition SecondLaw (proc : Process) (prior : Prior) : Prop :=
  match proc, prior with
  | erase e, erasure p => eraseSecondLaw e p
  | measureFeedback f, feedback mi =>
      extWork f <= - deltaFreeEnergy f + kB * bathTemp (feedbackBath f) * mi
  | transition, thermodynamic old new =>
      core_admissible (density old) (density new) (free_energy old) (free_energy new)
  | erase e, transformation p q => shannon p - shannon q <= work e / bathTemp (erasureBath e)
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

(** Binary erasure is the transformation whose target is the Dirac state. *)
Theorem SecondLaw_erasure_iff_transformation (e : ErasureProcess) (p : ProbDist2) :
  SecondLaw (erase e) (erasure p) <-> SecondLaw (erase e) (transformation (asProbDist p) (asProbDist dirac0)).
Proof. simpl. unfold eraseSecondLaw. rewrite !shannon_asProbDist. tauto. Qed.

(** Leaving a distribution unchanged costs nothing. *)
Theorem SecondLaw_transformation_id (b : HeatBath) (p : ProbDist) :
  SecondLaw (erase (mkErasure b 0)) (transformation p p).
Proof. simpl. unfold Rdiv. rewrite Rmult_0_l. lra. Qed.

(** **Composition**: at one bath, transformations p -> q at work W1 and q -> r at work W2 that obey the second law
    compose into p -> r at work W1 + W2, which obeys it: entropy drops telescope and costs add. *)
Theorem SecondLaw_transformation_comp (b : HeatBath) (p q r : ProbDist) (W1 W2 : R) :
  SecondLaw (erase (mkErasure b W1)) (transformation p q) ->
  SecondLaw (erase (mkErasure b W2)) (transformation q r) ->
  SecondLaw (erase (mkErasure b (W1 + W2))) (transformation p r).
Proof.
  simpl. intros h1 h2. pose proof (bathTemp_pos b).
  replace ((W1 + W2) / bathTemp b) with (W1 / bathTemp b + W2 / bathTemp b) by (field; lra). lra.
Qed.

(** A state move that changes nothing is admissible. *)
Theorem SecondLaw_transition_refl (s : ThermodynamicState) : SecondLaw transition (thermodynamic s s).
Proof.
  simpl. unfold core_admissible, delta_mass, Qminus. rewrite Qplus_opp_r.
  split; [discriminate | split; [discriminate | apply Qle_refl]].
Qed.

(** The predicate is satisfiable: the Landauer-tight erasure of a uniform bit obeys it. *)
Theorem secondLaw_process_family_satisfiable : exists p pr, SecondLaw p pr.
Proof.
  exists (erase (landauerTightErasure (mkHeatBath 300 ltac:(lra)))), (erasure uniform2).
  apply landauerTight.
Qed.

(** Independent erasures: the entropy both remove is at most the entropy both dissipate. *)
Theorem SecondLaw_erasure_additive (e1 e2 : ErasureProcess) (p q : ProbDist2) :
  SecondLaw (erase e1) (erasure p) -> SecondLaw (erase e2) (erasure q) ->
  (shannon2 p - shannon2 dirac0) + (shannon2 q - shannon2 dirac0) <=
    work e1 / bathTemp (erasureBath e1) + work e2 / bathTemp (erasureBath e2).
Proof. simpl. unfold eraseSecondLaw. intros h1 h2. lra. Qed.

(* --------------------------------------------------------------------- *)
(*  Witness: the Szilard engine at I = ln 2                               *)
(* --------------------------------------------------------------------- *)

(** A joint distribution on two binary variables, by the masses of (0,0), (0,1), (1,0), (1,1). *)
Record JointDist2 : Type := mkJointDist2 {
  j00 : R; j01 : R; j10 : R; j11 : R;
  j00_nonneg : 0 <= j00; j01_nonneg : 0 <= j01; j10_nonneg : 0 <= j10; j11_nonneg : 0 <= j11;
  j_sum : j00 + j01 + j10 + j11 = 1
}.

(** Marginals, by the probability of the first state. *)
Definition marginalX2 (J : JointDist2) : ProbDist2 :=
  mkProbDist2 (j00 J + j01 J)
    ltac:(pose proof (j00_nonneg J); pose proof (j01_nonneg J); lra)
    ltac:(pose proof (j10_nonneg J); pose proof (j11_nonneg J); pose proof (j_sum J); lra).
Definition marginalY2 (J : JointDist2) : ProbDist2 :=
  mkProbDist2 (j00 J + j10 J)
    ltac:(pose proof (j00_nonneg J); pose proof (j10_nonneg J); lra)
    ltac:(pose proof (j01_nonneg J); pose proof (j11_nonneg J); pose proof (j_sum J); lra).

Definition jointEntropy2 (J : JointDist2) : R := - (xlnx (j00 J) + xlnx (j01 J) + xlnx (j10 J) + xlnx (j11 J)).

(** Mutual information (nats): H(X) + H(Y) - H(X, Y). *)
Definition mutualInformation2 (J : JointDist2) : R :=
  shannon2 (marginalX2 J) + shannon2 (marginalY2 J) - jointEntropy2 J.

(** The deterministic Szilard copy joint: one bit of correlation. *)
Definition szilardJoint : JointDist2 :=
  mkJointDist2 (1 / 2) 0 0 (1 / 2) ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra).

Theorem szilardJoint_marginalX : p0 (marginalX2 szilardJoint) = p0 uniform2.
Proof. simpl. lra. Qed.

Theorem szilardJoint_marginalY : p0 (marginalY2 szilardJoint) = p0 uniform2.
Proof. simpl. lra. Qed.

Lemma shannon2_ext (p q : ProbDist2) : p0 p = p0 q -> shannon2 p = shannon2 q.
Proof. intro h. unfold shannon2. rewrite h. reflexivity. Qed.

Theorem szilardJoint_entropy : jointEntropy2 szilardJoint = ln 2.
Proof.
  unfold jointEntropy2, szilardJoint, xlnx; simpl.
  destruct (Rle_dec (1 / 2) 0) as [h | _]; [lra |].
  destruct (Rle_dec 0 0) as [_ | h]; [| lra].
  replace (1 / 2) with (/ 2) by lra. rewrite ln_Rinv by lra. lra.
Qed.

Theorem szilardJoint_mutualInformation : mutualInformation2 szilardJoint = ln 2.
Proof.
  unfold mutualInformation2.
  rewrite (shannon2_ext _ _ szilardJoint_marginalX), (shannon2_ext _ _ szilardJoint_marginalY),
    shannon2_uniform2, szilardJoint_entropy. lra.
Qed.

(** Szilard-limited feedback work at the bath: W_ext = k_B T ln 2, dF = 0. *)
Definition szilardEngine (b : HeatBath) : FeedbackProcess := mkFeedback b (kB * bathTemp b * ln 2) 0.

(** The Szilard engine obeys the second law at equality, judged against the information of its joint. *)
Theorem SecondLaw_szilardEngine (b : HeatBath) :
  SecondLaw (measureFeedback (szilardEngine b)) (feedback (mutualInformation2 szilardJoint)).
Proof. simpl. rewrite szilardJoint_mutualInformation. lra. Qed.

(** Units bridge: the erase instance states work in units of k_B times kelvin; in joules that work is k_B W, and the
    instance is exactly the SI Clausius form at that work. One law, two unit systems. *)
Theorem SecondLaw_transformation_iff_SI (b : HeatBath) (W : R) (p q : ProbDist) :
  SecondLaw (erase (mkErasure b W)) (transformation p q) <->
    eraseSecondLawSI (bathTemp b) (shannon p - shannon q) (kB * W).
Proof.
  simpl. unfold eraseSecondLawSI. pose proof kB_pos as hk. pose proof (bathTemp_pos b) as hT.
  replace (kB * W / (kB * bathTemp b)) with (W / bathTemp b) by (field; split; lra).
  reflexivity.
Qed.
