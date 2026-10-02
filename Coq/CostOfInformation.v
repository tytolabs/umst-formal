(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: CostOfInformation.v                                      *)
(*                                                                        *)
(*  Twin of Lean/CostOfInformation.lean: an erasure obeying the one       *)
(*  predicate removes at most 1/(k_B T) nats per joule; erasing b bits    *)
(*  costs at least b k_B T ln 2 joules; a claim paid by such an erasure   *)
(*  spends honestly, and an honest claim's information-per-joule score    *)
(*  is at most its dignity over k_B T ln 2.                               *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Require Import UMSTFormal.Process.

Open Scope R_scope.

Lemma fold_sum_repeat (c : R) (n : nat) : fold_right Rplus 0 (repeat c n) = INR n * c.
Proof. induction n as [| k IH]; [simpl; ring |]. rewrite S_INR. simpl. rewrite IH. ring. Qed.

Lemma fold_xlnx_repeat (c : R) (n : nat) : fold_right (fun x acc => xlnx x + acc) 0 (repeat c n) = INR n * xlnx c.
Proof. induction n as [| k IH]; [simpl; ring |]. rewrite S_INR. simpl. rewrite IH. ring. Qed.

(** The uniform distribution on n states. *)
Definition uniformN (n : nat) (hn : (0 < n)%nat) : ProbDist.
Proof.
  refine (mkProbDist (repeat (/ INR n) n) _ _).
  - apply Forall_forall. intros x hx. apply repeat_spec in hx. subst.
    apply Rlt_le, Rinv_0_lt_compat, lt_0_INR. exact hn.
  - rewrite fold_sum_repeat. apply Rinv_r. apply not_0_INR. lia.
Defined.

(** The uniform distribution on n states carries ln n nats. *)
Theorem shannon_uniformN (n : nat) (hn : (0 < n)%nat) : shannon (uniformN n hn) = ln (INR n).
Proof.
  unfold shannon, uniformN. simpl. rewrite fold_xlnx_repeat. unfold xlnx.
  pose proof (lt_0_INR n hn) as hpos.
  destruct (Rle_dec (/ INR n) 0) as [h | _].
  - pose proof (Rinv_0_lt_compat _ hpos). lra.
  - rewrite ln_Rinv by exact hpos. field. lra.
Qed.

(** The point distribution on n states, at the first state. *)
Definition diracN (n : nat) : ProbDist.
Proof.
  refine (mkProbDist (1 :: repeat 0 n) _ _).
  - constructor; [lra |]. apply Forall_forall. intros x hx. apply repeat_spec in hx. lra.
  - simpl. rewrite fold_sum_repeat. ring.
Defined.

Theorem shannon_diracN (n : nat) : shannon (diracN n) = 0.
Proof.
  unfold shannon, diracN. simpl. rewrite fold_xlnx_repeat. unfold xlnx.
  destruct (Rle_dec 1 0) as [h | _]; [lra |]. destruct (Rle_dec 0 0) as [_ | h]; [| lra].
  rewrite ln_1. ring.
Qed.

(** In joules: an erasure obeying the predicate dissipates at least k_B T times the entropy it removes. *)
Theorem entropyDrop_joules_le (b : HeatBath) (W : R) (p q : ProbDist) :
  SecondLaw (erase (mkErasure b W)) (transformation p q) -> kB * bathTemp b * (shannon p - shannon q) <= kB * W.
Proof.
  simpl. intro h. pose proof kB_pos as hk. pose proof (bathTemp_pos b) as hT.
  apply Rmult_le_compat_r with (r := bathTemp b) in h; [| lra].
  unfold Rdiv in h. rewrite Rmult_assoc, Rinv_l, Rmult_1_r in h by lra.
  apply Rmult_le_compat_l with (r := kB) in h; [| lra]. nra.
Qed.

(** Information per joule: an erasure obeying the predicate removes at most 1/(k_B T) nats per joule. *)
Theorem informationPerJoule_le (b : HeatBath) (W : R) (p q : ProbDist) :
  0 < W -> SecondLaw (erase (mkErasure b W)) (transformation p q) ->
  (shannon p - shannon q) / (kB * W) <= 1 / (kB * bathTemp b).
Proof.
  intros hW h. pose proof (entropyDrop_joules_le b W p q h) as hc.
  pose proof kB_pos as hk. pose proof (bathTemp_pos b) as hT.
  assert (hkW : 0 < kB * W) by (apply Rmult_lt_0_compat; lra).
  assert (hkT : 0 < kB * bathTemp b) by (apply Rmult_lt_0_compat; lra).
  apply (Rmult_le_reg_r (kB * W * (kB * bathTemp b))); [apply Rmult_lt_0_compat; assumption |].
  replace ((shannon p - shannon q) / (kB * W) * (kB * W * (kB * bathTemp b)))
    with (kB * bathTemp b * (shannon p - shannon q)) by (field; lra).
  replace (1 / (kB * bathTemp b) * (kB * W * (kB * bathTemp b))) with (kB * W) by (field; lra).
  exact hc.
Qed.

(** The cost of b bits: erasing the uniform distribution on 2^b states to a point costs at least b k_B T ln 2. *)
Theorem bitErasure_cost (b : HeatBath) (W : R) (bits : nat) (hn : (0 < 2 ^ bits)%nat) :
  SecondLaw (erase (mkErasure b W)) (transformation (uniformN (2 ^ bits) hn) (diracN (2 ^ bits - 1))) ->
  INR bits * (kB * bathTemp b * ln 2) <= kB * W.
Proof.
  intro h. pose proof (entropyDrop_joules_le b W _ _ h) as hc.
  rewrite shannon_uniformN, shannon_diracN, pow_INR, ln_pow in hc by (simpl; lra).
  replace (INR 2) with 2 in hc by (simpl; ring). lra.
Qed.

(** The cockpit's information-per-joule score: dignity times bits over energy plus one Landauer bit energy. *)
Definition etaCog (dignity bits energy landauerBit : R) : R := dignity * bits / (energy + landauerBit).

Definition honest_spend (T bits energy : R) : Prop := kB * T * ln 2 * bits <= energy.

(** An honest claim scores at most its dignity over the Landauer bit energy. *)
Theorem eta_cog_le_of_honest (dignity bits energy L : R) :
  0 <= dignity -> 0 <= energy -> 0 < L -> L * bits <= energy -> etaCog dignity bits energy L <= dignity / L.
Proof.
  intros hd he hL hh. unfold etaCog.
  assert (hD : 0 < energy + L) by lra.
  replace (dignity * bits / (energy + L)) with (dignity * bits * L * / (L * (energy + L))) by (field; lra).
  replace (dignity / L) with (dignity * (energy + L) * / (L * (energy + L))) by (field; lra).
  apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; lra |]. nra.
Qed.

(** Honest spend from the second law: a claim of b bits whose energy is the work of an erasure of b bits obeying
    the predicate pays the Landauer floor. *)
Theorem honest_spend_of_secondLaw (b : HeatBath) (W : R) (bits : nat) (hn : (0 < 2 ^ bits)%nat) :
  SecondLaw (erase (mkErasure b W)) (transformation (uniformN (2 ^ bits) hn) (diracN (2 ^ bits - 1))) ->
  honest_spend (bathTemp b) (INR bits) (kB * W).
Proof. intro h. unfold honest_spend. pose proof (bitErasure_cost b W bits hn h). lra. Qed.

(** The bound composed over the predicate. *)
Theorem eta_cog_le_of_secondLaw (dignity : R) (b : HeatBath) (W : R) (bits : nat) (hn : (0 < 2 ^ bits)%nat) :
  0 <= dignity -> 0 <= W ->
  SecondLaw (erase (mkErasure b W)) (transformation (uniformN (2 ^ bits) hn) (diracN (2 ^ bits - 1))) ->
  etaCog dignity (INR bits) (kB * W) (kB * bathTemp b * ln 2) <= dignity / (kB * bathTemp b * ln 2).
Proof.
  intros hd hW h. pose proof kB_pos. pose proof (bathTemp_pos b). assert (hln : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
  apply eta_cog_le_of_honest; [exact hd | nra | apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra | exact hln] |].
  pose proof (bitErasure_cost b W bits hn h). lra.
Qed.
