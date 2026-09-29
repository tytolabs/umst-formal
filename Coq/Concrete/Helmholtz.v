(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMSTFormal.Concrete.Helmholtz — Helmholtz ψ-antitone witness (OPC). *)
(*  Discharges global `psi_antitone` for states on the Helmholtz model. *)
(* ================================================================== *)

From Stdlib Require Import QArith.
From Stdlib Require Import Qfield.

Require Import UMSTFormal.Concrete.Gate.
Export UMSTFormal.Concrete.Gate.

Open Scope Q_scope.

Definition helmholtz_state (s : ThermodynamicState) : Prop :=
  free_energy s == helmholtz (hydration s).

Local Lemma Qeq_le_l : forall x y : Q, x == y -> x <= y.
Proof.
  intros x y H. rewrite H. apply Qle_refl.
Qed.

Local Lemma Qeq_le_r : forall x y : Q, x == y -> y <= x.
Proof.
  intros x y H. rewrite H. apply Qle_refl.
Qed.

Lemma psi_antitone_helmholtz :
  forall s1 s2 : ThermodynamicState,
  helmholtz_state s1 ->
  helmholtz_state s2 ->
  hydration s1 <= hydration s2 ->
  free_energy s2 <= free_energy s1.
Proof.
  intros s1 s2 H1 H2 Hhyd.
  unfold helmholtz_state in H1, H2.
  apply Qle_trans with (y := helmholtz (hydration s2)).
  - apply Qeq_le_l; exact H2.
  - apply Qle_trans with (y := helmholtz (hydration s1)).
    + apply helmholtz_antitone; exact Hhyd.
    + apply Qeq_le_r; exact H1.
Qed.
