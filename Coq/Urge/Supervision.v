(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* Urge/Supervision.v — BP II §6. Zero Axiom/Admitted. *)

From Stdlib Require Import List Arith Bool.
Require Import UMSTFormal.Urge.Transport.

Inductive SupervisionPhase :=
  | PObserve | PReconcile | PSelfHeal | PVerify | PRecord.

Inductive SupervisionTier := TFast | TSlow.

Definition budget_us (t : SupervisionTier) : nat :=
  match t with
  | TFast => 100000
  | TSlow => 1000000
  end.

Definition phase_order : list SupervisionPhase :=
  PObserve :: PReconcile :: PSelfHeal :: PVerify :: PRecord :: nil.

Lemma phase_order_len : length phase_order = 5.
Proof. reflexivity. Qed.

Definition local_cycle_admissible (ch : Transport) : bool := can_carry ch.

Lemma local_admissible : local_cycle_admissible TLocal = true.
Proof. reflexivity. Qed.

Lemma offline_inadmissible : local_cycle_admissible TOffline = false.
Proof. reflexivity. Qed.

Definition supervision_physics_green : bool := false.
Lemma supervision_physics_green_false : supervision_physics_green = false.
Proof. reflexivity. Qed.
