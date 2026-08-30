(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* UMST-Formal: Urge/Transport.v — BP II §5.3 transport seam. Zero Axiom/Admitted. *)

From Stdlib Require Import Arith List Bool.
Require Import UMSTFormal.Urge.AppendOnly.

Inductive Transport :=
  | TLocal | TGit | TMesh | TRemote | TOffline.

Definition can_carry (t : Transport) : bool :=
  match t with
  | TOffline => false
  | _ => true
  end.

Inductive TransportError := OfflineCannotCarry.

Definition admit_carry (t : Transport) : option TransportError :=
  if can_carry t then None else Some OfflineCannotCarry.

Lemma local_can_carry : can_carry TLocal = true.
Proof. reflexivity. Qed.

Lemma offline_cannot_carry : can_carry TOffline = false.
Proof. reflexivity. Qed.

Lemma admit_offline_refuses : admit_carry TOffline = Some OfflineCannotCarry.
Proof. reflexivity. Qed.

Lemma admit_local_ok : admit_carry TLocal = None.
Proof. reflexivity. Qed.

Definition channel_set : list Transport :=
  TLocal :: TGit :: TMesh :: TRemote :: TOffline :: nil.

Lemma channel_set_len : length channel_set = 5.
Proof. reflexivity. Qed.

Definition transport_physics_green : bool := false.

Lemma transport_physics_green_false : transport_physics_green = false.
Proof. reflexivity. Qed.
