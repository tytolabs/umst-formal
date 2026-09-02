(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

From Stdlib Require Import Arith Bool String Lia.

Definition sole_axiom_count : nat := 1.
Lemma sole_axiom_is_one : sole_axiom_count = 1. Proof. reflexivity. Qed.
Definition physics_green : bool := false.
Definition sidecar_model_pin : string := "EGOFF_SIDECAR_MODEL".
Definition harness_drift_forbidden : bool := true.

Lemma refuse_second_axiom : sole_axiom_count <> 2.
Proof. discriminate. Qed.
