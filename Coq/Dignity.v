(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Dignity — the dignity scalar on [0, d_max], twin of          *)
(*  Lean/Dignity.lean: d_max = 10, the honest-spend step (dignity rises by  *)
(*  the claimed mutual information, capped at d_max, only when the          *)
(*  measured energy covers the Landauer cost k_B T ln 2 per claimed bit),   *)
(*  and its monotonicity in the claimed information. The step is stated on  *)
(*  the scalar value. Zero Axiom, Parameter or Admitted.                    *)
(* ======================================================================== *)

From Stdlib Require Import Reals Lra.
Require Import UMSTFormal.Process.

Open Scope R_scope.

(** Upper end of the dignity range [0, d_max]. *)
Definition d_max : R := 10.

(** SI Landauer bit energy k_B T ln 2 (J per bit) at temperature [T] (K). *)
Definition landauer_joules_per_bit (T : R) : R := kB * T * ln 2.

(** A dignity scalar in [0, d_max]. *)
Record Dignity : Type := mkDignity {
  value : R;
  value_nonneg : 0 <= value;
  value_bounded : value <= d_max
}.

(** A claimed mutual-information gain (bits) and a measured energy spend (J), both nonnegative. *)
Record DignityClaim : Type := mkClaim {
  delta_mi_bits : R;
  delta_energy_j : R;
  hmi : 0 <= delta_mi_bits;
  he : 0 <= delta_energy_j
}.

(** Honest spend: the Landauer floor of the claimed bits is covered by the measured energy. *)
Definition honest_spend (T : R) (c : DignityClaim) : Prop :=
  landauer_joules_per_bit T * delta_mi_bits c <= delta_energy_j c.

(** One step on the scalar: on honest spend add the claimed information, capped at d_max; otherwise unchanged. *)
Definition dignity_step (T : R) (d : Dignity) (c : DignityClaim) : R :=
  if Rle_dec (landauer_joules_per_bit T * delta_mi_bits c) (delta_energy_j c)
  then Rmin d_max (value d + delta_mi_bits c)
  else value d.

Lemma dignity_step_honest_eq (T : R) (d : Dignity) (c : DignityClaim) :
  honest_spend T c -> dignity_step T d c = Rmin d_max (value d + delta_mi_bits c).
Proof.
  unfold dignity_step, honest_spend. intros h.
  destruct (Rle_dec _ _) as [_ | n]; [reflexivity | contradiction].
Qed.

(** Monotonicity in the claimed information when both steps are honest. *)
Theorem dignity_monotone_under_mi_gain (T : R) (d : Dignity) (c1 c2 : DignityClaim) :
  0 < T -> honest_spend T c1 -> honest_spend T c2 -> delta_mi_bits c1 <= delta_mi_bits c2 ->
  dignity_step T d c1 <= dignity_step T d c2.
Proof.
  intros _ h1 h2 hmi12.
  rewrite (dignity_step_honest_eq T d c1 h1), (dignity_step_honest_eq T d c2 h2).
  unfold Rmin.
  destruct (Rle_dec d_max (value d + delta_mi_bits c1));
  destruct (Rle_dec d_max (value d + delta_mi_bits c2)); lra.
Qed.
