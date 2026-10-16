(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: UnfoldProxStepLaws.v                                     *)
(*                                                                        *)
(*  Twin of Lean/UnfoldProxStepLaws.lean over exact rationals (law L3):   *)
(*  a step minimising psi x - w x + tau phi (d x), with phi 0 = 0 and     *)
(*  d x0 = 0, satisfies psi x+ - psi x0 + tau phi (d x+) <= w x+ - w x0;  *)
(*  with phi >= 0 the free-energy change is at most the supplied work; a  *)
(*  candidate breaking the inequality is no minimiser; on a scalar state  *)
(*  supporting lines of the convex psi and phi at a stationary point give *)
(*  the same inequality, and the slope of phi makes b v >= phi v >= 0.    *)
(* ===================================================================== *)

From Stdlib Require Import QArith Lqa.

Open Scope Q_scope.

Section Prox.

Variable X : Type.

Definition incremental (psi w : X -> Q) (phi : Q -> Q) (d : X -> Q) (tau : Q) (x : X) : Q :=
  psi x - w x + tau * phi (d x).

Definition isProxStep (psi w : X -> Q) (phi : Q -> Q) (d : X -> Q) (tau : Q) (xp : X) : Prop :=
  forall x, incremental psi w phi d tau xp <= incremental psi w phi d tau x.

(** L3 from minimality. *)
Theorem prox_step_le (psi w : X -> Q) (phi : Q -> Q) (d : X -> Q) (tau : Q) (x0 xp : X) :
  phi 0 == 0 -> d x0 = 0 -> isProxStep psi w phi d tau xp ->
  psi xp - psi x0 + tau * phi (d xp) <= w xp - w x0.
Proof.
  intros hphi0 hd0 hmin. pose proof (hmin x0) as h. unfold incremental in h. rewrite hd0 in h.
  assert (hz : tau * phi 0 == 0) by (rewrite hphi0; ring).
  rewrite hz in h. lra.
Qed.

(** L3, the inequality Delta F <= W_in, with a non-negative dissipation potential. *)
Theorem prox_step_deltaF_le (psi w : X -> Q) (phi : Q -> Q) (d : X -> Q) (tau : Q) (x0 xp : X) :
  0 <= tau -> (forall v, 0 <= phi v) -> phi 0 == 0 -> d x0 = 0 -> isProxStep psi w phi d tau xp ->
  psi xp - psi x0 <= w xp - w x0.
Proof.
  intros ht hphi hphi0 hd0 hmin. pose proof (prox_step_le psi w phi d tau x0 xp hphi0 hd0 hmin) as h.
  pose proof (Qmult_le_0_compat _ _ ht (hphi (d xp))) as hD. lra.
Qed.

(** L3 refusal: a candidate that breaks the discrete inequality is no minimiser. *)
Theorem prox_step_refused (psi w : X -> Q) (phi : Q -> Q) (d : X -> Q) (tau : Q) (x0 xp : X) :
  phi 0 == 0 -> d x0 = 0 -> w xp - w x0 < psi xp - psi x0 + tau * phi (d xp) -> ~ isProxStep psi w phi d tau xp.
Proof.
  intros hphi0 hd0 hanti hmin. pose proof (prox_step_le psi w phi d tau x0 xp hphi0 hd0 hmin) as h. lra.
Qed.

End Prox.

(** L3 from stationarity (scalar state, tau v = x+ - x0). *)
Theorem prox_step_stationary_le (psi phi : Q -> Q) (tau x0 xp v a b f : Q) :
  tau * v == xp - x0 -> phi 0 == 0 -> 0 <= tau ->
  psi x0 >= psi xp + a * (x0 - xp) -> phi 0 >= phi v + b * (0 - v) -> a + b == f ->
  psi xp - psi x0 + tau * phi v <= f * (xp - x0).
Proof.
  intros hv hphi0 ht hpsi hphi hstat. rewrite hphi0 in hphi.
  assert (h1 : phi v <= b * v) by nra.
  assert (h2 : tau * phi v <= tau * (b * v)) by (setoid_replace (tau * phi v) with (phi v * tau) by ring; setoid_replace (tau * (b * v)) with (b * v * tau) by ring; apply Qmult_le_compat_r; assumption).
  rewrite <- hstat. nra.
Qed.

(** The slope of a convex phi with phi 0 = 0 and phi >= 0 makes the dissipation rate non-negative. *)
Theorem prox_dissipation_rate_nonneg (phi : Q -> Q) (v b : Q) :
  phi 0 == 0 -> 0 <= phi v -> phi 0 >= phi v + b * (0 - v) -> phi v <= b * v /\ 0 <= b * v.
Proof. intros hphi0 hv hphi. rewrite hphi0 in hphi. split; nra. Qed.
