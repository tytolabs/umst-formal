(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Constants.SecondLawRestitution — the coefficient of          *)
(*  restitution bounded by the second law (twin of                          *)
(*  ConvexPhiChannels.restitution_le_one and                                *)
(*  restitution_energy_loss_nonneg in Lean).                                *)
(*                                                                          *)
(*  A passive impact has free energy 1/2 mu v^2 before and                  *)
(*  1/2 mu (e v)^2 after; as a transition case of SecondLaw it forces       *)
(*  e <= 1 for e >= 0, and the kinetic energy lost is nonnegative. The      *)
(*  result is a bound, never a value. Zero Axiom, Parameter or Admitted.    *)
(* ======================================================================== *)

From Stdlib Require Import QArith Lqa.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.

Open Scope Q_scope.

(** A passive impact of a body with reduced mass [mu] at speed [v] and restitution [e]. *)
Definition impact (rho rho' mu v e : Q) : Prior :=
  thermodynamic (mkState rho ((1#2) * mu * (v * v)) 0 0) (mkState rho' ((1#2) * mu * ((e * v) * (e * v))) 0 0).

(** Passive restitution: the impact obeys the second law only with e <= 1 (for e >= 0, mu v^2 > 0). *)
Theorem restitution_le_one (rho rho' mu v e : Q) :
  0 <= e -> 0 < mu * (v * v) -> SecondLaw transition (impact rho rho' mu v e) -> e <= 1.
Proof.
  intros he hpos h. simpl in h. unfold core_admissible in h. simpl in h. destruct h as [_ [_ hd]].
  destruct (Qlt_le_dec 1 e) as [c|c]; [exfalso | exact c].
  assert (h1 : 1 < e * e) by nra.
  nra.
Qed.

(** The kinetic energy lost in a passive impact, 1/2 mu v^2 (1 - e^2), is nonnegative under the second law. *)
Theorem restitution_energy_loss_nonneg (rho rho' mu v e : Q) :
  SecondLaw transition (impact rho rho' mu v e) -> 0 <= (1#2) * mu * (v * v) * (1 - e * e).
Proof.
  intros h. simpl in h. unfold core_admissible in h. simpl in h. destruct h as [_ [_ hd]]. nra.
Qed.
