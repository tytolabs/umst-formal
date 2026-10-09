(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Constants.SecondLawDissipation — dissipation coefficients    *)
(*  bounded by the second law (twin of                                      *)
(*  Lean/Constants/SecondLawDissipation.lean).                              *)
(*                                                                          *)
(*  A passive step whose dissipated energy D leaves the free energy         *)
(*  (psi_new = psi_old - D) satisfies the transition case of SecondLaw only *)
(*  when D >= 0; writing D as a coefficient times a positive measure of the *)
(*  step bounds the coefficient. Coq carries the energies as rationals, so  *)
(*  the loss-modulus cycle measure pi * eps0^2 enters as a positive q. Each *)
(*  result is a bound, never a value. Zero Axiom, Parameter or Admitted.    *)
(* ======================================================================== *)

From Stdlib Require Import QArith Qfield Qabs Lqa.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.

Open Scope Q_scope.

(** A passive step from free energy [psi] that dissipates [d]. *)
Definition dissipates (rho rho' psi d : Q) : Prior :=
  thermodynamic (mkState rho psi 0 0) (mkState rho' (psi - d) 0 0).

Lemma dissipates_nonneg (rho rho' psi d : Q) :
  SecondLaw transition (dissipates rho rho' psi d) -> 0 <= d.
Proof. simpl. unfold core_admissible. simpl. intros [_ [_ h]]. lra. Qed.

(** Dissipation coefficient: a passive step dissipating c * q (q > 0) obeys the second law only when c >= 0. *)
Theorem dissipation_coefficient_nonneg (rho rho' psi c q : Q) :
  0 < q -> SecondLaw transition (dissipates rho rho' psi (c * q)) -> 0 <= c.
Proof.
  intros hq h. apply dissipates_nonneg in h.
  destruct (Qlt_le_dec c 0) as [hc|hc]; [nra | exact hc].
Qed.

(** Viscosity: a dashpot at rate r <> 0 over dt > 0 dissipates eta * r^2 * dt; the second law gives eta >= 0. *)
Theorem viscosity_nonneg (rho rho' psi eta r dt : Q) :
  ~ r == 0 -> 0 < dt -> SecondLaw transition (dissipates rho rho' psi (eta * (r * r) * dt)) -> 0 <= eta.
Proof.
  intros hr hdt h.
  assert (hr2 : 0 < r * r).
  { destruct (Qlt_le_dec r 0) as [hn|hp].
    - nra.
    - assert (0 < r) by (apply Qle_lteq in hp; destruct hp as [hp|hp]; [exact hp | exfalso; apply hr; rewrite hp; reflexivity]).
      nra. }
  apply (dissipation_coefficient_nonneg rho rho' psi eta (r * r * dt)); [nra |].
  simpl in h |- *. unfold core_admissible in h |- *. simpl in h |- *.
  setoid_replace (eta * (r * r * dt)) with (eta * (r * r) * dt) by ring. exact h.
Qed.

(** Bingham fluid: dissipating (tau0 * |r| + etap * r^2) * dt at every rate r under the second law gives a yield
    stress tau0 >= 0 and a plastic viscosity etap >= 0. *)
Theorem bingham_nonneg (rho rho' psi tau0 etap dt : Q) :
  0 < dt ->
  (forall r, SecondLaw transition (dissipates rho rho' psi ((tau0 * Qabs r + etap * (r * r)) * dt))) ->
  0 <= tau0 /\ 0 <= etap.
Proof.
  intros hdt h.
  (* At every positive rate the dissipation per unit rate, tau0 + etap * r, is nonnegative. *)
  assert (per : forall r, 0 < r -> 0 <= tau0 + etap * r).
  { intros r hr.
    pose proof (dissipation_coefficient_nonneg _ _ _ _ _ hdt (h r)) as hc.
    rewrite Qabs_pos in hc by lra.
    destruct (Qlt_le_dec (tau0 + etap * r) 0) as [c|c]; [nra | exact c]. }
  split.
  - destruct (Qlt_le_dec tau0 0) as [ht|ht]; [exfalso | exact ht].
    set (m := Qabs etap + 1).
    assert (hm : 0 < m) by (unfold m; pose proof (Qabs_nonneg etap); lra).
    set (r := - tau0 / (2 * m)).
    assert (hr : 0 < r) by (unfold r; apply Qlt_shift_div_l; lra).
    assert (hmr : m * r == - tau0 / 2) by (unfold r; field; intro c; lra).
    assert (hle : etap * r <= Qabs etap * r).
    { apply Qmult_le_compat_r; [apply Qle_Qabs | lra]. }
    pose proof (per r hr) as p.
    assert (Qabs etap * r < m * r) by (unfold m; lra).
    assert (hmr' : m * r == - tau0 * (1 # 2)) by (rewrite hmr; field).
    lra.
  - destruct (Qlt_le_dec etap 0) as [he|he]; [exfalso | exact he].
    set (r := 2 * (Qabs tau0 + 1) / - etap).
    assert (hr : 0 < r).
    { unfold r. apply Qlt_shift_div_l; [lra |]. pose proof (Qabs_nonneg tau0). lra. }
    assert (her : etap * r == - (2 * (Qabs tau0 + 1))) by (unfold r; field; intro c; lra).
    pose proof (per r hr) as p.
    pose proof (Qle_Qabs tau0). pose proof (Qabs_nonneg tau0).
    lra.
Qed.

(** Loss modulus: a harmonic cycle with positive measure q (pi * eps0^2) that dissipates E'' * q obeys the second
    law only when E'' >= 0; for a storage modulus E' > 0 the loss factor E''/E' is nonnegative. *)
Theorem lossModulus_nonneg (rho rho' psi E' E'' q : Q) :
  0 < q -> 0 < E' -> SecondLaw transition (dissipates rho rho' psi (E'' * q)) -> 0 <= E'' /\ 0 <= E'' / E'.
Proof.
  intros hq hE h. pose proof (dissipation_coefficient_nonneg _ _ _ _ _ hq h) as h0.
  split; [exact h0 | apply Qle_shift_div_l; lra].
Qed.
