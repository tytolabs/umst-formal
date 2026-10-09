(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Constants.SecondLawSolidInelastic — material parameters of   *)
(*  an inelastic solid bounded by the second law (twin of                   *)
(*  Lean/Constants/SecondLawSolidInelastic.lean).                           *)
(*                                                                          *)
(*  Each hypothesis is the transition case of SecondLaw: the relaxation of  *)
(*  a loaded state to its natural state, or a passive step that dissipates  *)
(*  energy out of the free energy. Coq carries the energies as rationals:   *)
(*  a power sigma^n, a root sqrt(f_c) and the toughness radicand enter as   *)
(*  positive rationals or as the product E * G_c. Each result is a bound,   *)
(*  never a value. Zero Axiom, Parameter or Admitted.                       *)
(* ======================================================================== *)

From Stdlib Require Import QArith Qfield Lqa.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.
Require Import UMSTFormal.Constants.SecondLawElastic UMSTFormal.Constants.SecondLawDissipation.

Open Scope Q_scope.

(** Free energy of a plastic strain x and a hardening variable y with modulus k and cross coupling c. *)
Definition coupledWell (k c x y : Q) : Q := (1#2) * k * (x * x + y * y + 2 * c * x * y).

(** Coupled well: relaxing passively from every (x, y), with k <> 0, gives k > 0 and -1 <= c <= 1. *)
Theorem coupledWell_bounds (rho rho' k c : Q) :
  ~ k == 0 ->
  (forall x y, SecondLaw transition (relaxation rho rho' (coupledWell k c x y))) ->
  0 < k /\ -1 <= c /\ c <= 1.
Proof.
  intros hk h.
  pose proof (relaxation_nonneg _ _ _ (h 1 0)) as h10.
  pose proof (relaxation_nonneg _ _ _ (h 1 1)) as h11.
  pose proof (relaxation_nonneg _ _ _ (h 1 (-1))) as h1m.
  unfold coupledWell in h10, h11, h1m.
  assert (kpos : 0 < k).
  { destruct (Qlt_le_dec k 0) as [hn|hp]; [exfalso; nra |].
    apply Qle_lteq in hp. destruct hp as [hp|hp]; [exact hp | exfalso; apply hk; rewrite hp; reflexivity]. }
  split; [exact kpos | split].
  - destruct (Qlt_le_dec c (-1)) as [hc|hc]; [exfalso; nra | exact hc].
  - destruct (Qlt_le_dec 1 c) as [hc|hc]; [exfalso; nra | exact hc].
Qed.

(** Double well: a phase field phi not 0 or 1 storing k * phi^2 * (1 - phi)^2 that relaxes passively has k >= 0. *)
Theorem doubleWell_modulus_nonneg (rho rho' k phi : Q) :
  ~ phi == 0 -> ~ phi == 1 ->
  SecondLaw transition (relaxation rho rho' (k * (phi * phi * ((1 - phi) * (1 - phi))))) -> 0 <= k.
Proof.
  intros h0 h1 h. apply relaxation_nonneg in h.
  assert (sq : forall z, ~ z == 0 -> 0 < z * z).
  { intros z hz. destruct (Qlt_le_dec z 0) as [hn|hp].
    - nra.
    - assert (0 < z) by (apply Qle_lteq in hp; destruct hp as [hp|hp]; [exact hp | exfalso; apply hz; rewrite hp; reflexivity]).
      nra. }
  assert (ha : 0 < phi * phi) by (apply sq; exact h0).
  assert (hb : 0 < (1 - phi) * (1 - phi)) by (apply sq; intro c; apply h1; lra).
  assert (hq : 0 < phi * phi * ((1 - phi) * (1 - phi))) by (apply Qmult_lt_0_compat; assumption).
  destruct (Qlt_le_dec k 0) as [hk|hk]; [exfalso; nra | exact hk].
Qed.

(** Griffith fracture energy: a crack extension dA > 0 dissipating G_c * dA obeys the second law only when
    G_c >= 0. *)
Theorem griffith_fracture_energy_nonneg (rho rho' psi Gc dA : Q) :
  0 < dA -> SecondLaw transition (dissipates rho rho' psi (Gc * dA)) -> 0 <= Gc.
Proof. intros hA h. exact (dissipation_coefficient_nonneg _ _ _ _ _ hA h). Qed.

(** Fracture toughness: with G_c >= 0 from a crack extension and E > 0 from the relaxation of a body held at a
    stress sigma <> 0, the radicand of K = sqrt(E * G_c) is nonnegative. *)
Theorem griffith_toughness_nonneg (rho rho' psi Gc dA E sigma : Q) :
  0 < dA -> ~ sigma == 0 -> ~ E == 0 ->
  SecondLaw transition (dissipates rho rho' psi (Gc * dA)) ->
  SecondLaw transition (relaxation rho rho' ((sigma * sigma) / (2 * E))) ->
  0 <= E * Gc.
Proof.
  intros hA hs hE hG hR.
  pose proof (griffith_fracture_energy_nonneg _ _ _ _ _ hA hG) as g.
  pose proof (relaxation_modulus_pos _ _ _ _ hs hE hR) as e.
  apply Qmult_le_0_compat; lra.
Qed.

(** Norton creep: steady creep at stress sigma > 0 with rate A * p (p = sigma^n > 0) over dt > 0 dissipates
    sigma * (A * p) * dt; the second law gives A >= 0. *)
Theorem norton_coefficient_nonneg (rho rho' psi A sigma p dt : Q) :
  0 < sigma -> 0 < p -> 0 < dt ->
  SecondLaw transition (dissipates rho rho' psi (sigma * (A * p) * dt)) -> 0 <= A.
Proof.
  intros hs hp hdt h.
  assert (hq : 0 < sigma * p * dt) by (apply Qmult_lt_0_compat; [apply Qmult_lt_0_compat |]; assumption).
  apply (dissipation_coefficient_nonneg rho rho' psi A (sigma * p * dt) hq).
  simpl in h |- *. unfold core_admissible in h |- *. simpl in h |- *.
  setoid_replace (A * (sigma * p * dt)) with (sigma * (A * p) * dt) by ring. exact h.
Qed.

(** Parabolic scaling: a scale of thickness x > 0 growing at kp / (2 x) under a reaction affinity a > 0 over dt > 0
    dissipates a * (kp / (2 x)) * dt; the second law gives kp >= 0. *)
Theorem parabolic_rate_nonneg (rho rho' psi a kp x dt : Q) :
  0 < a -> 0 < x -> 0 < dt ->
  SecondLaw transition (dissipates rho rho' psi (a * (kp / (2 * x)) * dt)) -> 0 <= kp.
Proof.
  intros ha hx hdt h.
  assert (hq : 0 < a / (2 * x) * dt).
  { apply Qmult_lt_0_compat; [apply Qlt_shift_div_l; lra | exact hdt]. }
  apply (dissipation_coefficient_nonneg rho rho' psi kp (a / (2 * x) * dt) hq).
  simpl in h |- *. unfold core_admissible in h |- *. simpl in h |- *.
  setoid_replace (kp * (a / (2 * x) * dt)) with (a * (kp / (2 * x)) * dt) by (field; intro c; lra). exact h.
Qed.

(** Frictional bond: a fibre whose bond stress is b * r (r = sqrt f_c > 0) sliding over a slip area s > 0
    dissipates b * r * s; the second law gives b >= 0. *)
Theorem frictional_bond_nonneg (rho rho' psi b r s : Q) :
  0 < r -> 0 < s -> SecondLaw transition (dissipates rho rho' psi (b * r * s)) -> 0 <= b.
Proof.
  intros hr hs h.
  assert (hq : 0 < r * s) by (apply Qmult_lt_0_compat; assumption).
  apply (dissipation_coefficient_nonneg rho rho' psi b (r * s) hq).
  simpl in h |- *. unfold core_admissible in h |- *. simpl in h |- *.
  setoid_replace (b * (r * s)) with (b * r * s) by ring. exact h.
Qed.
