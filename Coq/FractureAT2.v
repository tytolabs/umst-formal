(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: FractureAT2.v                                            *)
(*                                                                        *)
(*  Twin of Lean/Concrete/FractureAT2.lean over exact rationals: the AT2  *)
(*  stored energy g(phi) psi_e with g(phi) = (1 - phi)^2, the crack       *)
(*  energy (c/2)(phi_new^2 - phi^2) spent as dissipation (c = G_c / l), the  *)
(*  irreversible alternate-minimisation step phi_new = max(phi, phi_star),       *)
(*  phi_star = 2 psi_e / (2 psi_e + c), which stays in [0, 1], minimises the  *)
(*  total energy over [phi, 1] and is a SecondLaw transition through the  *)
(*  passive route on the whole domain; Griffith as the passive            *)
(*  inequality; the loading step refused, its missing term W_in.          *)
(* ===================================================================== *)

From Stdlib Require Import QArith Qminmax Lqa.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process UMSTFormal.Convex.PassiveRoute.

Open Scope Q_scope.

Lemma Qsq_mono (a b : Q) : 0 <= a -> a <= b -> a * a <= b * b.
Proof. intros h0 h. apply Qmult_le_compat_nonneg; split; assumption. Qed.

Lemma Qsq_nonneg (y : Q) : 0 <= y * y.
Proof.
  destruct (Qlt_le_dec y 0) as [h | h].
  - setoid_replace (y * y) with ((- y) * (- y)) by ring. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Definition degradation (phi : Q) : Q := (1 - phi) * (1 - phi).
Definition stored (psie phi : Q) : Q := degradation phi * psie.
Definition crackSpent (c phi phi' : Q) : Q := c * (1 # 2) * (phi' * phi' - phi * phi).
Definition total (c psie phi : Q) : Q := stored psie phi + c * (1 # 2) * (phi * phi).
Definition damageTarget (c psie : Q) : Q := 2 * psie / (2 * psie + c).
Definition damageUpdate (c psie phi : Q) : Q := Qmax phi (damageTarget c psie).

Lemma damageTarget_mem (c psie : Q) : 0 < c -> 0 <= psie -> 0 <= damageTarget c psie /\ damageTarget c psie < 1.
Proof.
  intros hc hp. unfold damageTarget. split.
  - apply Qle_shift_div_l; lra.
  - apply Qlt_shift_div_r; lra.
Qed.

(** The total energy is a parabola in phi with vertex phi_star. *)
Lemma total_vertex (c psie x : Q) : 0 < c -> 0 <= psie ->
  total c psie x == total c psie (damageTarget c psie) + (psie + c * (1 # 2)) * ((x - damageTarget c psie) * (x - damageTarget c psie)).
Proof.
  intros hc hp. unfold total, stored, degradation, damageTarget. field.
  intro h. lra.
Qed.

(** The damage step stays in [0, 1], never heals, and minimises the total energy over [phi, 1]. *)
Theorem at2_damage_update (c psie phi : Q) : 0 < c -> 0 <= psie -> 0 <= phi -> phi <= 1 ->
  phi <= damageUpdate c psie phi /\ 0 <= damageUpdate c psie phi /\ damageUpdate c psie phi <= 1 /\
  forall x, phi <= x -> x <= 1 -> total c psie (damageUpdate c psie phi) <= total c psie x.
Proof.
  intros hc hp h0 h1. destruct (damageTarget_mem c psie hc hp) as [ht0 ht1].
  unfold damageUpdate.
  split; [apply Q.le_max_l |]. split; [apply (Qle_trans _ phi); [exact h0 | apply Q.le_max_l] |].
  split; [apply Q.max_lub; lra |].
  intros x hx _. rewrite (total_vertex c psie x hc hp), (total_vertex c psie (Qmax phi (damageTarget c psie)) hc hp).
  assert (ha : 0 <= psie + c * (1 # 2)) by lra.
  set (t := damageTarget c psie) in *. clearbody t.
  destruct (Qlt_le_dec t phi) as [hgt | hle].
  2: { rewrite (Q.max_r phi t hle).
    setoid_replace ((t - t) * (t - t)) with 0 by ring.
    pose proof (Qsq_nonneg (x - t)) as hsq.
    pose proof (Qmult_le_compat_r _ _ _ hsq ha). lra. }
  assert (hge : t <= phi) by (apply Qlt_le_weak; exact hgt).
  rewrite (Q.max_l phi t hge).
  assert (hsq : (phi - t) * (phi - t) <= (x - t) * (x - t)) by (apply Qsq_mono; lra).
  pose proof (Qmult_le_compat_r _ _ _ hsq ha). lra.
Qed.

(** The total energy does not increase on the whole domain [0, 1]. *)
Theorem at2_energy_nonincreasing (c psie phi : Q) : 0 < c -> 0 <= psie -> 0 <= phi -> phi <= 1 ->
  total c psie (damageUpdate c psie phi) <= total c psie phi.
Proof.
  intros hc hp h0 h1. destruct (at2_damage_update c psie phi hc hp h0 h1) as [_ [_ [_ hmin]]].
  apply hmin; lra.
Qed.

(** The two readings agree. *)
Theorem at2_balance_eq_total (c psie phi phi' : Q) :
  (stored psie phi' - stored psie phi) + crackSpent c phi phi' == total c psie phi' - total c psie phi.
Proof. unfold total, crackSpent. ring. Qed.

Lemma crackSpent_nonneg (c phi phi' : Q) : 0 < c -> 0 <= phi -> phi <= phi' -> 0 <= crackSpent c phi phi'.
Proof.
  intros hc h0 h. unfold crackSpent. assert (phi * phi <= phi' * phi') by (apply Qsq_mono; lra).
  apply Qmult_le_0_compat; lra.
Qed.

(** Release of degraded elastic energy by any irreversible step in [0, 1]. *)
Theorem at2_degradation_release_nonneg (psie phi phi' : Q) : 0 <= psie -> phi <= phi' -> phi' <= 1 ->
  0 <= stored psie phi - stored psie phi'.
Proof.
  intros hp h h1. unfold stored, degradation.
  assert (hg : (1 - phi') * (1 - phi') <= (1 - phi) * (1 - phi)) by (apply Qsq_mono; lra).
  pose proof (Qmult_le_compat_r _ _ _ hg hp). lra.
Qed.

(** Griffith: the passive inequality with the crack energy spent holds exactly when the release covers it. *)
Theorem at2_griffith_iff (c psie phi phi' : Q) :
  (stored psie phi' - stored psie phi) + crackSpent c phi phi' <= 0 <-> crackSpent c phi phi' <= stored psie phi - stored psie phi'.
Proof. split; intro; lra. Qed.

(** The damage step is a SecondLaw transition through the passive route. *)
Theorem at2_damage_step_secondLaw (c psie phi rho : Q) : 0 < c -> 0 <= psie -> 0 <= phi -> phi <= 1 ->
  SecondLaw transition (thermodynamic (mkState rho (stored psie phi) 0 0) (mkState rho (stored psie (damageUpdate c psie phi)) 0 0)).
Proof.
  intros hc hp h0 h1.
  destruct (at2_damage_update c psie phi hc hp h0 h1) as [hirr _].
  pose proof (at2_energy_nonincreasing c psie phi hc hp h0 h1) as hE.
  pose proof (at2_balance_eq_total c psie phi (damageUpdate c psie phi)) as hb.
  apply (passive_inequality_secondLaw (crackSpent c phi (damageUpdate c psie phi))); simpl.
  - unfold delta_mass. lra.
  - unfold delta_mass. lra.
  - exact (crackSpent_nonneg c phi _ hc h0 hirr).
  - lra.
Qed.

(** Typed absence, the loading step: raising the strain energy at fixed damage is refused; the missing term is W_in. *)
Theorem at2_loading_refused (psie psie' phi rho rho' : Q) : phi < 1 -> psie < psie' ->
  ~ SecondLaw transition (thermodynamic (mkState rho (stored psie phi) 0 0) (mkState rho' (stored psie' phi) 0 0)).
Proof.
  intros h1 hl hs. simpl in hs. unfold core_admissible in hs. destruct hs as [_ [_ hf]].
  unfold stored, degradation in hf.
  assert (hg : 0 < (1 - phi) * (1 - phi)) by (apply Qmult_lt_0_compat; lra).
  assert (hf' : psie' * ((1 - phi) * (1 - phi)) <= psie * ((1 - phi) * (1 - phi))).
  { setoid_replace (psie' * ((1 - phi) * (1 - phi))) with ((1 - phi) * (1 - phi) * psie') by ring.
    setoid_replace (psie * ((1 - phi) * (1 - phi))) with ((1 - phi) * (1 - phi) * psie) by ring. exact hf. }
  pose proof (proj1 (Qmult_le_r psie' psie _ hg) hf'). lra.
Qed.
