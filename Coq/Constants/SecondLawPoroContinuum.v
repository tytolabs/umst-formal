(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Constants.SecondLawPoroContinuum — transport, reaction and   *)
(*  poroelastic constants bounded by the second law (twin of                *)
(*  Lean/Constants/SecondLawPoroContinuum.lean).                            *)
(*                                                                          *)
(*  Each theorem takes a passive step as the transition case of SecondLaw:  *)
(*  a step whose dissipation leaves the free energy ([dissipates]) or the   *)
(*  relaxation of a loaded state to the natural state ([relaxation]). The   *)
(*  Biot relations enter as hypotheses on the constants. Each result is a   *)
(*  bound, never a value. Zero Axiom, Parameter or Admitted.                *)
(* ======================================================================== *)

From Stdlib Require Import QArith Qfield Lqa.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.
Require Import UMSTFormal.Constants.SecondLawDissipation UMSTFormal.Constants.SecondLawElastic.

Open Scope Q_scope.

(** A nonzero rational has a positive square. *)
Lemma sq_pos (s : Q) : ~ s == 0 -> 0 < s * s.
Proof.
  intros hs. destruct (Qlt_le_dec s 0) as [hn|hp].
  - nra.
  - assert (0 < s) by (apply Qle_lteq in hp; destruct hp as [hp|hp]; [exact hp | exfalso; apply hs; rewrite hp; reflexivity]).
    nra.
Qed.

(** A nonnegative rational that is not zero is positive. *)
Lemma nonneg_nonzero_pos (x : Q) : 0 <= x -> ~ x == 0 -> 0 < x.
Proof.
  intros h hx. apply Qle_lteq in h. destruct h as [h|h]; [exact h | exfalso; apply hx; rewrite h; reflexivity].
Qed.

(** Reaction rate: a reaction with affinity A > 0 advancing at rate r over dt > 0 dissipates A * r * dt; the second
    law gives r >= 0. *)
Theorem reaction_rate_nonneg (rho rho' psi A r dt : Q) :
  0 < A -> 0 < dt -> SecondLaw transition (dissipates rho rho' psi (A * r * dt)) -> 0 <= r.
Proof.
  intros hA hdt h. apply dissipates_nonneg in h.
  assert (hq : 0 < A * dt) by (apply Qmult_lt_0_compat; assumption).
  assert (e : A * r * dt == r * (A * dt)) by ring. rewrite e in h.
  destruct (Qlt_le_dec r 0) as [hr|hr]; [nra | exact hr].
Qed.

(** Rate constant: with affinity A > 0 and rate law r = k * g, g > 0, the step dissipates A * (k * g) * dt; the
    second law gives k >= 0. *)
Theorem reaction_rate_constant_nonneg (rho rho' psi A k g dt : Q) :
  0 < A -> 0 < g -> 0 < dt -> SecondLaw transition (dissipates rho rho' psi (A * (k * g) * dt)) -> 0 <= k.
Proof.
  intros hA hg hdt h. apply dissipates_nonneg in h.
  assert (hq : 0 < A * g * dt) by (apply Qmult_lt_0_compat; [apply Qmult_lt_0_compat |]; assumption).
  assert (e : A * (k * g) * dt == k * (A * g * dt)) by ring. rewrite e in h.
  destruct (Qlt_le_dec k 0) as [hk|hk]; [nra | exact hk].
Qed.

(** Diffusivity: Fickian diffusion at a gradient g <> 0 with thermodynamic factor chi > 0 over dt > 0 dissipates
    D * chi * g^2 * dt; the second law gives D >= 0. *)
Theorem fick_diffusivity_nonneg (rho rho' psi D chi g dt : Q) :
  0 < chi -> ~ g == 0 -> 0 < dt ->
  SecondLaw transition (dissipates rho rho' psi (D * chi * (g * g) * dt)) -> 0 <= D.
Proof.
  intros hchi hg hdt h. apply dissipates_nonneg in h.
  pose proof (sq_pos g hg) as hg2.
  assert (hq : 0 < chi * (g * g) * dt) by (apply Qmult_lt_0_compat; [apply Qmult_lt_0_compat |]; assumption).
  assert (e : D * chi * (g * g) * dt == D * (chi * (g * g) * dt)) by ring. rewrite e in h.
  destruct (Qlt_le_dec D 0) as [hD|hD]; [nra | exact hD].
Qed.

(** Permeability: Darcy flow at a pressure gradient g <> 0 through a fluid of viscosity mu > 0 over dt > 0
    dissipates (kappa / mu) * g^2 * dt; the second law gives kappa >= 0. *)
Theorem darcy_permeability_nonneg (rho rho' psi kappa mu g dt : Q) :
  0 < mu -> ~ g == 0 -> 0 < dt ->
  SecondLaw transition (dissipates rho rho' psi (kappa / mu * (g * g) * dt)) -> 0 <= kappa.
Proof.
  intros hmu hg hdt h. apply dissipates_nonneg in h.
  pose proof (sq_pos g hg) as hg2.
  assert (hinv : 0 < / mu) by (apply Qinv_lt_0_compat; exact hmu).
  assert (hq : 0 < / mu * (g * g) * dt) by (apply Qmult_lt_0_compat; [apply Qmult_lt_0_compat |]; assumption).
  assert (e : kappa / mu * (g * g) * dt == kappa * (/ mu * (g * g) * dt)) by (unfold Qdiv; ring). rewrite e in h.
  destruct (Qlt_le_dec kappa 0) as [hk|hk]; [nra | exact hk].
Qed.

(** Biot coefficient: with K == Ks * (1 - b) and b - phi == Ks * n (Ks > 0), a drained mode storing 1/2 K s^2 and a
    pore mode storing 1/2 n s^2 that relax passively at a strain s <> 0 give phi <= b <= 1. *)
Theorem biot_coefficient_bounds (rho rho' K Ks n phi b s : Q) :
  ~ s == 0 -> 0 < Ks -> K == Ks * (1 - b) -> b - phi == Ks * n ->
  SecondLaw transition (relaxation rho rho' ((1#2) * K * (s * s))) ->
  SecondLaw transition (relaxation rho rho' ((1#2) * n * (s * s))) ->
  phi <= b /\ b <= 1.
Proof.
  intros hs hKs hK hn hdrained hpore.
  pose proof (relaxation_stiffness_nonneg _ _ _ _ hs hdrained) as hK0.
  pose proof (relaxation_stiffness_nonneg _ _ _ _ hs hpore) as hn0.
  split.
  - assert (0 <= Ks * n) by (apply Qmult_le_0_compat; lra). lra.
  - destruct (Qlt_le_dec 1 b) as [hb|hb]; [exfalso | exact hb].
    assert (Ks * (1 - b) < 0) by nra. lra.
Qed.

(** Biot storage: with m == n + phi * cf, phi > 0, a pore mode storing 1/2 n s^2 and a fluid mode storing
    1/2 cf s^2 (cf <> 0) that relax passively at a strain s <> 0, the storage coefficient m = 1/M is positive and so
    is the Biot modulus M with M * m == 1. *)
Theorem biot_storage_pos (rho rho' n cf phi m M s : Q) :
  ~ s == 0 -> 0 < phi -> ~ cf == 0 -> m == n + phi * cf -> M * m == 1 ->
  SecondLaw transition (relaxation rho rho' ((1#2) * n * (s * s))) ->
  SecondLaw transition (relaxation rho rho' ((1#2) * cf * (s * s))) ->
  0 < m /\ 0 < M.
Proof.
  intros hs hphi hcf hm hM hpore hfluid.
  pose proof (relaxation_stiffness_nonneg _ _ _ _ hs hpore) as hn0.
  pose proof (nonneg_nonzero_pos _ (relaxation_stiffness_nonneg _ _ _ _ hs hfluid) hcf) as hcf0.
  assert (hm0 : 0 < m) by (rewrite hm; assert (0 < phi * cf) by (apply Qmult_lt_0_compat; assumption); lra).
  split; [exact hm0 |].
  destruct (Qlt_le_dec 0 M) as [hp|hp]; [exact hp | exfalso].
  assert (M * m <= 0) by nra. lra.
Qed.

(** Isotropic moduli: an isotropic solid storing 1/2 K e^2 + 1/2 G g^2 with K <> 0 and G <> 0 that relaxes
    passively from every (e, g) has K > 0, G > 0 and -1 < nu < 1/2. *)
Theorem isotropic_moduli_pos (rho rho' K G : Q) :
  ~ K == 0 -> ~ G == 0 ->
  (forall e g, SecondLaw transition (relaxation rho rho' ((1#2) * K * (e * e) + (1#2) * G * (g * g)))) ->
  0 < K /\ 0 < G /\ -1 < poissonRatio K G /\ poissonRatio K G < 1#2.
Proof.
  intros hK hG h. destruct (twoMode_stiffness_nonneg _ _ _ _ h) as [hK0 hG0].
  pose proof (nonneg_nonzero_pos _ hK0 hK) as hKp.
  pose proof (nonneg_nonzero_pos _ hG0 hG) as hGp.
  assert (hd : 0 < 2 * (3 * K + G)) by lra.
  unfold poissonRatio. split; [exact hKp |]. split; [exact hGp |]. split.
  - apply Qlt_shift_div_l; [exact hd | lra].
  - apply Qlt_shift_div_r; [exact hd | lra].
Qed.
