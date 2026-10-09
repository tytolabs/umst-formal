(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Constants.SecondLawElastic — elastic moduli bounded by the    *)
(*  second law (twin of Lean/Constants/SecondLawElastic.lean).               *)
(*                                                                          *)
(*  A linear-elastic body loaded away from its natural state stores free    *)
(*  energy; released, it relaxes passively to the natural state (free       *)
(*  energy zero). Each theorem takes that relaxation as the transition case *)
(*  of SecondLaw and concludes a bound on a modulus. Each result is a bound, *)
(*  never a value. Zero Axiom, Parameter or Admitted.                       *)
(* ======================================================================== *)

From Stdlib Require Import QArith Qfield Lqa.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.

Open Scope Q_scope.

(** The relaxation of a state of free energy [psi] to the natural state. *)
Definition relaxation (rho rho' psi : Q) : Prior :=
  thermodynamic (mkState rho psi 0 0) (mkState rho' 0 0 0).

Lemma relaxation_nonneg (rho rho' psi : Q) :
  SecondLaw transition (relaxation rho rho' psi) -> 0 <= psi.
Proof. simpl. unfold core_admissible. simpl. tauto. Qed.

(** Stiffness: a mode storing 1/2 k s^2 at a strain s <> 0 that relaxes passively has k >= 0. *)
Theorem relaxation_stiffness_nonneg (rho rho' k s : Q) :
  ~ s == 0 -> SecondLaw transition (relaxation rho rho' ((1#2) * k * (s * s))) -> 0 <= k.
Proof.
  intros hs h. apply relaxation_nonneg in h.
  assert (hs2 : 0 < s * s).
  { destruct (Qlt_le_dec s 0) as [hn|hp].
    - nra.
    - assert (0 < s) by (apply Qle_lteq in hp; destruct hp as [hp|hp]; [exact hp | exfalso; apply hs; rewrite hp; reflexivity]).
      nra. }
  destruct (Qlt_le_dec k 0) as [hk|hk]; [nra | exact hk].
Qed.

(** Modulus: a body held at stress sigma <> 0 by a modulus E <> 0 stores sigma^2/(2E); its relaxation forces
    E > 0. *)
Theorem relaxation_modulus_pos (rho rho' E sigma : Q) :
  ~ sigma == 0 -> ~ E == 0 ->
  SecondLaw transition (relaxation rho rho' ((sigma * sigma) / (2 * E))) -> 0 < E.
Proof.
  intros hs hE h. apply relaxation_nonneg in h.
  assert (hs2 : 0 < sigma * sigma).
  { destruct (Qlt_le_dec sigma 0) as [hn|hp].
    - nra.
    - assert (0 < sigma) by (apply Qle_lteq in hp; destruct hp as [hp|hp]; [exact hp | exfalso; apply hs; rewrite hp; reflexivity]).
      nra. }
  destruct (Qlt_le_dec E 0) as [hn|hp].
  - exfalso.
    assert (hd : 0 < - (2 * E)) by lra.
    assert (hq : (sigma * sigma) / (2 * E) == - ((sigma * sigma) / (- (2 * E)))) by (field; intro c; apply hE; lra).
    rewrite hq in h.
    assert (0 < (sigma * sigma) / (- (2 * E))) by (apply Qlt_shift_div_l; [exact hd | lra]).
    lra.
  - apply Qle_lteq in hp. destruct hp as [hp|hp]; [exact hp | exfalso; apply hE; rewrite hp; reflexivity].
Qed.

(** Two modes: 1/2 a x^2 + 1/2 b y^2 relaxing passively from every (x, y) gives a >= 0 and b >= 0. *)
Theorem twoMode_stiffness_nonneg (rho rho' a b : Q) :
  (forall x y, SecondLaw transition (relaxation rho rho' ((1#2) * a * (x * x) + (1#2) * b * (y * y)))) ->
  0 <= a /\ 0 <= b.
Proof.
  intros h.
  pose proof (relaxation_nonneg _ _ _ (h 1 0)) as ha.
  pose proof (relaxation_nonneg _ _ _ (h 0 1)) as hb.
  split; nra.
Qed.

(** Poisson ratio and Young's modulus of an isotropic solid from its bulk modulus K and shear modulus G. *)
Definition poissonRatio (K G : Q) : Q := (3 * K - 2 * G) / (2 * (3 * K + G)).
Definition youngModulus (K G : Q) : Q := 9 * K * G / (3 * K + G).

(** Poisson ratio: an isotropic solid storing 1/2 K e^2 + 1/2 G g^2 that relaxes passively from every
    volumetric strain e and shear g, with 3K + G > 0, has -1 <= nu <= 1/2. *)
Theorem isotropic_poisson_bounds (rho rho' K G : Q) :
  0 < 3 * K + G ->
  (forall e g, SecondLaw transition (relaxation rho rho' ((1#2) * K * (e * e) + (1#2) * G * (g * g)))) ->
  -1 <= poissonRatio K G /\ poissonRatio K G <= 1#2.
Proof.
  intros hpos h. destruct (twoMode_stiffness_nonneg _ _ _ _ h) as [hK hG].
  assert (hd : 0 < 2 * (3 * K + G)) by lra.
  unfold poissonRatio. split.
  - apply Qle_shift_div_l; [exact hd | lra].
  - apply Qle_shift_div_r; [exact hd | lra].
Qed.

(** Young's modulus: under the same relaxation, E = 9KG/(3K + G) >= 0. *)
Theorem isotropic_young_nonneg (rho rho' K G : Q) :
  0 < 3 * K + G ->
  (forall e g, SecondLaw transition (relaxation rho rho' ((1#2) * K * (e * e) + (1#2) * G * (g * g)))) ->
  0 <= youngModulus K G.
Proof.
  intros hpos h. destruct (twoMode_stiffness_nonneg _ _ _ _ h) as [hK hG].
  unfold youngModulus. apply Qle_shift_div_l; [exact hpos | nra].
Qed.

(** Standard linear solid: storing 1/2 Ginf eps^2 + 1/2 G1 xi^2 and relaxing passively from every total strain
    and arm strain, 0 <= Ginf <= Ginf + G1, the instantaneous modulus. *)
Theorem sls_relaxed_le_instantaneous (rho rho' Ginf G1 : Q) :
  (forall eps xi, SecondLaw transition (relaxation rho rho' ((1#2) * Ginf * (eps * eps) + (1#2) * G1 * (xi * xi)))) ->
  0 <= Ginf /\ Ginf <= Ginf + G1.
Proof.
  intros h. destruct (twoMode_stiffness_nonneg _ _ _ _ h) as [hinf h1]. split; lra.
Qed.

(** Plane-stress free energy of an orthotropic lamina at stresses s1, s2 in its material axes. *)
Definition orthotropicEnergy (E1 E2 nu12 s1 s2 : Q) : Q :=
  (s1 * s1) / (2 * E1) - nu12 * s1 * s2 / E1 + (s2 * s2) / (2 * E2).

(** Orthotropic Poisson ratio: a lamina with nonzero moduli that relaxes passively from every plane stress state
    has E1 > 0, E2 > 0 and nu12^2 <= E1/E2. *)
Theorem orthotropic_poisson_sq_le (rho rho' E1 E2 nu12 : Q) :
  ~ E1 == 0 -> ~ E2 == 0 ->
  (forall s1 s2, SecondLaw transition (relaxation rho rho' (orthotropicEnergy E1 E2 nu12 s1 s2))) ->
  0 < E1 /\ 0 < E2 /\ nu12 * nu12 <= E1 / E2.
Proof.
  intros h1 h2 h.
  assert (p1 : 0 < E1).
  { apply (relaxation_modulus_pos rho rho' E1 1); [discriminate | exact h1 |].
    pose proof (h 1 0) as h10. simpl in h10 |- *. unfold core_admissible in h10 |- *. simpl in h10 |- *.
    destruct h10 as [m1 [m2 d]]. repeat split; [exact m1 | exact m2 |].
    unfold orthotropicEnergy in d.
    setoid_replace (1 * 1 / (2 * E1)) with (1 * 1 / (2 * E1) - nu12 * 1 * 0 / E1 + 0 * 0 / (2 * E2))
      by (field; split; assumption).
    exact d. }
  assert (p2 : 0 < E2).
  { apply (relaxation_modulus_pos rho rho' E2 1); [discriminate | exact h2 |].
    pose proof (h 0 1) as h01. simpl in h01 |- *. unfold core_admissible in h01 |- *. simpl in h01 |- *.
    destruct h01 as [m1 [m2 d]]. repeat split; [exact m1 | exact m2 |].
    unfold orthotropicEnergy in d.
    setoid_replace (1 * 1 / (2 * E2)) with (0 * 0 / (2 * E1) - nu12 * 0 * 1 / E1 + 1 * 1 / (2 * E2))
      by (field; split; assumption).
    exact d. }
  split; [exact p1 | split; [exact p2 |]].
  pose proof (relaxation_nonneg _ _ _ (h nu12 1)) as hn. unfold orthotropicEnergy in hn.
  assert (e : nu12 * nu12 / (2 * E1) - nu12 * nu12 * 1 / E1 + 1 * 1 / (2 * E2)
              == (E1 - nu12 * nu12 * E2) / (2 * E1 * E2)) by (field; split; assumption).
  rewrite e in hn.
  assert (hd : 0 < 2 * E1 * E2) by nra.
  assert (hnum : 0 <= E1 - nu12 * nu12 * E2).
  { destruct (Qlt_le_dec (E1 - nu12 * nu12 * E2) 0) as [c|c]; [| exact c].
    exfalso.
    assert (hq : (E1 - nu12 * nu12 * E2) / (2 * E1 * E2) == - ((nu12 * nu12 * E2 - E1) / (2 * E1 * E2)))
      by (field; split; assumption).
    rewrite hq in hn.
    assert (0 < (nu12 * nu12 * E2 - E1) / (2 * E1 * E2)) by (apply Qlt_shift_div_l; [exact hd | lra]).
    lra. }
  apply Qle_shift_div_l; [exact p2 | lra].
Qed.
