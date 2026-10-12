(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: FreeFall.v                                               *)
(*                                                                        *)
(*  Twin of Lean/FreeFall.lean over exact rationals: a body dropped from  *)
(*  rest, an instance of the passive transition case of SecondLaw.        *)
(*  Gravity is the gradient of a scalar potential Phi on the              *)
(*  configuration manifold and free fall is the flow along -grad Phi;     *)
(*  psi(z) = m Phi(z) = m g z is linear, hence convex, in z, so the       *)
(*  passive route of ConvexPhiDissipation applies. The SDF, MSDF, TESDF   *)
(*  and FRep framing is left out: it does not reduce any proof below.     *)
(*  Typed absence: the k_B T ln 2 cost per extracted frame bit is the     *)
(*  measureFeedback case; follow-up cell FORMAL-FREEFALL-MEASURE-FEEDBACK.*)
(*  Zero Axiom, Parameter or Admitted.                                    *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra QArith Qreals Lqa.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process UMSTFormal.OneInequalitySecondLaw
  UMSTFormal.Constants.SecondLawRestitution.

Open Scope Q_scope.

(** The work the gravitational potential supplies to mass [m] dropped through [h] in the field [g]. *)
Definition fallWork (m g h : Q) : Q := m * g * h.

(** The dissipation of a fall: the work supplied less the kinetic energy at the ground. *)
Definition fallDissipation (m g h v : Q) : Q := fallWork m g h - (1#2) * m * (v * v).

(** The fall: free energy m g h at rest on top, 1/2 m v^2 at the ground. *)
Definition fall (rho rho' m g h v : Q) : Prior :=
  thermodynamic (mkState rho (fallWork m g h) 0 0) (mkState rho' ((1#2) * m * (v * v)) 0 0).

(** Free fall as a passive transition: D >= 0, 1/2 m v^2 = W_in - D <= W_in, v^2 <= 2 g h and g >= v^2 / (2 h). *)
Theorem freeFall_gravity_lower_bound (rho rho' m g h v : Q) :
  0 < m -> 0 < h -> SecondLaw transition (fall rho rho' m g h v) ->
  0 <= fallDissipation m g h v /\ (1#2) * m * (v * v) == fallWork m g h - fallDissipation m g h v /\
  (1#2) * m * (v * v) <= fallWork m g h /\ v * v <= 2 * g * h /\ v * v / (2 * h) <= g.
Proof.
  intros hm hh hS. simpl in hS. unfold core_admissible in hS. simpl in hS. destruct hS as [_ [_ hd]].
  unfold fallDissipation, fallWork in *.
  assert (hv : v * v <= 2 * g * h) by nra.
  repeat split; try lra; try exact hv.
  apply Qle_shift_div_r; [lra | nra].
Qed.

(** Fall, impact and rebound steps of the chain, at one bath. *)
Definition fallStep (b : HeatBath) (rho rho' m g hd v : Q) : Step :=
  transitionStepAt b (mkState rho (fallWork m g hd) 0 0) (mkState rho' ((1#2) * m * (v * v)) 0 0).
Definition impactStep (b : HeatBath) (rho rho' m v e : Q) : Step :=
  transitionStepAt b (mkState rho ((1#2) * m * (v * v)) 0 0) (mkState rho' ((1#2) * m * ((e * v) * (e * v))) 0 0).
Definition reboundStep (b : HeatBath) (rho rho' m g hr v e : Q) : Step :=
  transitionStepAt b (mkState rho ((1#2) * m * ((e * v) * (e * v))) 0 0) (mkState rho' (fallWork m g hr) 0 0).

(** Fall, impact, rebound as one mixed chain of the one inequality (I = 0). *)
Theorem freeFallRebound_chain_oneInequality (b : HeatBath) (r0 r1 r2 r3 m g hd hr v e : Q) :
  SecondLaw transition (thermodynamic (mkState r0 (fallWork m g hd) 0 0) (mkState r1 ((1#2) * m * (v * v)) 0 0)) ->
  SecondLaw transition (impact r1 r2 m v e) ->
  SecondLaw transition (thermodynamic (mkState r2 ((1#2) * m * ((e * v) * (e * v))) 0 0) (mkState r3 (fallWork m g hr) 0 0)) ->
  oneInequality (chain (chain (fallStep b r0 r1 m g hd v) (impactStep b r1 r2 m v e)) (reboundStep b r2 r3 m g hr v e)).
Proof.
  intros hF hI hR.
  apply oneInequality_chain; [reflexivity | | ].
  - apply oneInequality_chain; [reflexivity | | ].
    + exact (proj1 (proj1 (SecondLaw_transition_oneInequality_iff b _ _) hF)).
    + exact (proj1 (proj1 (SecondLaw_transition_oneInequality_iff b _ _) hI)).
  - exact (proj1 (proj1 (SecondLaw_transition_oneInequality_iff b _ _) hR)).
Qed.

(** The rebound never rises above the drop. *)
Theorem freeFallRebound_height_le (b : HeatBath) (r0 r1 r2 r3 m g hd hr v e : Q) :
  0 < m -> 0 < g ->
  SecondLaw transition (thermodynamic (mkState r0 (fallWork m g hd) 0 0) (mkState r1 ((1#2) * m * (v * v)) 0 0)) ->
  SecondLaw transition (impact r1 r2 m v e) ->
  SecondLaw transition (thermodynamic (mkState r2 ((1#2) * m * ((e * v) * (e * v))) 0 0) (mkState r3 (fallWork m g hr) 0 0)) ->
  hr <= hd.
Proof.
  intros hm hg hF hI hR.
  pose proof (freeFallRebound_chain_oneInequality b r0 r1 r2 r3 m g hd hr v e hF hI hR) as h.
  unfold oneInequality, chain, fallStep, impactStep, reboundStep, transitionStepAt in h. simpl in h.
  unfold fallWork in h.
  assert (Hz : (kB * bathTemp b * (0 + 0 + 0) = 0)%R) by ring. rewrite Hz in h.
  assert (h2 : (Q2R (m * g * hr)%Q <= Q2R (m * g * hd)%Q)%R) by Lra.lra.
  apply Rle_Qle in h2.
  assert (hmg : 0 < m * g) by nra. nra.
Qed.

(** Restitution from the heights (g cancels): with no dissipation in flight, e^2 = h_r / h_d, e <= 1, h_r / h_d <= 1. *)
Theorem freeFallRebound_restitution (r1 r2 m g hd hr v e : Q) :
  0 < m -> 0 < g -> 0 < hd -> 0 <= e -> 0 < m * (v * v) ->
  (1#2) * m * (v * v) == fallWork m g hd ->
  (1#2) * m * ((e * v) * (e * v)) == fallWork m g hr ->
  SecondLaw transition (impact r1 r2 m v e) ->
  e * e == hr / hd /\ e <= 1 /\ hr / hd <= 1.
Proof.
  intros hm hg hhd he hv hFall hRise hI.
  unfold fallWork in *.
  assert (he1 : e <= 1) by exact (restitution_le_one r1 r2 m v e he hv hI).
  assert (h3 : (e * e) * ((1#2) * m * (v * v)) == (e * e) * (m * g * hd)) by (apply Qmult_comp; [apply Qeq_refl | exact hFall]).
  assert (hq : m * g * hr == m * g * (e * e * hd)) by nra.
  assert (hh : hr == e * e * hd).
  { apply (proj1 (Qmult_inj_l _ _ (m * g) ltac:(intro H0; nra))). exact hq. }
  assert (hratio : e * e == hr / hd).
  { apply Qle_antisym; [apply Qle_shift_div_l | apply Qle_shift_div_r]; try exact hhd; nra. }
  repeat split; try exact he1; try exact hratio.
  rewrite <- hratio. nra.
Qed.
