(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: AdaptiveSeamLensLaws.v                                   *)
(*                                                                        *)
(*  Twin of Lean/AdaptiveSeamLensLaws.lean. L-A: the transfer lens        *)
(*  get = R, put s v = (s - P (R s)) + P v satisfies GetPut, and PutGet   *)
(*  when R P = id, with s - P (R s) in ker R. L-D: two subsystems each    *)
(*  satisfying dF <= W + c I (c = k_B T), joined by a power-preserving    *)
(*  seam (W1 + W2 = 0), satisfy dF1 + dF2 <= c (I1 + I2); without         *)
(*  information the composite free energy does not rise. L-I: for         *)
(*  L antisymmetric, M symmetric positive semidefinite, L gS = 0 and      *)
(*  M gE = 0 under a symmetric pairing, gE . (L gE + M gS) = 0 and        *)
(*  gS . (L gE + M gS) >= 0. The group and pairing laws are section       *)
(*  hypotheses (arguments of each theorem), not axioms.                   *)
(* ===================================================================== *)

From Stdlib Require Import QArith Lqa.

Open Scope Q_scope.

Section Lens.

Variables S V : Type.
Variables (sadd ssub : S -> S -> S) (vadd vsub : V -> V -> V) (vzero : V).
Variables (R : S -> V) (P : V -> S).
Hypothesis sub_add_cancel : forall x y, sadd (ssub x y) y = x.
Hypothesis R_add : forall a b, R (sadd a b) = vadd (R a) (R b).
Hypothesis R_sub : forall a b, R (ssub a b) = vsub (R a) (R b).
Hypothesis vsub_self : forall u, vsub u u = vzero.
Hypothesis vzero_add : forall v, vadd vzero v = v.

Definition lensGet (s : S) : V := R s.
Definition lensPut (s : S) (v : V) : S := sadd (ssub s (P (R s))) (P v).

(** L-A GetPut. *)
Theorem lens_getPut (s : S) : lensPut s (lensGet s) = s.
Proof. unfold lensPut, lensGet. apply sub_add_cancel. Qed.

(** L-A PutGet, when R P = id. *)
Theorem lens_putGet (RP : forall v, R (P v) = v) (s : S) (v : V) : lensGet (lensPut s v) = v.
Proof. unfold lensGet, lensPut. rewrite R_add, R_sub, !RP, vsub_self. apply vzero_add. Qed.

(** With R P = id, s - P (R s) lies in ker R. *)
Theorem proj_mem_ker (RP : forall v, R (P v) = v) (s : S) : R (ssub s (P (R s))) = vzero.
Proof. rewrite R_sub, RP. apply vsub_self. Qed.

End Lens.

(** ** L-D: a power-preserving seam creates no energy. *)

Record Step := mkStep { dF : Q; wIn : Q; infoI : Q }.

Definition oneIneq (c : Q) (s : Step) : Prop := dF s <= wIn s + c * infoI s.

Theorem seam_oneInequality (c : Q) (s1 s2 : Step) :
  oneIneq c s1 -> oneIneq c s2 -> wIn s1 + wIn s2 == 0 -> dF s1 + dF s2 <= c * (infoI s1 + infoI s2).
Proof. unfold oneIneq. intros h1 h2 hw. nra. Qed.

Theorem seam_creates_no_energy (c : Q) (s1 s2 : Step) :
  oneIneq c s1 -> oneIneq c s2 -> wIn s1 + wIn s2 == 0 -> infoI s1 + infoI s2 == 0 -> dF s1 + dF s2 <= 0.
Proof.
  intros h1 h2 hw hi. pose proof (seam_oneInequality c s1 s2 h1 h2 hw) as h. rewrite hi in h.
  rewrite Qmult_0_r in h. exact h.
Qed.

Theorem seam_refused (c : Q) (s1 s2 : Step) :
  wIn s1 + wIn s2 == 0 -> infoI s1 + infoI s2 == 0 -> 0 < dF s1 + dF s2 -> ~ (oneIneq c s1 /\ oneIneq c s2).
Proof.
  intros hw hi hr [h1 h2]. pose proof (seam_creates_no_energy c s1 s2 h1 h2 hw hi). lra.
Qed.

(** ** L-I: GENERIC degeneracy. *)

Section Generic.

Variable W : Type.
Variables (vadd : W -> W -> W) (vzero : W) (pair : W -> W -> Q) (L M : W -> W).
Hypothesis pair_add_r : forall x y z, pair x (vadd y z) == pair x y + pair x z.
Hypothesis pair_comm : forall x y, pair x y == pair y x.
Hypothesis pair_zero_l : forall y, pair vzero y == 0.
Hypothesis L_antisym : forall x y, pair x (L y) == - pair (L x) y.
Hypothesis M_sym : forall x y, pair x (M y) == pair (M x) y.
Hypothesis M_psd : forall x, 0 <= pair x (M x).

Lemma quad_antisymm_zero (g : W) : pair g (L g) == 0.
Proof. pose proof (L_antisym g g) as h. rewrite (pair_comm (L g) g) in h. lra. Qed.

(** L-I, energy conserved. *)
Theorem generic_energy_rate (gE gS : W) : M gE = vzero -> pair gE (vadd (L gE) (M gS)) == 0.
Proof.
  intro hME. rewrite pair_add_r, quad_antisymm_zero, M_sym, hME, pair_zero_l. ring.
Qed.

(** L-I, entropy produced. *)
Theorem generic_entropy_rate_nonneg (gE gS : W) : L gS = vzero -> 0 <= pair gS (vadd (L gE) (M gS)).
Proof.
  intro hLS. rewrite pair_add_r, L_antisym, hLS, pair_zero_l. pose proof (M_psd gS). lra.
Qed.

End Generic.
