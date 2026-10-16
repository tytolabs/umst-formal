(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: Culture/CarryingCapacity.v                               *)
(*                                                                        *)
(*  Twin of Lean/Culture/CarryingCapacity.lean over exact rationals, with *)
(*  ln 2 a parameter l: an age cap tau bounds the live ticks of a window  *)
(*  by tau (D_T + N_T); erasing D bits at a cost of at least D l, with at *)
(*  most i D l recovered and the net paid by T W, gives                   *)
(*  D l (1 - i) <= T W; so the mean live count is at most                 *)
(*  tau (W / (l (1 - i)) + N_T / T), and a lower enclosure l_lo <= l of   *)
(*  ln 2 gives the same bound with l_lo.                                  *)
(* ===================================================================== *)

From Stdlib Require Import QArith Lqa List ZArith Lia.
Import ListNotations.

Open Scope Q_scope.

Definition qsum (l : list Q) : Q := fold_right Qplus 0 l.

Definition qlen (l : list Q) : Q := inject_Z (Z.of_nat (length l)).

Lemma qlen_cons (d : Q) (ds : list Q) : qlen (d :: ds) == 1 + qlen ds.
Proof. unfold qlen. simpl length. rewrite Nat2Z.inj_succ, <- Z.add_1_l, inject_Z_plus. reflexivity. Qed.

Lemma qlen_app (xs ys : list Q) : qlen (xs ++ ys) == qlen xs + qlen ys.
Proof. unfold qlen. rewrite length_app, Nat2Z.inj_add, inject_Z_plus. reflexivity. Qed.

Lemma qlen_nonneg (xs : list Q) : 0 <= qlen xs.
Proof. unfold qlen. change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. Qed.

(** Age cap: lives of at most tau ticks give at most tau live ticks each. *)
Theorem liveTicks_le_length (tau : Q) (ds : list Q) : Forall (fun d => d <= tau) ds -> qsum ds <= tau * qlen ds.
Proof.
  induction ds as [| d ds IH]; intro h.
  { unfold qsum, qlen. simpl fold_right. simpl length. change (inject_Z (Z.of_nat 0)) with 0. rewrite Qmult_0_r. apply Qle_refl. }
  inversion h as [| ? ? hd hds]; subst. rewrite qlen_cons. pose proof (IH hds) as ih. unfold qsum in *. simpl fold_right. lra.
Qed.

(** Age cap over a window: Sigma_t N_t <= tau (D_T + N_T). *)
Theorem liveTicks_le (tau : Q) (dead alive : list Q) :
  Forall (fun d => d <= tau) (dead ++ alive) -> qsum (dead ++ alive) <= tau * (qlen dead + qlen alive).
Proof. intro h. rewrite <- qlen_app. apply liveTicks_le_length. exact h. Qed.

(** Death cost: D l (1 - i) <= T W. *)
Theorem deathCost_le (D l i T W Werase Wrec : Q) :
  D * l <= Werase -> Wrec <= i * (D * l) -> Werase - Wrec <= T * W -> D * l * (1 - i) <= T * W.
Proof. intros h1 h2 h3. lra. Qed.

(** The carrying capacity, with denominators cleared: tau T W + tau l (1 - i) N_T bounds l (1 - i) Sigma_t N_t. *)
Theorem meanLive_le (tau T W l i : Q) (dead alive : list Q) :
  0 <= tau -> 0 < T -> 0 < l -> i < 1 -> Forall (fun d => d <= tau) (dead ++ alive) ->
  qlen dead * l * (1 - i) <= T * W ->
  l * (1 - i) * qsum (dead ++ alive) <= tau * (T * W + l * (1 - i) * qlen alive).
Proof.
  intros ht hT hl hi hage hcost.
  pose proof (liveTicks_le tau dead alive hage) as hlive.
  assert (hk : 0 < l * (1 - i)) by (apply Qmult_lt_0_compat; lra).
  pose proof (Qmult_le_compat_r _ _ _ hlive (Qlt_le_weak _ _ hk)) as h1.
  assert (h2 : tau * (qlen dead + qlen alive) * (l * (1 - i)) == tau * (qlen dead * l * (1 - i)) + tau * (l * (1 - i) * qlen alive)) by ring.
  pose proof (Qmult_le_compat_r _ _ _ hcost ht) as h3.
  assert (h4 : tau * (T * W + l * (1 - i) * qlen alive) == tau * (T * W) + tau * (l * (1 - i) * qlen alive)) by ring.
  rewrite h4. rewrite h2 in h1.
  setoid_replace (l * (1 - i) * qsum (dead ++ alive)) with (qsum (dead ++ alive) * (l * (1 - i))) by ring. lra.
Qed.

(** With a lower enclosure l_lo <= l of ln 2 the bound holds with l_lo. *)
Theorem meanLive_le_of_enclosure (tau T W l llo i : Q) (dead alive : list Q) :
  0 <= tau -> 0 < T -> 0 < llo -> llo <= l -> i < 1 -> Forall (fun d => d <= tau) (dead ++ alive) ->
  qlen dead * l * (1 - i) <= T * W ->
  llo * (1 - i) * qsum (dead ++ alive) <= tau * (T * W + llo * (1 - i) * qlen alive).
Proof.
  intros ht hT hlo hl hi hage hcost.
  pose proof (liveTicks_le tau dead alive hage) as hlive.
  assert (hk : 0 < llo * (1 - i)) by (apply Qmult_lt_0_compat; lra).
  pose proof (Qmult_le_compat_r _ _ _ hlive (Qlt_le_weak _ _ hk)) as h1.
  assert (hc' : qlen dead * llo * (1 - i) <= T * W).
  { assert (hq : 0 <= qlen dead * (1 - i)) by (apply Qmult_le_0_compat; [apply qlen_nonneg | lra]).
    pose proof (Qmult_le_compat_r _ _ _ hl hq) as hm.
    setoid_replace (qlen dead * llo * (1 - i)) with (qlen dead * (1 - i) * llo) by ring.
    setoid_replace (qlen dead * l * (1 - i)) with (qlen dead * (1 - i) * l) in hcost by ring. lra. }
  pose proof (Qmult_le_compat_r _ _ _ hc' ht) as h3.
  assert (h2 : tau * (qlen dead + qlen alive) * (llo * (1 - i)) == tau * (qlen dead * llo * (1 - i)) + tau * (llo * (1 - i) * qlen alive)) by ring.
  assert (h4 : tau * (T * W + llo * (1 - i) * qlen alive) == tau * (T * W) + tau * (llo * (1 - i) * qlen alive)) by ring.
  rewrite h4. rewrite h2 in h1.
  setoid_replace (llo * (1 - i) * qsum (dead ++ alive)) with (qsum (dead ++ alive) * (llo * (1 - i))) by ring. lra.
Qed.
