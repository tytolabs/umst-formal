(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: ClassicalDPI.v                                           *)
(*                                                                        *)
(*  Twin of Lean/ClassicalDPI.lean. The analytic step is proved here      *)
(*  over the reals: the two-term log-sum inequality                       *)
(*    (a + b) ln((a + b)/(s + t)) <= a ln(a/s) + b ln(b/t)                *)
(*  from ln x <= x - 1 (log_sum_two). The combinatorial step is proved    *)
(*  for any column functional G that is zero on the zero column and       *)
(*  subadditive on non-negative columns (the property log_sum_two gives   *)
(*  G(v) = sum v_i ln v_i - (sum v_i) ln(sum v_i) in Lean): merging the   *)
(*  columns of each group of a summary does not raise the sum of G        *)
(*  (summary_colsum_le), which is I(X; f(Y)) - H(X) <= I(X; Y) - H(X).    *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.

Open Scope R_scope.

(** ln x <= x - 1 for x > 0. *)
Lemma ln_le_sub_one (x : R) : 0 < x -> ln x <= x - 1.
Proof. intro hx. pose proof (exp_ineq1_le (ln x)) as h. rewrite exp_ln in h by exact hx. lra. Qed.

(** One term of the log-sum inequality: x ln(x/y) >= x ln(A/S) - y A/S + x for x >= 0 and y, A, S > 0. *)
Lemma log_sum_term (x y A S : R) :
  0 <= x -> 0 < y -> 0 < A -> 0 < S -> x * ln (A / S) - y * A / S + x <= x * ln (x / y).
Proof.
  intros hx hy hA hS.
  destruct (Req_dec x 0) as [h0 | hne].
  - subst x. assert (0 < y * A / S) by (unfold Rdiv; apply Rmult_lt_0_compat; [nra | apply Rinv_0_lt_compat; lra]). lra.
  - assert (hxp : 0 < x) by lra.
    set (u := y * A / (x * S)).
    assert (hu : 0 < u).
    { unfold u, Rdiv. apply Rmult_lt_0_compat; [nra | apply Rinv_0_lt_compat; nra]. }
    assert (hsplit : ln (A / S) = ln (x / y) + ln u).
    { rewrite <- ln_mult; [| unfold Rdiv; apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra] | exact hu].
      f_equal. unfold u. field. repeat split; lra. }
    pose proof (ln_le_sub_one u hu) as hl.
    assert (hxu : x * u = y * A / S) by (unfold u; field; split; lra).
    rewrite hsplit. nra.
Qed.

(** The two-term log-sum inequality. *)
Theorem log_sum_two (a b s t : R) :
  0 <= a -> 0 <= b -> 0 < s -> 0 < t -> (a + b) * ln ((a + b) / (s + t)) <= a * ln (a / s) + b * ln (b / t).
Proof.
  intros ha hb hs ht.
  destruct (Req_dec (a + b) 0) as [h0 | hne].
  - assert (a = 0) by lra. assert (b = 0) by lra. subst. rewrite h0. lra.
  - assert (hA : 0 < a + b) by lra. assert (hS : 0 < s + t) by lra.
    pose proof (log_sum_term a s (a + b) (s + t) ha hs hA hS) as h1.
    pose proof (log_sum_term b t (a + b) (s + t) hb ht hA hS) as h2.
    assert (hc : s * (a + b) / (s + t) + t * (a + b) / (s + t) = a + b) by (field; lra).
    nra.
Qed.

(** The combinatorial step, for any column functional subadditive on non-negative columns. *)
Section Merge.

Variable C : Type.
Variable add : C -> C -> C.
Variable zero : C.
Variable N : C -> Prop.
Hypothesis N_zero : N zero.
Hypothesis N_add : forall a b, N a -> N b -> N (add a b).
Variable G : C -> R.
Hypothesis G_zero : G zero = 0.
Hypothesis G_sub : forall a b, N a -> N b -> G (add a b) <= G a + G b.

Definition mergeAll (cs : list C) : C := fold_right add zero cs.

Definition sumG (cs : list C) : R := fold_right (fun c acc => G c + acc) 0 cs.

Lemma N_mergeAll (cs : list C) : Forall N cs -> N (mergeAll cs).
Proof. induction cs as [| c cs IH]; intro h; [exact N_zero |]. inversion h; subst. apply N_add; auto. Qed.

(** Merging a family of non-negative columns does not raise the sum of G. *)
Theorem merge_le (cs : list C) : Forall N cs -> G (mergeAll cs) <= sumG cs.
Proof.
  induction cs as [| c cs IH]; intro h; [simpl; rewrite G_zero; lra |].
  inversion h as [| ? ? hc hcs]; subst. simpl.
  pose proof (G_sub c (mergeAll cs) hc (N_mergeAll cs hcs)). pose proof (IH hcs). lra.
Qed.

Lemma sumG_app (xs ys : list C) : sumG (xs ++ ys) = sumG xs + sumG ys.
Proof. induction xs as [| x xs IH]; simpl; [ring | rewrite IH; ring]. Qed.

(** The summary merges the columns of each group; the receipts are all the columns. The summary's sum of G is at
    most the receipts', so I(X; f(Y)) <= I(X; Y) once H(X), which merging leaves unchanged, is added to both. *)
Theorem summary_colsum_le (groups : list (list C)) :
  Forall (Forall N) groups ->
  fold_right (fun g acc => G (mergeAll g) + acc) 0 groups <= sumG (concat groups).
Proof.
  induction groups as [| g gs IH]; intro h; [simpl; lra |].
  inversion h as [| ? ? hg hgs]; subst. simpl. rewrite sumG_app.
  pose proof (merge_le g hg). pose proof (IH hgs). lra.
Qed.

End Merge.
