(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: UncertaintyRelation.v                                    *)
(*                                                                        *)
(*  Twin of Lean/UncertaintyRelation.lean. The thermodynamic uncertainty  *)
(*  relation (Barato and Seifert, PRL 114, 158101 (2015)) for the biased  *)
(*  random walk (uniform ring) with rates kp, km > 0: mean current        *)
(*  (kp - km) t and variance (kp + km) t (Skellam, J. R. Stat. Soc. 109,  *)
(*  296 (1946)), entropy production (kp - km)(ln kp - ln km) t            *)
(*  (Schnakenberg, Rev. Mod. Phys. 48, 571 (1976)):                       *)
(*    2 <J>^2 <= Var(J) * sigma.                                          *)
(*  Analytic core: ln x >= 2 (x - 1)/(x + 1) for x >= 1, by the mean      *)
(*  value theorem on f x = ln x - 2 (x - 1)/(x + 1), whose derivative     *)
(*  (x - 1)^2 / (x (x + 1)^2) is non-negative. The general TUR for any    *)
(*  current of any finite Markov jump process is a typed absence          *)
(*  (follow-up FORMAL-TUR-GENERAL).                                       *)
(*  Zero Axiom, Parameter or Admitted.                                    *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra.

Open Scope R_scope.

Definition turAux (x : R) : R := ln x - 2 * (x - 1) / (x + 1).

Definition turAuxDeriv (x : R) : R := / x - 4 / ((x + 1) * (x + 1)).

Lemma turAux_derivable : forall c, 0 < c -> derivable_pt_lim turAux c (turAuxDeriv c).
Proof.
  intros c hc.
  assert (hnum : derivable_pt_lim (mult_real_fct 2 (id - fct_cte 1)%F) c (2 * (1 - 0))).
  { apply derivable_pt_lim_scal. apply derivable_pt_lim_minus;
      [apply derivable_pt_lim_id | apply derivable_pt_lim_const]. }
  assert (hden : derivable_pt_lim (id + fct_cte 1)%F c (1 + 0)).
  { apply derivable_pt_lim_plus; [apply derivable_pt_lim_id | apply derivable_pt_lim_const]. }
  assert (hq := derivable_pt_lim_div _ _ c _ _ hnum hden).
  assert (hq' : derivable_pt_lim (mult_real_fct 2 (id - fct_cte 1)%F / (id + fct_cte 1)%F)%F c
     ((2 * (1 - 0) * (id + fct_cte 1)%F c - (1 + 0) * mult_real_fct 2 (id - fct_cte 1)%F c) /
        Rsqr ((id + fct_cte 1)%F c))).
  { apply hq. unfold plus_fct, id, fct_cte. lra. }
  assert (hl := derivable_pt_lim_minus _ _ c _ _ (derivable_pt_lim_ln c hc) hq').
  replace (turAuxDeriv c) with
    (/ c - (2 * (1 - 0) * (id + fct_cte 1)%F c - (1 + 0) * mult_real_fct 2 (id - fct_cte 1)%F c) /
        Rsqr ((id + fct_cte 1)%F c)).
  - exact hl.
  - unfold turAuxDeriv, plus_fct, minus_fct, mult_real_fct, id, fct_cte, Rsqr. field. lra.
Qed.

Lemma turAuxDeriv_nonneg : forall c, 0 < c -> 0 <= turAuxDeriv c.
Proof.
  intros c hc. unfold turAuxDeriv.
  replace (/ c - 4 / ((c + 1) * (c + 1))) with ((c - 1) * (c - 1) / (c * ((c + 1) * (c + 1)))) by (field; lra).
  apply Rmult_le_pos.
  - apply Rle_0_sqr.
  - left. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; [lra |]. apply Rmult_lt_0_compat; lra.
Qed.

(** ln x >= 2 (x - 1)/(x + 1) for x >= 1. *)
Theorem two_mul_div_le_log : forall x, 1 <= x -> 2 * (x - 1) / (x + 1) <= ln x.
Proof.
  intros x hx.
  destruct (Req_dec x 1) as [-> | hne].
  - rewrite ln_1. unfold Rdiv. replace (1 - 1) with 0 by ring. lra.
  - assert (hlt : 1 < x) by lra.
    destruct (MVT_cor2 turAux turAuxDeriv 1 x hlt) as [c [hc hcI]].
    + intros c hc. apply turAux_derivable. lra.
    + assert (hd : 0 <= turAuxDeriv c) by (apply turAuxDeriv_nonneg; lra).
      assert (h1 : turAux 1 = 0).
      { unfold turAux. rewrite ln_1. unfold Rdiv. replace (1 - 1) with 0 by ring. ring. }
      assert (0 <= turAux x - turAux 1).
      { rewrite hc. apply Rmult_le_pos; lra. }
      unfold turAux in *. lra.
Qed.

(** Logarithmic-mean bound: 2 (a - b)^2 <= (a + b)(a - b)(ln a - ln b) for a, b > 0. *)
Lemma log_mean_bound_ordered : forall a b, 0 < b -> b <= a ->
  2 * ((a - b) * (a - b)) <= (a + b) * (a - b) * (ln a - ln b).
Proof.
  intros a b hb hab.
  assert (ha : 0 < a) by lra.
  assert (hx : 1 <= a / b) by (apply (Rmult_le_reg_r b); [lra | field_simplify; lra]).
  pose proof (two_mul_div_le_log (a / b) hx) as hlog.
  assert (hdiv : ln (a / b) = ln a - ln b).
  { unfold Rdiv. rewrite ln_mult by (try apply Rinv_0_lt_compat; lra). rewrite ln_Rinv by lra. ring. }
  rewrite hdiv in hlog.
  replace (2 * (a / b - 1) / (a / b + 1)) with (2 * (a - b) / (a + b)) in hlog by (field; lra).
  assert (hs : 0 <= (a + b) * (a - b)) by (apply Rmult_le_pos; lra).
  pose proof (Rmult_le_compat_l _ _ _ hs hlog) as hmul.
  replace ((a + b) * (a - b) * (2 * (a - b) / (a + b))) with (2 * ((a - b) * (a - b))) in hmul by (field; lra).
  lra.
Qed.

Theorem log_mean_bound : forall a b, 0 < a -> 0 < b ->
  2 * ((a - b) * (a - b)) <= (a + b) * (a - b) * (ln a - ln b).
Proof.
  intros a b ha hb.
  destruct (Rle_or_lt b a) as [hab | hab].
  - apply log_mean_bound_ordered; lra.
  - pose proof (log_mean_bound_ordered b a ha (Rlt_le _ _ hab)) as h.
    replace ((a - b) * (a - b)) with ((b - a) * (b - a)) by ring.
    replace ((a + b) * (a - b) * (ln a - ln b)) with ((b + a) * (b - a) * (ln b - ln a)) by ring.
    exact h.
Qed.

(** The biased random walk by its forward and backward rates. *)
Record BiasedWalk : Type := mkBiasedWalk {
  kPlus : R;
  kMinus : R;
  kPlus_pos : 0 < kPlus;
  kMinus_pos : 0 < kMinus
}.

Definition meanCurrent (w : BiasedWalk) (t : R) : R := (kPlus w - kMinus w) * t.
Definition varCurrent (w : BiasedWalk) (t : R) : R := (kPlus w + kMinus w) * t.
Definition entropyProduction (w : BiasedWalk) (t : R) : R :=
  (kPlus w - kMinus w) * (ln (kPlus w) - ln (kMinus w)) * t.

(** Thermodynamic uncertainty relation for the biased walk: 2 <J_t>^2 <= Var(J_t) * sigma_t. *)
Theorem tur_biasedWalk : forall (w : BiasedWalk) (t : R), 0 <= t ->
  2 * (meanCurrent w t * meanCurrent w t) <= varCurrent w t * entropyProduction w t.
Proof.
  intros w t ht. unfold meanCurrent, varCurrent, entropyProduction.
  pose proof (log_mean_bound (kPlus w) (kMinus w) (kPlus_pos w) (kMinus_pos w)) as h.
  assert (ht2 : 0 <= t * t) by apply Rle_0_sqr.
  pose proof (Rmult_le_compat_r _ _ _ ht2 h) as hm.
  replace (2 * ((kPlus w - kMinus w) * t * ((kPlus w - kMinus w) * t)))
    with (2 * ((kPlus w - kMinus w) * (kPlus w - kMinus w)) * (t * t)) by ring.
  replace ((kPlus w + kMinus w) * t * ((kPlus w - kMinus w) * (ln (kPlus w) - ln (kMinus w)) * t))
    with ((kPlus w + kMinus w) * (kPlus w - kMinus w) * (ln (kPlus w) - ln (kMinus w)) * (t * t)) by ring.
  exact hm.
Qed.
