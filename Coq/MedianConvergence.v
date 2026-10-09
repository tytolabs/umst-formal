(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.MedianConvergence — the median warm-up budget, twin of       *)
(*  Lean/MedianConvergence.lean: the Hoeffding-style sample threshold       *)
(*  (2 / (eps^2 rho_min^2)) ln (2 / delta) at the reference triple          *)
(*  (eps, delta, rho_min) = (1, 1/2, 1) lies below max 3 ceil(sqrt 32) = 6, *)
(*  the default cockpit window's warm-up count. Ceilings are stated by      *)
(*  their defining inequalities: ceil x <= n iff x <= n, and ceil(sqrt 32)  *)
(*  = 6 iff 5 < sqrt 32 <= 6. Zero Axiom, Parameter or Admitted.            *)
(* ======================================================================== *)

From Stdlib Require Import Reals Lra.

Open Scope R_scope.

(** Analytic sample threshold (natural log). *)
Definition nWarmupBound (eps delta rho_min : R) : R := (2 / (eps ^ 2 * rho_min ^ 2)) * ln (2 / delta).

Theorem sqrt_window_warmup_is_admissible :
  (5 < sqrt 32 <= 6) /\ nWarmupBound 1 (1 / 2) 1 <= Rmax 3 6.
Proof.
  split; [split |].
  - replace 5 with (sqrt (5 * 5)) by (apply sqrt_square; lra).
    apply sqrt_lt_1_alt. lra.
  - apply Rle_trans with (sqrt (6 * 6)); [apply sqrt_le_1_alt; lra | rewrite sqrt_square; lra].
  - unfold nWarmupBound, Rmax. destruct (Rle_dec 3 6) as [_ | n]; [| lra].
    replace (2 / (1 / 2)) with 4 by field.
    replace (2 / (1 ^ 2 * 1 ^ 2)) with 2 by field.
    assert (h : ln 4 < 3).
    { rewrite <- (ln_exp 3). apply ln_increasing; [lra |].
      pose proof (exp_ineq1 3 ltac:(lra)). lra. }
    lra.
Qed.
