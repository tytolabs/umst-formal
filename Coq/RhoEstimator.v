(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.RhoEstimator — Gaussian bivariate mutual information in bits *)
(*  from the Pearson correlation, twin of Lean/RhoEstimator.lean:           *)
(*  MI(rho) = - 1/2 log2 (1 - rho^2) for rho^2 < 1, a function of rho^2.    *)
(*  Zero Axiom, Parameter or Admitted.                                      *)
(* ======================================================================== *)

From Stdlib Require Import Reals.

Open Scope R_scope.

(** Correlations for which the closed form holds. *)
Definition ValidRho (rho : R) : Prop := rho ^ 2 < 1.

(** Base-2 logarithm. *)
Definition logb2 (x : R) : R := ln x / ln 2.

(** Mutual information (bits) as a function of t = rho^2. *)
Definition rhoMiOfSq (t : R) : R := - (1 / 2) * logb2 (1 - t).

(** Mutual information (bits) of a bivariate Gaussian with correlation [rho]. *)
Definition rhoMi (rho : R) : R := rhoMiOfSq (rho ^ 2).

Theorem rho_based_mi_formula (rho : R) :
  ValidRho rho -> rhoMi rho = - (1 / 2) * logb2 (1 - rho ^ 2).
Proof. intros _. reflexivity. Qed.
