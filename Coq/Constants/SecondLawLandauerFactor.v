(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Constants.SecondLawLandauerFactor — the Landauer factor      *)
(*  ln 2 fixed by the second law (twin of                                   *)
(*  Lean/Constants/SecondLawLandauerFactor.lean).                           *)
(*                                                                          *)
(*  Erasing the uniform bit at a bath of temperature T with work T r (work  *)
(*  per kelvin r, in nats) obeys the erase case of SecondLaw exactly when   *)
(*  ln 2 <= r; ln 2 is the least admitted work per kelvin at every          *)
(*  temperature. Zero Axiom, Parameter or Admitted.                         *)
(* ======================================================================== *)

From Stdlib Require Import Reals Lra.
Require Import UMSTFormal.Process.

Open Scope R_scope.

(** An erasure at bath [b] dissipating [bathTemp b * r]. *)
Definition erasureAtFactor (b : HeatBath) (r : R) : ErasureProcess := mkErasure b (bathTemp b * r).

Theorem secondLaw_uniformBit_iff (b : HeatBath) (r : R) :
  SecondLaw (erase (erasureAtFactor b r)) (erasure uniform2) <-> ln 2 <= r.
Proof.
  simpl. unfold eraseSecondLaw, erasureAtFactor. simpl.
  rewrite shannon2_uniform2, shannon2_dirac0.
  pose proof (bathTemp_pos b) as hT.
  replace (bathTemp b * r / bathTemp b) with r by (field; lra).
  split; intros h; lra.
Qed.

(** The Landauer factor: ln 2 is admitted, and every admitted work per kelvin is at least ln 2. *)
Theorem landauerFactor_isLeast (b : HeatBath) :
  SecondLaw (erase (erasureAtFactor b (ln 2))) (erasure uniform2) /\
  (forall r, SecondLaw (erase (erasureAtFactor b r)) (erasure uniform2) -> ln 2 <= r).
Proof.
  split.
  - apply secondLaw_uniformBit_iff. lra.
  - intros r h. exact (proj1 (secondLaw_uniformBit_iff b r) h).
Qed.
