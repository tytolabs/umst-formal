(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: Concrete/PowersCapillary.v                               *)
(*                                                                        *)
(*  Twin of Lean/Concrete/PowersCapillary.lean: the capillary porosity    *)
(*  of Powers' volume model in closed form,                               *)
(*  (w - (w/c)_s a) / (w + rho_w/rho_c), and the rounded coefficients     *)
(*  0.36, 0.32 and 0.317 that runtime closures carry, each the rounding   *)
(*  of its derived value (round x = floor (x + 1/2), as in Mathlib).      *)
(* ===================================================================== *)

From Stdlib Require Import QArith Qfield Qabs Qround Lqa.
Require Import UMSTFormal.Constants.SI.
Require Import UMSTFormal.Concrete.PowersVolume.

Open Scope Q_scope.

(** Capillary pore fraction of the paste: capillary water plus chemical-shrinkage voids. *)
Definition capillaryPorosity (w a : Q) : Q :=
  capillaryWater (waterFraction w) a + shrinkage (waterFraction w) a.

(** Capillary porosity in closed form: (w - (w/c)_s a) / (w + 1 / (rho_c/rho_w)). *)
Theorem capillaryPorosity_eq (w a : Q) : 0 <= w ->
  capillaryPorosity w a == (w - criticalWcSpace * a) / (w + 1 / densityRatio).
Proof.
  intro hw. unfold capillaryPorosity, capillaryWater, shrinkage, waterFraction.
  setoid_replace capillaryConsumption with (1323 # 1000) by (vm_compute; reflexivity).
  setoid_replace shrinkageVolume with (2016 # 10000) by (vm_compute; reflexivity).
  setoid_replace criticalWcSpace with (89 # 250) by (vm_compute; reflexivity).
  setoid_replace densityRatio with (63 # 20) by (vm_compute; reflexivity).
  field. repeat split; intro e; lra.
Qed.

(** x rounded to two and to three decimals. *)
Definition round2 (x : Q) : Q := inject_Z (Qfloor (100 * x + (1 # 2))) / 100.
Definition round3 (x : Q) : Q := inject_Z (Qfloor (1000 * x + (1 # 2))) / 1000.

Definition powersCapillaryWaterCoeff : Q := round2 criticalWcSpace.
Definition powersPasteOffsetCoeff : Q := round2 (1 / densityRatio).
Definition powersCementVolumeCoeff : Q := round3 (1 / densityRatio).

Theorem powersCapillaryWaterCoeff_value : powersCapillaryWaterCoeff == 36 # 100.
Proof. vm_compute. reflexivity. Qed.

Theorem powersPasteOffsetCoeff_value : powersPasteOffsetCoeff == 32 # 100.
Proof. vm_compute. reflexivity. Qed.

Theorem powersCementVolumeCoeff_value : powersCementVolumeCoeff == 317 # 1000.
Proof. vm_compute. reflexivity. Qed.

(** The rounded capillary-water coefficient lies within 1/200 of (w/c)_s. *)
Theorem powersCapillaryWaterCoeff_err : Qabs (powersCapillaryWaterCoeff - criticalWcSpace) <= 1 # 200.
Proof. apply Qle_bool_imp_le. vm_compute. reflexivity. Qed.

(** The rounded paste-offset coefficient lies within 1/200 of rho_w/rho_c. *)
Theorem powersPasteOffsetCoeff_err : Qabs (powersPasteOffsetCoeff - 1 / densityRatio) <= 1 # 200.
Proof. apply Qle_bool_imp_le. vm_compute. reflexivity. Qed.
