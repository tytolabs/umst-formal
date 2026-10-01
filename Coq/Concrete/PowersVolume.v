(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: Concrete/PowersVolume.v                                  *)
(*                                                                        *)
(*  Powers' volume model with coefficients derived in Constants/SI.v;     *)
(*  twin of Lean/Concrete/PowersVolume.lean: the phases fill the paste    *)
(*  (volume balance), and at complete hydration capillary water remains   *)
(*  exactly when w >= 0.42 and the products fit exactly when w >= 0.356;  *)
(*  per unit volume of cement both thresholds hold without division.      *)
(* ===================================================================== *)

From Stdlib Require Import QArith Qfield Lqa.
Require Import UMSTFormal.Constants.SI.

Open Scope Q_scope.

(** Initial volume fraction of water in a paste of water-cement ratio w (by mass). *)
Definition waterFraction (w : Q) : Q := w * densityRatio / (w * densityRatio + 1).

Definition cement (p a : Q) : Q := (1 - p) * (1 - a).
Definition gelSolids (p a : Q) : Q := gelSolidsVolume * (1 - p) * a.
Definition gelWaterV (p a : Q) : Q := gelWaterVolume * (1 - p) * a.
Definition capillaryWater (p a : Q) : Q := p - capillaryConsumption * (1 - p) * a.
Definition shrinkage (p a : Q) : Q := shrinkageVolume * (1 - p) * a.

(** The coefficients conserve volume. *)
Lemma coefficient_balance : gelSolidsVolume + gelWaterVolume + shrinkageVolume - capillaryConsumption == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma balance_general (gs gw cs cc p a : Q) :
  gs + gw + cs - cc == 1 ->
  (1 - p) * (1 - a) + gs * (1 - p) * a + gw * (1 - p) * a + (p - cc * (1 - p) * a) + cs * (1 - p) * a == 1.
Proof.
  intro H. setoid_replace gs with (1 - gw - cs + cc) by (rewrite <- H; ring). ring.
Qed.

(** Volume balance: at every initial water fraction and degree of hydration the phases fill the paste. *)
Theorem volume_balance (p a : Q) :
  cement p a + gelSolids p a + gelWaterV p a + capillaryWater p a + shrinkage p a == 1.
Proof. exact (balance_general _ _ _ _ p a coefficient_balance). Qed.

(** Capillary water, and capillary water with shrinkage voids, at complete hydration per unit volume of cement. *)
Definition capillaryPerCement (w : Q) : Q := w * densityRatio - capillaryConsumption.
Definition spacePerCement (w : Q) : Q := capillaryPerCement w + shrinkageVolume.

(** Sealed-curing threshold, per unit volume of cement: capillary water remains exactly when w >= 0.42. *)
Theorem capillaryPerCement_nonneg_iff (w : Q) : 0 <= capillaryPerCement w <-> criticalWcSealed <= w.
Proof.
  unfold capillaryPerCement.
  setoid_replace densityRatio with (63 # 20) by (vm_compute; reflexivity).
  setoid_replace capillaryConsumption with (1323 # 1000) by (vm_compute; reflexivity).
  setoid_replace criticalWcSealed with (21 # 50) by (vm_compute; reflexivity).
  split; intro h; lra.
Qed.

(** Space threshold, per unit volume of cement: the products fit exactly when w >= 0.356. *)
Theorem spacePerCement_nonneg_iff (w : Q) : 0 <= spacePerCement w <-> criticalWcSpace <= w.
Proof.
  unfold spacePerCement, capillaryPerCement.
  setoid_replace densityRatio with (63 # 20) by (vm_compute; reflexivity).
  setoid_replace capillaryConsumption with (1323 # 1000) by (vm_compute; reflexivity).
  setoid_replace shrinkageVolume with (2016 # 10000) by (vm_compute; reflexivity).
  setoid_replace criticalWcSpace with (89 # 250) by (vm_compute; reflexivity).
  split; intro h; lra.
Qed.

Lemma denom_pos (w : Q) : 0 <= w -> 0 < w * densityRatio + 1.
Proof. intro hw. assert (0 <= w * densityRatio) by (apply Qmult_le_0_compat; [exact hw | vm_compute; discriminate]). lra. Qed.

Lemma nonneg_div_iff (x d : Q) : 0 < d -> (0 <= x / d <-> 0 <= x).
Proof.
  intro hd. split; intro h.
  - setoid_replace x with (x / d * d) by (field; intro e; rewrite e in hd; discriminate).
    apply Qmult_le_0_compat; [exact h | lra].
  - apply Qle_shift_div_l; [exact hd | lra].
Qed.

(** Capillary water at complete hydration in terms of the water-cement ratio. *)
Theorem capillaryWater_full (w : Q) : 0 <= w ->
  capillaryWater (waterFraction w) 1 == densityRatio * (w - criticalWcSealed) / (w * densityRatio + 1).
Proof.
  intro hw. pose proof (denom_pos w hw) as hd.
  unfold capillaryWater, waterFraction.
  setoid_replace capillaryConsumption with (criticalWcSealed * densityRatio) by (vm_compute; reflexivity).
  field. intro e. rewrite e in hd. discriminate.
Qed.

(** The paste fraction of capillary water is the per-cement volume over the paste volume w d + 1. *)
Theorem capillaryWater_full_eq (w : Q) : 0 <= w ->
  capillaryWater (waterFraction w) 1 == capillaryPerCement w / (w * densityRatio + 1).
Proof.
  intro hw. pose proof (denom_pos w hw) as hd.
  unfold capillaryWater, waterFraction, capillaryPerCement.
  field. intro e. rewrite e in hd. discriminate.
Qed.

(** Sealed-curing threshold: capillary water remains at complete hydration exactly when w >= 0.42. *)
Theorem capillaryWater_full_nonneg_iff (w : Q) : 0 <= w ->
  (0 <= capillaryWater (waterFraction w) 1 <-> criticalWcSealed <= w).
Proof.
  intro hw. rewrite (capillaryWater_full w hw), (nonneg_div_iff _ _ (denom_pos w hw)).
  setoid_replace densityRatio with (63 # 20) by (vm_compute; reflexivity).
  setoid_replace criticalWcSealed with (21 # 50) by (vm_compute; reflexivity).
  split; intro h; lra.
Qed.

(** Capillary water and shrinkage voids at complete hydration: the space left for hydration products. *)
Theorem space_full (w : Q) : 0 <= w ->
  capillaryWater (waterFraction w) 1 + shrinkage (waterFraction w) 1 ==
    densityRatio * (w - criticalWcSpace) / (w * densityRatio + 1).
Proof.
  intro hw. pose proof (denom_pos w hw) as hd.
  unfold capillaryWater, shrinkage, waterFraction.
  setoid_replace capillaryConsumption with (criticalWcSealed * densityRatio) by (vm_compute; reflexivity).
  setoid_replace shrinkageVolume with ((criticalWcSealed - criticalWcSpace) * densityRatio) by (vm_compute; reflexivity).
  field. intro e. rewrite e in hd. discriminate.
Qed.

(** The paste fraction of space left for products is the per-cement volume over the paste volume. *)
Theorem space_full_eq (w : Q) : 0 <= w ->
  capillaryWater (waterFraction w) 1 + shrinkage (waterFraction w) 1 == spacePerCement w / (w * densityRatio + 1).
Proof.
  intro hw. pose proof (denom_pos w hw) as hd.
  unfold capillaryWater, shrinkage, waterFraction, spacePerCement, capillaryPerCement.
  field. intro e. rewrite e in hd. discriminate.
Qed.

(** Space threshold: the products fit at complete hydration exactly when w >= 0.356. *)
Theorem space_full_nonneg_iff (w : Q) : 0 <= w ->
  (0 <= capillaryWater (waterFraction w) 1 + shrinkage (waterFraction w) 1 <-> criticalWcSpace <= w).
Proof.
  intro hw. rewrite (space_full w hw), (nonneg_div_iff _ _ (denom_pos w hw)).
  setoid_replace densityRatio with (63 # 20) by (vm_compute; reflexivity).
  setoid_replace criticalWcSpace with (89 # 250) by (vm_compute; reflexivity).
  split; intro h; lra.
Qed.
