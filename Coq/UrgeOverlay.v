(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* UrgeOverlay: packet arrival is not overlay admit (refuses tunnel-as-trust). *)
(* Zero new physics axioms. *)

From Coq Require Import Bool.

Record OverlayCarrier : Type := mkOverlay {
  packetArrived : bool;
  suiteBound : bool;
  gateAdmit : bool;
  occupancyCanonical : bool
}.

Definition overlay_admissible (c : OverlayCarrier) : Prop :=
  suiteBound c = true /\ gateAdmit c = true /\ occupancyCanonical c = true.

Definition tunnel_only : OverlayCarrier :=
  mkOverlay true false false false.

Theorem packet_not_sufficient :
  ~ (forall c : OverlayCarrier, packetArrived c = true -> overlay_admissible c).
Proof.
  intro H.
  specialize (H tunnel_only eq_refl).
  unfold overlay_admissible, tunnel_only in H.
  simpl in H.
  destruct H as [Hs _].
  discriminate.
Qed.

Theorem tunnel_only_inadmissible : ~ overlay_admissible tunnel_only.
Proof.
  unfold overlay_admissible, tunnel_only; simpl.
  intros [Hs _]; discriminate.
Qed.
