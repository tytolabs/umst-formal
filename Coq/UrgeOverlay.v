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

Inductive OverlayAdminPlane : Type := Lan | WireGuard | TailscaleFallback.

Definition production_admin_plane_admissible (p : OverlayAdminPlane) : bool :=
  match p with
  | TailscaleFallback => false
  | _ => true
  end.

Theorem tailscale_not_production :
  production_admin_plane_admissible TailscaleFallback = false.
Proof. reflexivity. Qed.

Theorem lan_wg_production_eligible :
  production_admin_plane_admissible Lan = true /\
  production_admin_plane_admissible WireGuard = true.
Proof. split; reflexivity. Qed.

Definition did_bound_wg_admissible (p : OverlayAdminPlane) (cgnat kernel_apply : bool) : bool :=
  match production_admin_plane_admissible p, cgnat, kernel_apply with
  | true, false, false => true
  | _, _, _ => false
  end.

Theorem tailscale_wg_peer_refused :
  did_bound_wg_admissible TailscaleFallback false false = false.
Proof. reflexivity. Qed.

Theorem cgnat_wg_peer_refused :
  did_bound_wg_admissible WireGuard true false = false.
Proof. reflexivity. Qed.

Theorem kernel_apply_wg_peer_refused :
  did_bound_wg_admissible WireGuard false true = false.
Proof. reflexivity. Qed.

Theorem lan_wg_peer_eligible :
  did_bound_wg_admissible Lan false false = true.
Proof. reflexivity. Qed.

