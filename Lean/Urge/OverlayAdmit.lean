-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/OverlayAdmit.lean

  Agentic admitted overlay — packets on L3 (WireGuard / Tailscale / LAN) are not
  an admit oracle. Overlay admissibility is suite-bound Trust ∧ UCRS gate ∧
  SDF-canonical occupancy. Sole physics axiom remains LandauerLaw.physicalSecondLaw
  (imported by sibling Urge.AdmitKleisli; **zero new axioms here**).

  This is a positive theorem: packet arrival does not imply overlay admit.
  Crypto EUF-CMA stays CryptoHypothesis (not PhysicsAxiom).
-/

namespace UMST.Urge.OverlayAdmit

/-- Carrier: L3 arrival vs the three overlay conjuncts (I §24.7). -/
structure OverlayCarrier where
  packetArrived : Prop
  suiteBound : Prop
  gateAdmit : Prop
  occupancyCanonical : Prop

/-- Overlay admit = suite ∧ gate ∧ SDF occupancy — not packet arrival. -/
def overlayAdmissible (c : OverlayCarrier) : Prop :=
  c.suiteBound ∧ c.gateAdmit ∧ c.occupancyCanonical

/-- Tunnel-as-trust counterexample: packet on wg0/tailscale0 with no suite/gate/SDF. -/
def tunnelOnly : OverlayCarrier :=
  { packetArrived := True
    suiteBound := False
    gateAdmit := False
    occupancyCanonical := False }

/-- Packet arrival is not sufficient for overlay admit (refuses VPN category error). -/
theorem packet_arrival_not_sufficient
    {c : OverlayCarrier}
    (hs : ¬ c.suiteBound) :
    ¬ overlayAdmissible c := by
  intro h
  exact hs h.1

/-- Instantiation: the tunnel-only carrier is inadmissible. -/
theorem tunnel_only_inadmissible : ¬ overlayAdmissible tunnelOnly :=
  packet_arrival_not_sufficient (c := tunnelOnly) (by intro h; exact h)

/-- MagicDNS hostname is not occupancy-canonical (label ≠ SDF fingerprint). -/
structure ReplicaLag where
  magicDnsName : Prop
  occupancyRemainderSdf : Prop

def lagIdentifiedGeometrically (r : ReplicaLag) : Prop :=
  r.occupancyRemainderSdf ∧ ¬ r.magicDnsName

theorem magicdns_not_geometric
    {r : ReplicaLag}
    (_hm : r.magicDnsName)
    (hn : ¬ r.occupancyRemainderSdf) :
    ¬ lagIdentifiedGeometrically r := by
  intro h
  exact hn h.1

/-- Positive compose: the three conjuncts are exactly overlay admit (I §24.7). -/
theorem overlay_admissible_iff_conjuncts (c : OverlayCarrier) :
    overlayAdmissible c ↔ c.suiteBound ∧ c.gateAdmit ∧ c.occupancyCanonical :=
  Iff.rfl

/-- Missing UCRS gate independently refuses overlay admit. -/
theorem gate_missing_not_admissible
    {c : OverlayCarrier} (hg : ¬ c.gateAdmit) :
    ¬ overlayAdmissible c := by
  intro h
  exact hg h.2.1

/-- Missing occupancy-canonical SDF independently refuses overlay admit. -/
theorem occupancy_missing_not_admissible
    {c : OverlayCarrier} (ho : ¬ c.occupancyCanonical) :
    ¬ overlayAdmissible c := by
  intro h
  exact ho h.2.2

/-- Production admin plane. TailscaleFallback is not production. -/
inductive OverlayAdminPlane where
  | lan
  | wireGuard
  | tailscaleFallback

def productionAdminPlaneAdmissible : OverlayAdminPlane → Prop
  | .lan => True
  | .wireGuard => True
  | .tailscaleFallback => False

/-- DID-bound WG peer: LAN/WG, not CGNAT, library never applies to kernel. -/
structure DidBoundWgPeer where
  plane : OverlayAdminPlane
  cgnatEndpoint : Prop
  kernelApply : Prop

def didBoundWgAdmissible (p : DidBoundWgPeer) : Prop :=
  productionAdminPlaneAdmissible p.plane ∧ ¬ p.cgnatEndpoint ∧ ¬ p.kernelApply

theorem tailscale_wg_peer_refused :
    ¬ didBoundWgAdmissible
      { plane := .tailscaleFallback, cgnatEndpoint := False, kernelApply := False } := by
  intro h
  exact h.1

theorem cgnat_wg_peer_refused :
    ¬ didBoundWgAdmissible
      { plane := .wireGuard, cgnatEndpoint := True, kernelApply := False } := by
  intro h
  exact h.2.1 trivial

theorem kernel_apply_wg_peer_refused :
    ¬ didBoundWgAdmissible
      { plane := .wireGuard, cgnatEndpoint := False, kernelApply := True } := by
  intro h
  exact h.2.2 trivial

theorem lan_wg_peer_eligible :
    didBoundWgAdmissible
      { plane := .lan, cgnatEndpoint := False, kernelApply := False } := by
  constructor
  · trivial
  · constructor <;> intro h <;> exact h

end OverlayAdmit
end UMST.Urge
