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

end OverlayAdmit
end UMST.Urge
