-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/GeometricMemory.lean

  §5.3 geometric memory identity of a history object is a canonical SDF/F-Rep
  fingerprint — not a host id, CGNAT address, or MagicDNS name.
  Zero new physics axioms. Completes the Rust pin `Urge.GeometricMemory`.
-/

namespace UMST.Urge.GeometricMemory

/-- Host-id keyed identity (Tailscale/CGNAT style) vs SDF fingerprint. -/
structure HistoryId where
  hostId : Prop
  sdfFingerprint : Prop

def geometricIdentity (h : HistoryId) : Prop :=
  h.sdfFingerprint ∧ ¬ h.hostId

theorem host_id_not_geometric
    {h : HistoryId}
    (_hh : h.hostId)
    (hs : ¬ h.sdfFingerprint) :
    ¬ geometricIdentity h := by
  intro g
  exact hs g.1

def payloadOnly : HistoryId :=
  { hostId := True, sdfFingerprint := False }

theorem payload_only_refused : ¬ geometricIdentity payloadOnly :=
  host_id_not_geometric (h := payloadOnly) trivial (fun h => h)

end GeometricMemory
end UMST.Urge
