-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST — crypto hypothesis metadata (NOT `PhysicsAxiom`).

  Physics stack: sole axiom `LandauerLaw.physicalSecondLaw` (umst-formal / double-slit).
  Crypto warrant: egoff §14bis.f-S-0 Measurement witnesses (umst-algebra `s0_crypto_*` tests).
  Bridge rows: Tier-2 compose targets (e.g. L-S3 amplitude bound) — not Landauer.
-/

namespace UMST
namespace CryptoHypothesis

/-- Hypothesis record: every crypto-layer assumption carries provenance text. -/
structure Record where
  provenance : String
  deriving Inhabited

/-- Tier-2 bridge between proved quantum lemmas and meso observables (not second law). -/
structure BridgeRecord extends Record

end CryptoHypothesis
end UMST
