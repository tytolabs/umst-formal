/-
  UMST — crypto hypothesis metadata (NOT `PhysicsAxiom`).

  Physics stack: sole axiom `LandauerLaw.physicalSecondLaw` (umst-formal / double-slit).
  Crypto warrant: egoff §14bis.f-S-0 Measurement witnesses (umst-math `s0_crypto_*` tests).
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
