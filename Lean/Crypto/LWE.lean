/-
  UMST-Formal — L-S0 Module-LWE hardness.

  Layer: **CryptoHypothesis** (NOT `PhysicsAxiom`).
  Warrant: egoff §14bis.f-S-0 Measurement — `s0_crypto_kem_kat`, `s0_crypto_kem_roundtrip`,
    `s0_crypto_registry_constants`, `s0_crypto_malformed_input` (umst-math/tests).
  Physics stack: unchanged — sole physics axiom `LandauerLaw.physicalSecondLaw`.
-/

import Crypto.CryptoHypothesis

namespace Crypto
namespace LWE

def hypothesisMeta : UMST.CryptoHypothesis.Record :=
  { provenance :=
      "CryptoHypothesis/L-S0 Module-LWE; NIST PQC research-frontier; " ++
      "warrant=s0_crypto_kem_kat,s0_crypto_kem_roundtrip,s0_crypto_registry_constants,s0_crypto_malformed_input; " ++
      "NOT LandauerLaw.physicalSecondLaw" }

axiom LatticeProblem : Type
axiom hardness_assumption : LatticeProblem → Prop

axiom ModuleLWEHardness (p : LatticeProblem) : hardness_assumption p

end LWE
end Crypto
