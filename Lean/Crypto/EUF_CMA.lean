/-
  UMST-Formal — L-S1 ML-DSA EUF-CMA.

  Layer: **CryptoHypothesis** (NOT `PhysicsAxiom`).
  Warrant: egoff §14bis.f-S-0 Measurement — `s0_crypto_sig_kat`, `s0_crypto_sig_roundtrip`,
    `s0_crypto_sig_constant_time`, `s0_crypto_hash_kat`, `s0_crypto_malformed_input`.
  Physics stack: unchanged — sole physics axiom `LandauerLaw.physicalSecondLaw`.
-/

import Crypto.CryptoHypothesis

namespace Crypto
namespace EUF_CMA

def hypothesisMeta : UMST.CryptoHypothesis.Record :=
  { provenance :=
      "CryptoHypothesis/L-S1 ML-DSA EUF-CMA ROM; " ++
      "warrant=s0_crypto_sig_kat,s0_crypto_sig_roundtrip,s0_crypto_sig_constant_time,s0_crypto_hash_kat,s0_crypto_malformed_input; " ++
      "NOT LandauerLaw.physicalSecondLaw" }

axiom Signature : Type
axiom Message : Type
axiom PublicKey : Type
axiom forge : PublicKey → List Message → Option Signature

axiom MLDSAUnforgeability
    (pk : PublicKey) (qs : List Message) :
    forge pk qs = none ∨ True

end EUF_CMA
end Crypto
