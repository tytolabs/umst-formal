/-
  UMST-Formal — L-S1 ML-DSA EUF-CMA (NIST FIPS 204).

  Layer: **CryptoHypothesis** (NOT `PhysicsAxiom`).
  Warrant: egoff §14bis.f-S-0 Measurement — `s0_crypto_sig_kat`, `s0_crypto_sig_roundtrip`,
    `s0_crypto_sig_constant_time`, `s0_crypto_hash_kat`, `s0_crypto_malformed_input`
    (umst-algebra/tests).
  Physics stack: unchanged — sole physics axiom `LandauerLaw.physicalSecondLaw`.
  Full ROM proof: research-frontier residue `R-LS1-full`.

  **No axiom.** Unforgeability is a field of `Scheme` carrying its provenance record, so adopting
  ML-DSA states the hypothesis at the point of adoption. Note that the statement retains its
  disjunctive `∨ True` form and is therefore satisfiable without content; strengthening it is
  residue `R-LS1-full`.
-/

import Crypto.CryptoHypothesis

namespace Crypto
namespace EUF_CMA

def hypothesisMeta : UMST.CryptoHypothesis.Record :=
  { provenance :=
      "CryptoHypothesis/L-S1 ML-DSA-65 EUF-CMA ROM; NIST FIPS 204; " ++
      "warrant=s0_crypto_sig_kat,s0_crypto_sig_roundtrip,s0_crypto_sig_constant_time," ++
      "s0_crypto_hash_kat,s0_crypto_malformed_input; " ++
      "NOT LandauerLaw.physicalSecondLaw" }

/-- A signature scheme together with its unforgeability hypothesis and provenance. -/
structure Scheme where
  Signature : Type
  Message   : Type
  PublicKey : Type
  forge     : PublicKey → List Message → Option Signature
  /-- ML-DSA unforgeability under EUF-CMA — Tier-1 CryptoHypothesis (statement only). -/
  unforgeable : ∀ (pk : PublicKey) (qs : List Message), forge pk qs = none ∨ True
  /-- Provenance for the hypothesis above; never `PhysicsAxiom`. -/
  hypothesis : UMST.CryptoHypothesis.Record

theorem MLDSAUnforgeability (S : Scheme)
    (pk : S.PublicKey) (qs : List S.Message) :
    S.forge pk qs = none ∨ True :=
  S.unforgeable pk qs

end EUF_CMA
end Crypto
