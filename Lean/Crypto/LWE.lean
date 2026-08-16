/-
  UMST-Formal — L-S0 Module-LWE hardness (ML-KEM-768 / NIST FIPS 203).

  Layer: **CryptoHypothesis** (NOT `PhysicsAxiom`).
  Warrant: egoff §14bis.f-S-0 Measurement — `s0_crypto_kem_kat`, `s0_crypto_kem_roundtrip`,
    `s0_crypto_kem_constant_time`, `s0_crypto_registry_constants`, `s0_crypto_malformed_input`
    (umst-algebra/tests).
  Physics stack: unchanged — sole physics axiom `LandauerLaw.physicalSecondLaw`.
  Full lattice proof: research-frontier residue `R-LS0-full` (very low priority).

  **No axiom.** Hardness is a field of `Spec`, discharged where a lattice family is supplied.
-/

import Crypto.CryptoHypothesis

namespace Crypto
namespace LWE

def hypothesisMeta : UMST.CryptoHypothesis.Record :=
  { provenance :=
      "CryptoHypothesis/L-S0 Module-LWE ML-KEM-768; NIST FIPS 203 research-frontier; " ++
      "warrant=s0_crypto_kem_kat,s0_crypto_kem_roundtrip,s0_crypto_kem_constant_time," ++
      "s0_crypto_registry_constants,s0_crypto_malformed_input; " ++
      "NOT LandauerLaw.physicalSecondLaw" }

/-- A lattice problem family together with its hardness hypothesis and provenance. -/
structure Spec where
  LatticeProblem     : Type
  hardness_assumption : LatticeProblem → Prop
  /-- Module-LWE / Module-LWR hardness — Tier-1 CryptoHypothesis (statement only). -/
  hardness : ∀ p : LatticeProblem, hardness_assumption p
  /-- Provenance for the hypothesis above; never `PhysicsAxiom`. -/
  hypothesis : UMST.CryptoHypothesis.Record

theorem ModuleLWEHardness (L : Spec) (p : L.LatticeProblem) :
    L.hardness_assumption p :=
  L.hardness p

end LWE
end Crypto
