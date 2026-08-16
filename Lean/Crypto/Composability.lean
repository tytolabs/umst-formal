-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal — L-S4 categorical trust algebra.

  Associativity and revocation absorption are Tier-1 structural assumptions; `TrustAlgebra` is
  proved from them. Runtime consumer: egoff `Trust` ADT + `TrustGate` (S-1/S-2 slices).
  Agda mirror: priority residue `R-LS4-agda-priority`.

  **No axiom.** Both laws are fields of `Spec`, discharged wherever a trust algebra is constructed.
  Physics stack unchanged — the sole axiom in the workspace is `LandauerLaw.physicalSecondLaw`.
-/

namespace Crypto
namespace Composability

/-- A trust algebra: carriers, operations, and the two structural laws they must satisfy.
    Constructing a `Spec` discharges both laws for that algebra. -/
structure Spec where
  Trust     : Type
  Authority : Type
  compose   : Trust → Trust → Trust
  revoke    : Authority → Trust → Trust
  revoked   : Authority → Trust
  /-- Composition is associative on the trust carrier. -/
  compose_assoc : ∀ t₁ t₂ t₃ : Trust,
    compose (compose t₁ t₂) t₃ = compose t₁ (compose t₂ t₃)
  /-- Revoked trust is a left zero for composition. -/
  revoke_absorb_left : ∀ (a : Authority) (T : Trust),
    compose T (revoked a) = revoked a

theorem TrustAlgebra (A : Spec)
    (t₁ t₂ t₃ : A.Trust) (a : A.Authority) :
    (A.compose (A.compose t₁ t₂) t₃ = A.compose t₁ (A.compose t₂ t₃)) ∧
    (∀ T : A.Trust, A.compose T (A.revoked a) = A.revoked a) :=
  ⟨A.compose_assoc t₁ t₂ t₃, fun T => A.revoke_absorb_left a T⟩

end Composability
end Crypto
