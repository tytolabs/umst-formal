/-
  UMST-Formal — L-S4 categorical trust algebra.

  Associativity and revocation absorption are Tier-1 structural axioms; `TrustAlgebra` is proved.
-/

namespace Crypto
namespace Composability

axiom Trust : Type
axiom Authority : Type
axiom compose : Trust → Trust → Trust
axiom revoke : Authority → Trust → Trust
axiom revoked : Authority → Trust

/-- Composition is associative on the trust carrier. -/
axiom compose_assoc (t₁ t₂ t₃ : Trust) :
    compose (compose t₁ t₂) t₃ = compose t₁ (compose t₂ t₃)

/-- Revoked trust is a left zero for composition. -/
axiom revoke_absorb_left (a : Authority) (T : Trust) :
    compose T (revoked a) = revoked a

theorem TrustAlgebra
    (t₁ t₂ t₃ : Trust) (a : Authority) :
    (compose (compose t₁ t₂) t₃ = compose t₁ (compose t₂ t₃)) ∧
    (∀ T : Trust, compose T (revoked a) = revoked a) :=
  ⟨compose_assoc t₁ t₂ t₃, revoke_absorb_left a⟩

end Composability
end Crypto
