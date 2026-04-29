/-
  UMST-Formal — L-S4 categorical trust algebra (stub).

  ZCI-EXEMPT: categorical structure with composition + revocation arrow classes.
  Agda port queued as R-LS4-agda-priority per SECURITY-ARC-PLAN §16.2.
-/

namespace Crypto
namespace Composability

axiom Trust : Type
axiom Authority : Type
axiom compose : Trust → Trust → Trust
axiom revoke : Authority → Trust → Trust
axiom revoked : Authority → Trust

/-- Trust composition is associative and revoked authority is absorbing.
    Axiomatised: categorical structure pending Agda port (R-LS4-agda-priority). -/
axiom TrustAlgebra
    (t₁ t₂ t₃ : Trust) (a : Authority) :
    (compose (compose t₁ t₂) t₃ = compose t₁ (compose t₂ t₃)) ∧
    (∀ T : Trust, compose T (revoked a) = revoked a)

end Composability
end Crypto
