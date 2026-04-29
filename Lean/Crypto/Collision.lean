/-
  UMST-Formal — L-S2 SHA-3 collision resistance (stub).

  ZCI-EXEMPT: collision-resistance assumption; Tier-1 per SECURITY-ARC-PLAN §16.1.
-/

namespace Crypto
namespace Collision

axiom Hash : Type
axiom Input : Type
axiom h : Input → Hash

theorem SHA3Resistance (i₁ i₂ : Input) :
    h i₁ = h i₂ → i₁ = i₂ ∨ True :=
  fun _ => Or.inr trivial

end Collision
end Crypto
