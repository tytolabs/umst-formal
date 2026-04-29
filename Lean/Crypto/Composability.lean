/-
  UMST-Formal — L-S4 categorical trust algebra.

  Concrete instantiation: Trust is a free monoid (List Nat) with an absorbing element.
  Associativity follows from List.append_assoc; absorption from definition.
-/

namespace Crypto
namespace Composability

/-- Trust token: `none` = revoked (absorbing), `some ts` = live trust chain. -/
abbrev Trust := Option (List Nat)

abbrev Authority := Unit

def compose (a b : Trust) : Trust :=
  match a, b with
  | some xs, some ys => some (xs ++ ys)
  | _, _ => none  -- revoked absorbs

def revoke (_ : Authority) (_ : Trust) : Trust := none
def revoked (_ : Authority) : Trust := none

theorem TrustAlgebra
    (t₁ t₂ t₃ : Trust) (a : Authority) :
    (compose (compose t₁ t₂) t₃ = compose t₁ (compose t₂ t₃)) ∧
    (∀ T : Trust, compose T (revoked a) = revoked a) := by
  constructor
  · -- associativity
    simp only [compose]
    split <;> split <;> simp_all [List.append_assoc]
    all_goals (split <;> simp_all)
  · -- absorption: revoked a = none, compose T none = none
    intro T
    simp [compose, revoked]
    split <;> rfl

end Composability
end Crypto
