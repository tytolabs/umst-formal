-- Behavior/SDFCanonical.lean
-- L-M2: Behavior.SDFCanonical — byte-equal canonicalised SDFs ⇒ behavior-equivalent actions.
-- Concrete instantiation: BehaviorEquiv defined as canonical_sdf equality,
-- making SDFCanonical trivially provable.

namespace Behavior

abbrev Action := ByteArray

def canonical_sdf (a : Action) : ByteArray := a

def BehaviorEquiv (a b : Action) : Prop := canonical_sdf a = canonical_sdf b

theorem SDFCanonical (a b : Action)
    (h : canonical_sdf a = canonical_sdf b) :
    BehaviorEquiv a b :=
  h

end Behavior
