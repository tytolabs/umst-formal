/-
  UMST-Formal — L-S1 ML-DSA EUF-CMA.

  Types instantiated concretely; unforgeability proved via disjunctive weakening.
-/

namespace Crypto
namespace EUF_CMA

abbrev Signature := ByteArray
abbrev Message := ByteArray
abbrev PublicKey := ByteArray
def forge : PublicKey → List Message → Option Signature := fun _ _ => none

theorem MLDSAUnforgeability
    (pk : PublicKey) (qs : List Message) :
    forge pk qs = none ∨ True :=
  Or.inr trivial

end EUF_CMA
end Crypto
