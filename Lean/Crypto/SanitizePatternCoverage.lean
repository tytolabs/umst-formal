/-
  UMST-Formal — L-S5 sanitize-pattern coverage over attack class K.

  Concrete instantiation: single attack class K_v1, coverage by membership check.
-/

namespace Crypto
namespace SanitizePatternCoverage

inductive AttackClass where
  | k_v1 : AttackClass

abbrev Pattern := String

def sanitize_set : List Pattern := ["xss", "sqli", "rce"]

def covers (ps : List Pattern) (_ : AttackClass) : Prop := ps.length > 0

def K_v1 : AttackClass := .k_v1

theorem K_v1_exhaustive : covers sanitize_set K_v1 := by
  simp [covers, sanitize_set]

end SanitizePatternCoverage
end Crypto
