/-
  UMST-Formal — L-S5 sanitize-pattern coverage over attack class K.

  `K_v1` is opaque (enumerated GMD-7 + GSD-6 set). Exhaustive coverage for fixed `K_v1` is a
  named Tier-2 hypothesis (versioned `K_vN` bumps), not a deferred proof.
  Runtime witness: egoff `sanitize::scan_for_serials_redact` + privacy fuzz (S-4 slice).

  **No axiom.** Coverage is a field of `Spec`, so supplying a sanitize set states the claim at the
  point of supply. This is the one hypothesis in the crypto layer that a newly discovered attack
  can falsify: it is an empirical completeness claim, not a hardness assumption, and it carries a
  version so a bump is visible.
-/

namespace Crypto
namespace SanitizePatternCoverage

/-- A sanitize set together with the coverage claim it makes over a fixed attack class. -/
structure Spec where
  AttackClass  : Type
  Pattern      : Type
  sanitize_set : List Pattern
  covers       : List Pattern → AttackClass → Prop
  /-- Attack class K_v1 (GMD-7 + GSD-6 sanitize set); opaque carrier. -/
  K_v1         : AttackClass
  /-- Tier-2 fixed-K: the current sanitize set covers K_v1 (statement version v1). -/
  K_v1_exhaustive : covers sanitize_set K_v1
  /-- Version of the coverage claim; bump when the attack class changes. -/
  coverage_version : String

theorem K_v1_exhaustive (S : Spec) : S.covers S.sanitize_set S.K_v1 :=
  S.K_v1_exhaustive

end SanitizePatternCoverage
end Crypto
