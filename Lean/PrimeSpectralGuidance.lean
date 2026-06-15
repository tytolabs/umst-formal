/-
  UMST-Formal: PrimeSpectralGuidance.lean
  Lean 4 — Prime-statistics-inspired guidance on auxiliary multiplicative channels.

  Layer A (this file): spectral filters on `MultiplicativeChannel` that do NOT alter
  the four-conjunct thermodynamic gate on `ThermodynamicState`.

  Academic honesty: productive analogies only — no claim that primes emerge from
  Clausius–Duhem. See `Docs/PRIME_SPECTRAL_UMST_DESIGN.md`.

  Zero sorry. Zero new axioms.
-/

import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.VonMangoldt
import Gate

namespace UMST.PrimeSpectral

open UMST
open BigOperators

-- ================================================================
-- SECTION 1: Auxiliary multiplicative channel
-- ================================================================

/-- Auxiliary signal indexed by `Fin n` (slot `i` ↔ natural index `i.val + 1`).
    NOT part of `ThermodynamicState`; gate fields are untouched by channel filters. -/
structure MultiplicativeChannel (n : Nat) where
  values : Fin n → ℚ

/-- Prime period index for modulation (multiplicative indivisibility analogy). -/
structure PrimePeriod where
  p : Nat
  hp : Nat.Prime p

-- ================================================================
-- SECTION 2: von Mangoldt surrogate (ℚ layer)
-- ================================================================

/-- Rational surrogate for von Mangoldt impulse weight at `n`.
    Uses `minFac n` when `n` is a prime power; 0 otherwise.
    Differs from `ArithmeticFunction.vonMangoldt` (which returns `Real.log p`). -/
def vonMangoldtWeight (n : Nat) : ℚ :=
  if _h : IsPrimePow n then (Nat.minFac n : ℚ) else 0

@[simp]
theorem vonMangoldtWeight_zero : vonMangoldtWeight 0 = 0 := by
  simp [vonMangoldtWeight, not_isPrimePow_zero]

@[simp]
theorem vonMangoldtWeight_one : vonMangoldtWeight 1 = 0 := by
  simp [vonMangoldtWeight, not_isPrimePow_one]

/-- At a prime `p`, weight equals `p`. -/
theorem vonMangoldtWeight_prime {p : Nat} (hp : Nat.Prime p) :
    vonMangoldtWeight p = p := by
  simp [vonMangoldtWeight, hp.isPrimePow, hp.minFac_eq]

-- ================================================================
-- SECTION 3: Spectral filter (endofunctor on channels)
-- ================================================================

/-- Elementwise spectral filter: `values' i = weights i * values i`.
    Identity weights recover the input (`spectralFilter_id`). -/
def spectralFilter {T : Nat} (weights : Fin T → ℚ) (s : MultiplicativeChannel T) :
    MultiplicativeChannel T where
  values := fun i => weights i * s.values i

@[simp]
theorem spectralFilter_values {T : Nat} (weights : Fin T → ℚ) (s : MultiplicativeChannel T)
    (i : Fin T) :
    (spectralFilter weights s).values i = weights i * s.values i := rfl

/-- Identity filter is the identity endofunctor. -/
theorem spectralFilter_id {T : Nat} (s : MultiplicativeChannel T) :
    spectralFilter (fun _ => (1 : ℚ)) s = s := by
  cases s
  simp [spectralFilter, MultiplicativeChannel]

/-- Pointwise perturbation identity: `(w i - 1) * s i`. -/
theorem spectralFilter_perturb {T : Nat} (w : Fin T → ℚ) (s : MultiplicativeChannel T)
    (i : Fin T) :
    (spectralFilter w s).values i - s.values i = (w i - 1) * s.values i := by
  simp [spectralFilter_values]
  ring

/-- If every weight is `1`, perturbation is zero at each index. -/
theorem spectralFilter_perturb_zero {T : Nat} (s : MultiplicativeChannel T) (i : Fin T) :
    (spectralFilter (fun _ => (1 : ℚ)) s).values i - s.values i = 0 := by
  rw [spectralFilter_perturb]
  simp

/-- L¹-style weight deviation sum (finite, exact ℚ). -/
def weightDeviationL1 {T : Nat} (w : Fin T → ℚ) : ℚ :=
  ∑ i : Fin T, |w i - 1|

/-- Bounded deviation: pointwise bound from L¹ bound (crude but provable). -/
theorem spectralFilter_deviation_le_l1 {T : Nat} (w : Fin T → ℚ) (s : MultiplicativeChannel T)
    (i : Fin T) (h : |w i - 1| ≤ weightDeviationL1 w) :
    |(spectralFilter w s).values i - s.values i| ≤
      weightDeviationL1 w * max (|s.values i|) 0 := by
  rw [spectralFilter_perturb]
  have hmul : |(w i - 1) * s.values i| = |w i - 1| * |s.values i| := abs_mul _ _
  rw [hmul]
  have hw : 0 ≤ weightDeviationL1 w := by
    dsimp [weightDeviationL1]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  exact mul_le_mul h (le_max_left _ _) (abs_nonneg _) hw

-- ================================================================
-- SECTION 4: Explicit formula — finite truncation
-- ================================================================

/-- Finite von Mangoldt-weighted sum (explicit-formula truncation on `Fin T`). -/
def mangoldtWeightedSum {T : Nat} (f : Fin T → ℚ) : ℚ :=
  ∑ i : Fin T, vonMangoldtWeight (i.val + 1) * f i

theorem mangoldtWeightedSum_add {T : Nat} (f g : Fin T → ℚ) :
    mangoldtWeightedSum (fun i => f i + g i) =
      mangoldtWeightedSum f + mangoldtWeightedSum g := by
  simp [mangoldtWeightedSum, mul_add, Finset.sum_add_distrib]

theorem mangoldtWeightedSum_zero {T : Nat} :
    mangoldtWeightedSum (f := fun (_ : Fin T) => (0 : ℚ)) = 0 := by
  simp [mangoldtWeightedSum]

-- ================================================================
-- SECTION 5: Coprime prime periods (topological mixing analogy)
-- ================================================================

/-- Distinct primes are coprime. -/
theorem prime_coprime {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    Nat.Coprime p q :=
  (Nat.coprime_primes hp hq).mpr hne

/-- lcm of coprime primes equals their product. -/
theorem coprime_primes_lcm_eq_mul {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) : Nat.lcm p q = p * q := by
  have hc := prime_coprime hp hq hne
  exact Nat.Coprime.lcm_eq_mul hc

-- ================================================================
-- SECTION 6: Guided state — thermo + auxiliary channel
-- ================================================================

/-- State bundle: gate scalars + auxiliary multiplicative channel. -/
structure GuidedState (n : Nat) where
  thermo : ThermodynamicState
  channel : MultiplicativeChannel n

/-- Gate projection: auxiliary channel is invisible to the thermodynamic gate. -/
def gateProjection {n : Nat} (g : GuidedState n) : ThermodynamicState := g.thermo

@[simp]
theorem gateProjection_id {n : Nat} (g : GuidedState n) : gateProjection g = g.thermo := rfl

/-- Apply a channel filter; thermodynamic fields unchanged. -/
def applyChannelFilter {n : Nat} (g : GuidedState n)
    (f : MultiplicativeChannel n → MultiplicativeChannel n) : GuidedState n where
  thermo := g.thermo
  channel := f g.channel

/-- Channel guidance preserves admissibility on thermodynamic scalars. -/
theorem applyChannelFilter_admissible {n : Nat} (g₁ g₂ : GuidedState n)
    (h : Admissible g₁.thermo g₂.thermo)
    (f : MultiplicativeChannel n → MultiplicativeChannel n) :
    Admissible (applyChannelFilter g₁ f).thermo (applyChannelFilter g₂ f).thermo := by
  simpa [applyChannelFilter] using h

/-- Alias: guidance on auxiliary data alone cannot break the gate. -/
theorem guidance_preserves_admissible {n : Nat} (old new : ThermodynamicState)
    (h : Admissible old new)
    (_f : MultiplicativeChannel n → MultiplicativeChannel n) :
    Admissible old new := h

/-- Graded admissibility is likewise preserved when only the channel changes. -/
theorem applyChannelFilter_admissibleN {n : Nat} (m : Nat) (g₁ g₂ : GuidedState n)
    (h : AdmissibleN m g₁.thermo g₂.thermo)
    (f : MultiplicativeChannel n → MultiplicativeChannel n) :
    AdmissibleN m (applyChannelFilter g₁ f).thermo (applyChannelFilter g₂ f).thermo := by
  simpa [applyChannelFilter] using h

/-- Kleisli / graded composition commutes with channel guidance when thermo paths are fixed. -/
theorem kleisli_guidance_commute {n m k : Nat} (g₁ g₂ g₃ : GuidedState n)
    (h1 : AdmissibleN m g₁.thermo g₂.thermo)
    (h2 : AdmissibleN k g₂.thermo g₃.thermo)
    (f : MultiplicativeChannel n → MultiplicativeChannel n) :
    AdmissibleN (m + k)
      (applyChannelFilter g₁ f).thermo
      (applyChannelFilter g₃ f).thermo := by
  exact admissibleN_compose (applyChannelFilter_admissibleN m g₁ g₂ h1 f)
    (applyChannelFilter_admissibleN k g₂ g₃ h2 f)

-- ================================================================
-- SECTION 7: Zeta-zero oscillatory basis (definition only; convergence open)
-- ================================================================

/-- Oscillatory basis function `cos(γ · log n)` for `n > 0` (filter-bank analogy).
    Convergence of infinite sums over zeta zeros is **OPEN** — not used in gate proofs. -/
noncomputable def zetaOscillator (gamma : ℝ) (n : Nat) (_hn : 0 < n) : ℝ :=
  Real.cos (gamma * Real.log n)

end UMST.PrimeSpectral
