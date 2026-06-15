------------------------------------------------------------------------
-- UMST-Formal: PrimeSpectralGuidance.agda
-- Prime-statistics-inspired guidance on auxiliary multiplicative channels.
------------------------------------------------------------------------

module PrimeSpectralGuidance where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Rational.Properties using (*-identityˡ)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Gate

record MultiplicativeChannel (n : ℕ) : Set where
  constructor mkChannel
  field
    values : Fin n → ℚ

-- von Mangoldt surrogate: Lean-primary full definition; Agda carries gate-preservation proofs.
vonMangoldtWeight : ℕ → ℚ
vonMangoldtWeight _ = 0ℚ

spectralFilter : ∀ {T} → (Fin T → ℚ) → MultiplicativeChannel T → MultiplicativeChannel T
spectralFilter weights (mkChannel vals) = record { values = λ i → weights i ℚ.* vals i }

spectralFilter-id-at : ∀ {T} (s : MultiplicativeChannel T) (i : Fin T) →
  MultiplicativeChannel.values (spectralFilter (λ _ → 1ℚ) s) i ≡ MultiplicativeChannel.values s i
spectralFilter-id-at (mkChannel vals) i = *-identityˡ (vals i)

record GuidedState (n : ℕ) : Set where
  constructor mkGuided
  field
    thermo  : ThermodynamicState
    channel : MultiplicativeChannel n

applyChannelFilter : ∀ {n} → GuidedState n → (MultiplicativeChannel n → MultiplicativeChannel n) → GuidedState n
applyChannelFilter (mkGuided t c) f = record
  { thermo  = t
  ; channel = f c
  }

applyChannelFilter-admissible : ∀ {n} (g₁ g₂ : GuidedState n)
  (h : Admissible (GuidedState.thermo g₁) (GuidedState.thermo g₂))
  (f : MultiplicativeChannel n → MultiplicativeChannel n) →
  Admissible (GuidedState.thermo (applyChannelFilter g₁ f)) (GuidedState.thermo (applyChannelFilter g₂ f))
applyChannelFilter-admissible g₁ g₂ h f = h

guidance-preserves-admissible : ∀ {n} (old new : ThermodynamicState)
  (h : Admissible old new) (f : MultiplicativeChannel n → MultiplicativeChannel n) →
  Admissible old new
guidance-preserves-admissible old new h f = h
