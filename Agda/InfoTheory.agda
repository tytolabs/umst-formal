------------------------------------------------------------------------
-- UMST-Formal: InfoTheory.agda
--
-- Finite product joint on lists of rationals, mirroring:
--   • Lean  @Lean/InfoTheory.lean@
--   • Coq   @Coq/InfoTheory.v@  (Qeq / Forall2 proofs)
--   • Haskell @Haskell/InfoTheory.hs@ (QC)
--
-- This Agda slice keeps the same *definitions*.  Full marginal / mass
-- identities are postulated here (stdlib ℚ + List proofs are lengthy);
-- authority for the algebraic laws remains Lean + Coq.
------------------------------------------------------------------------

module InfoTheory where

open import Data.List.Base as List using (List; []; _∷_; map; length; foldl)
open import Data.Nat using (ℕ; suc)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Sums and tensor row
------------------------------------------------------------------------

sumList : List ℚ → ℚ
sumList []       = 0ℚ
sumList (x ∷ xs) = x + sumList xs

mapMulRow : ℚ → List ℚ → List ℚ
mapMulRow p []       = []
mapMulRow p (x ∷ xs) = (p * x) ∷ mapMulRow p xs

productJoint : List ℚ → List ℚ → List (List ℚ)
productJoint []       q = []
productJoint (p ∷ ps) q = mapMulRow p q ∷ productJoint ps q

------------------------------------------------------------------------
-- Marginals (same layout as Coq/Haskell)
------------------------------------------------------------------------

marginalFirst : List (List ℚ) → List ℚ
marginalFirst []         = []
marginalFirst (r ∷ rows) = sumList r ∷ marginalFirst rows

pointwiseAdd : List ℚ → List ℚ → List ℚ
pointwiseAdd []         ys = ys
pointwiseAdd xs         [] = xs
pointwiseAdd (x ∷ xs) (y ∷ ys) = (x + y) ∷ pointwiseAdd xs ys

marginalSecond : List (List ℚ) → List ℚ
marginalSecond []         = []
marginalSecond (r ∷ rows) = foldl pointwiseAdd r rows

sumFlat : List (List ℚ) → ℚ
sumFlat []           = 0ℚ
sumFlat (row ∷ rows) = sumList row + sumFlat rows

------------------------------------------------------------------------
-- Small structural lemmas (machine-checked)
------------------------------------------------------------------------

mapMulRow-length : ∀ (p : ℚ) (q : List ℚ) → length (mapMulRow p q) ≡ length q
mapMulRow-length p []       = refl
mapMulRow-length p (x ∷ xs) = cong suc (mapMulRow-length p xs)

productJoint-first-row-length :
  ∀ (p : ℚ) (ps : List ℚ) (q : List ℚ) →
  length (mapMulRow p q) ≡ length q
productJoint-first-row-length p ps q = mapMulRow-length p q

------------------------------------------------------------------------
-- Algebraic laws (postulated; see Lean @marginalX_product@,
-- @marginalY_product@, @jointEntropy_product@ layer in Lean)
------------------------------------------------------------------------

open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)

postulate
  jointMassProduct :
    ∀ (p q : List ℚ) → sumFlat (productJoint p q) ≡ sumList p * sumList q

  marginalFirstProduct :
    ∀ (p q : List ℚ) →
    Pointwise _≡_ (marginalFirst (productJoint p q))
      (map (λ pi → pi * sumList q) p)

  marginalSecondProduct :
    ∀ (ph : ℚ) (pt q : List ℚ) →
    Pointwise _≡_ (marginalSecond (productJoint (ph ∷ pt) q))
      (map (λ qk → sumList (ph ∷ pt) * qk) q)
