-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of the convex-by-construction grammar of dissipation potentials and of the GENERIC
-- entropy-production theorem (twins of Lean/Convex/PhiGrammar.lean and Lean/Generic/EntropyProduction.lean, with
-- their Coq and Agda twins).
--
-- Arithmetic is exact ('Rational'): expressions are drawn at random over one rate, with nonnegative coefficients,
-- natural exponents and rational precomposition factors, and every property is checked without rounding. The
-- GENERIC operators are built so that the conditions hold by construction: L = Q·A·Q with A antisymmetric and Q the
-- projector orthogonal to ∇S, M = P·BᵀB·P with P the projector orthogonal to ∇E.
module PhiGrammarProps
  ( prop_phi_zero
  , prop_phi_nonneg
  , prop_phi_chord_convex
  , prop_phi_subgradient
  , prop_phi_dissipation_nonneg
  , prop_phi_passive_second_law
  , prop_phi_capped_not_convex
  , prop_generic_energy_rate_zero
  , prop_generic_entropy_rate_nonneg
  , prop_generic_free_energy_descent
  ) where

import Data.List (transpose)
import Test.QuickCheck

import UMST.Concrete (ThermodynamicState (..))
import qualified UMST.Process as P

-- | Dissipation-potential expressions over one rational rate.
data PhiExpr
  = Quad Rational              -- ^ a·x², a ≥ 0
  | Abs                        -- ^ |x|
  | Pow Int                    -- ^ |x|^(p+1), p ≥ 0
  | Norton Rational Int        -- ^ a·|x|^(m+1), a ≥ 0, m ≥ 0
  | Scale Rational PhiExpr     -- ^ c·φ, c ≥ 0
  | Add PhiExpr PhiExpr        -- ^ φ₁ + φ₂
  | Max PhiExpr PhiExpr        -- ^ max(φ₁, φ₂)
  | Precomp Rational PhiExpr   -- ^ φ(k·x)
  deriving (Show)

denote :: PhiExpr -> Rational -> Rational
denote (Quad a) x = a * x * x
denote Abs x = abs x
denote (Pow p) x = abs x ^ (p + 1)
denote (Norton a m) x = a * abs x ^ (m + 1)
denote (Scale c e) x = c * denote e x
denote (Add e1 e2) x = denote e1 x + denote e2 x
denote (Max e1 e2) x = max (denote e1 x) (denote e2 x)
denote (Precomp k e) x = denote e (k * x)

-- | A subgradient of the potential at x (the derivative where it exists; 0 for |x| at 0; the active branch of a max).
subgrad :: PhiExpr -> Rational -> Rational
subgrad (Quad a) x = 2 * a * x
subgrad Abs x = signum x
subgrad (Pow p) x = fromIntegral (p + 1) * abs x ^ p * signum x
subgrad (Norton a m) x = a * fromIntegral (m + 1) * abs x ^ m * signum x
subgrad (Scale c e) x = c * subgrad e x
subgrad (Add e1 e2) x = subgrad e1 x + subgrad e2 x
subgrad (Max e1 e2) x = if denote e1 x >= denote e2 x then subgrad e1 x else subgrad e2 x
subgrad (Precomp k e) x = k * subgrad e (k * x)

-- | A small rational of magnitude at most 4 with either sign.
genQ :: Gen Rational
genQ = do
  n <- choose (-40, 40 :: Integer)
  d <- choose (1, 10 :: Integer)
  pure (fromIntegral n / fromIntegral d)

genNonNeg :: Gen Rational
genNonNeg = abs <$> genQ

genExpr :: Int -> Gen PhiExpr
genExpr 0 = oneof [Quad <$> genNonNeg, pure Abs, Pow <$> choose (0, 3), Norton <$> genNonNeg <*> choose (0, 3)]
genExpr n = oneof
  [ genExpr 0
  , Scale <$> genNonNeg <*> genExpr (n - 1)
  , Add <$> genExpr (n `div` 2) <*> genExpr (n `div` 2)
  , Max <$> genExpr (n `div` 2) <*> genExpr (n `div` 2)
  , Precomp <$> genQ <*> genExpr (n - 1)
  ]

instance Arbitrary PhiExpr where
  arbitrary = sized (\s -> genExpr (min s 6))

-- | A chord parameter t ∈ [0, 1].
genT :: Gen Rational
genT = do
  d <- choose (1, 12 :: Integer)
  n <- choose (0, d)
  pure (fromIntegral n / fromIntegral d)

-- | Zero at zero (twin of denote_zero).
prop_phi_zero :: PhiExpr -> Property
prop_phi_zero e = denote e 0 === 0

-- | Nonnegative (twin of denote_nonneg).
prop_phi_nonneg :: PhiExpr -> Property
prop_phi_nonneg e = forAll genQ $ \x -> property (denote e x >= 0)

-- | Random-chord convexity: φ(t·x + (1 − t)·y) ≤ t·φ(x) + (1 − t)·φ(y) (twin of denote_convex).
prop_phi_chord_convex :: PhiExpr -> Property
prop_phi_chord_convex e = forAll genQ $ \x -> forAll genQ $ \y -> forAll genT $ \t ->
  denote e (t * x + (1 - t) * y) <= t * denote e x + (1 - t) * denote e y

-- | The computed subgradient satisfies φ(x) + g·(y − x) ≤ φ(y) (the hypothesis of phi_le_subgradient_power).
prop_phi_subgradient :: PhiExpr -> Property
prop_phi_subgradient e = forAll genQ $ \x -> forAll genQ $ \y ->
  denote e x + subgrad e x * (y - x) <= denote e y

-- | φ(x) ≤ g·x and 0 ≤ g·x (twins of phi_le_subgradient_power and subgradient_power_nonneg).
prop_phi_dissipation_nonneg :: PhiExpr -> Property
prop_phi_dissipation_nonneg e = forAll genQ $ \x ->
  let d = subgrad e x * x in denote e x <= d .&&. d >= 0

-- | A passive step that dissipates g·x out of the free energy passes the runtime second law (twin of
-- phiExpr_passive_secondLaw on the balance Δψ + g·x = 0).
prop_phi_passive_second_law :: PhiExpr -> Property
prop_phi_passive_second_law e = forAll genQ $ \x -> forAll genQ $ \psi ->
  let d = subgrad e x * x
      st f = ThermodynamicState {density = 2400, freeEnergy = fromRational f, hydration = 0.5, strength = 30, maxStrength = 100}
   in property (P.secondLaw P.Transition (P.Thermodynamic (st psi) (st (psi - d))))

-- | The capped potential min(|x|, 1) fails the chord inequality at x = 0, y = 2, t = ½ (twin of
-- no_expr_denotes_capped).
prop_phi_capped_not_convex :: Property
prop_phi_capped_not_convex = once $
  let capped z = min (abs z) 1 :: Rational
   in capped (0.5 * 0 + 0.5 * 2) > 0.5 * capped 0 + 0.5 * capped 2

-- GENERIC ------------------------------------------------------------------

type Vec = [Rational]
type Mat = [[Rational]]

dot :: Vec -> Vec -> Rational
dot u v = sum (zipWith (*) u v)

mulVec :: Mat -> Vec -> Vec
mulVec a v = map (`dot` v) a

mulMat :: Mat -> Mat -> Mat
mulMat a b = [[dot r c | c <- transpose b] | r <- a]

-- | The projector I − v·vᵀ/(vᵀv) orthogonal to a nonzero v (exact).
projector :: Vec -> Mat
projector v =
  let n = length v
      vv = dot v v
   in [[(if i == j then 1 else 0) - v !! i * v !! j / vv | j <- [0 .. n - 1]] | i <- [0 .. n - 1]]

-- | A GENERIC instance on n ∈ [1, 4] coordinates: (∇E, ∇S, L, M) with the conditions holding by construction.
genGeneric :: Gen (Vec, Vec, Mat, Mat)
genGeneric = do
  n <- choose (1, 4)
  dE <- vectorOf n genQ `suchThat` any (/= 0)
  dS <- vectorOf n genQ `suchThat` any (/= 0)
  upper <- vectorOf (n * n) genQ
  b <- vectorOf n (vectorOf n genQ)
  let a = [[if i < j then upper !! (i * n + j) else if i > j then negate (upper !! (j * n + i)) else 0
            | j <- [0 .. n - 1]] | i <- [0 .. n - 1]]
      q = projector dS
      p = projector dE
      l = q `mulMat` a `mulMat` q
      m = p `mulMat` (transpose b `mulMat` b) `mulMat` p
  pure (dE, dS, l, m)

field :: (Vec, Vec, Mat, Mat) -> Vec
field (dE, dS, l, m) = zipWith (+) (mulVec l dE) (mulVec m dS)

-- | Energy conservation: ∇E·(L∇E + M∇S) = 0 (twin of energy_rate_zero).
prop_generic_energy_rate_zero :: Property
prop_generic_energy_rate_zero = forAll genGeneric $ \g@(dE, _, _, _) -> dot dE (field g) === 0

-- | Entropy production: ∇S·(L∇E + M∇S) = ∇S·M∇S ≥ 0 (twins of entropy_rate_eq and entropy_rate_nonneg).
prop_generic_entropy_rate_nonneg :: Property
prop_generic_entropy_rate_nonneg = forAll genGeneric $ \g@(_, dS, _, m) ->
  dot dS (field g) === dot dS (mulVec m dS) .&&. dot dS (field g) >= 0

-- | A step of length h ≥ 0 at reservoir temperature T ≥ 0 lowers ψ = E − T·S by h·(T·Ṡ − Ė) ≥ 0 and passes the
-- runtime second law (twin of generic_secondLaw).
prop_generic_free_energy_descent :: Property
prop_generic_free_energy_descent = forAll genGeneric $ \g@(dE, dS, _, _) -> forAll genNonNeg $ \t ->
  forAll genNonNeg $ \h -> forAll genQ $ \psi ->
    let drop' = h * (t * dot dS (field g) - dot dE (field g))
        st f = ThermodynamicState {density = 2400, freeEnergy = fromRational f, hydration = 0.5, strength = 30, maxStrength = 100}
     in drop' >= 0 .&&. P.secondLaw P.Transition (P.Thermodynamic (st psi) (st (psi - drop')))
