-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of the composition law of GSM atoms and the glue fraction (twins of
-- Lean/Composition/GsmMonoid.lean, Coq/Composition/GsmMonoid.v and Agda/Composition/GsmMonoid.agda; W-44).
--
-- Potentials are drawn from the family a·x² + b·|x| (a, b ≥ 0) and atoms add a free energy k·(s − s0)²/2 (k ≥ 0);
-- coefficients, rates and states are exact rationals, so every algebraic law is checked with equality, not a
-- tolerance. The bridge properties run the runtime second law ('P.secondLaw' on the transition case) on the
-- composite step, with free-energy gaps of at least 0.01 so the verdict sits far outside the gate's 1e-6 tolerance.
module GsmMonoidProps
  ( prop_gsm_support_closed
  , prop_gsm_power_nonneg
  , prop_gsm_power_homomorphism
  , prop_gsm_potential_monoid_laws
  , prop_gsm_atom_monoid_laws
  , prop_gsm_residual_homomorphism
  , prop_gsm_combination_admissible
  , prop_gsm_convex_glue_admissible
  , prop_gsm_negative_glue_refused
  , prop_gsm_glue_fraction_gt_one_negative
  , gsmMonoidProps
  ) where

import Test.QuickCheck

import UMST.Concrete (ThermodynamicState (..))
import UMST.GsmMonoid
import qualified UMST.Process as P

-- | A non-negative rational with numerator in [0, 1000] and denominator in [1, 100].
genNonNeg :: Gen Rational
genNonNeg = (\n d -> fromIntegral n / fromIntegral d) <$> choose (0 :: Integer, 1000) <*> choose (1 :: Integer, 100)

-- | A rational of either sign.
genQ :: Gen Rational
genQ = (*) <$> elements [1, -1] <*> genNonNeg

genPotential :: Gen (Rational, Rational)
genPotential = (,) <$> genNonNeg <*> genNonNeg

genAtom :: Gen (Rational, Rational, Rational, Rational)
genAtom = (,,,) <$> genNonNeg <*> genQ <*> genNonNeg <*> genNonNeg

mkAtom :: (Rational, Rational, Rational, Rational) -> GsmAtom
mkAtom (k, s0, a, b) = quadAtom k s0 a b

-- | The supporting-line inequality phi x + dphi x (y − x) ≤ phi y.
supports :: GsmPotential -> Rational -> Rational -> Bool
supports p x y = phi p x + dphi p x * (y - x) <= phi p y

-- | A state with free energy @f@ (density, hydration and strength fixed).
st :: Rational -> ThermodynamicState
st f = ThermodynamicState {density = 2400, freeEnergy = fromRational f, hydration = 0.5, strength = 30, maxStrength = 100}

-- | Supporting lines are closed under sum and non-negative scaling, and the empty composite is pinned at zero.
prop_gsm_support_closed :: Property
prop_gsm_support_closed = forAll genPotential $ \(a, b) -> forAll genPotential $ \(a', b') ->
  forAll genNonNeg $ \c -> forAll genQ $ \x -> forAll genQ $ \y ->
    let p = quadAbsPotential a b
        q = quadAbsPotential a' b'
     in conjoin
          [ property (supports p x y)
          , property (supports (p <> q) x y)
          , property (supports (scalePotential c p) x y)
          , phi (p <> q) 0 === 0
          , phi (mempty :: GsmPotential) x === 0
          ]

-- | Dissipation of any non-negative combination is non-negative and dominates the potential.
prop_gsm_power_nonneg :: Property
prop_gsm_power_nonneg = forAll (listOf ((,) <$> genNonNeg <*> genPotential)) $ \cps -> forAll genQ $ \x ->
  let p = mconcat [scalePotential c (uncurry quadAbsPotential ab) | (c, ab) <- cps]
   in conjoin [property (power p x >= 0), property (phi p x <= power p x)]

-- | The power is a monoid homomorphism into the non-negative rationals: zero, additive, homogeneous.
prop_gsm_power_homomorphism :: Property
prop_gsm_power_homomorphism = forAll genPotential $ \(a, b) -> forAll genPotential $ \(a', b') ->
  forAll genNonNeg $ \c -> forAll genQ $ \x ->
    let p = quadAbsPotential a b
        q = quadAbsPotential a' b'
     in conjoin
          [ power mempty x === 0
          , power (p <> q) x === power p x + power q x
          , power (scalePotential c p) x === c * power p x
          ]

-- | Potentials form a commutative monoid and a cone (pointwise in phi and dphi).
prop_gsm_potential_monoid_laws :: Property
prop_gsm_potential_monoid_laws = forAll genPotential $ \pa -> forAll genPotential $ \pb ->
  forAll genPotential $ \pc -> forAll genNonNeg $ \c -> forAll genNonNeg $ \d -> forAll genQ $ \x ->
    let p = uncurry quadAbsPotential pa
        q = uncurry quadAbsPotential pb
        r = uncurry quadAbsPotential pc
        eqAt u v = (phi u x, dphi u x) === (phi v x, dphi v x)
     in conjoin
          [ eqAt ((p <> q) <> r) (p <> (q <> r))
          , eqAt (p <> q) (q <> p)
          , eqAt (mempty <> p) p
          , eqAt (p <> mempty) p
          , eqAt (scalePotential 1 p) p
          , eqAt (scalePotential (c * d) p) (scalePotential c (scalePotential d p))
          , eqAt (scalePotential c (p <> q)) (scalePotential c p <> scalePotential c q)
          , eqAt (scalePotential (c + d) p) (scalePotential c p <> scalePotential d p)
          ]

-- | Atoms form a commutative monoid and a cone (pointwise in psi, dpsi and the potential).
prop_gsm_atom_monoid_laws :: Property
prop_gsm_atom_monoid_laws = forAll genAtom $ \ga -> forAll genAtom $ \gb -> forAll genAtom $ \gc ->
  forAll genNonNeg $ \c -> forAll genQ $ \x ->
    let a = mkAtom ga
        b = mkAtom gb
        d = mkAtom gc
        eqAt u v =
          (psi u x, dpsi u x, phi (pot u) x, dphi (pot u) x) === (psi v x, dpsi v x, phi (pot v) x, dphi (pot v) x)
     in conjoin
          [ eqAt ((a <> b) <> d) (a <> (b <> d))
          , eqAt (a <> b) (b <> a)
          , eqAt (mempty <> a) a
          , eqAt (scaleAtom c (a <> b)) (scaleAtom c a <> scaleAtom c b)
          ]

-- | The passive-step residual is additive and homogeneous, so the passing atoms form a cone.
prop_gsm_residual_homomorphism :: Property
prop_gsm_residual_homomorphism = forAll genAtom $ \ga -> forAll genAtom $ \gb -> forAll genNonNeg $ \c ->
  forAll genQ $ \s -> forAll genQ $ \s' -> forAll genQ $ \r ->
    let a = mkAtom ga
        b = mkAtom gb
     in conjoin
          [ stepResidual mempty s s' r === 0
          , stepResidual (a <> b) s s' r === stepResidual a s s' r + stepResidual b s s' r
          , stepResidual (scaleAtom c a) s s' r === c * stepResidual a s s' r
          ]

-- | Composition law: the non-negative combination of the atoms that pass a step passes it, its dissipation is the
-- sum of theirs, and the runtime second law admits the composite step.
prop_gsm_combination_admissible :: Property
prop_gsm_combination_admissible = forAll (listOf ((,) <$> genNonNeg <*> genAtom)) $ \cas ->
  forAll genQ $ \s -> forAll genQ $ \s' -> forAll genQ $ \r ->
    let passing = [scaleAtom c (mkAtom g) | (c, g) <- cas, passiveStep (mkAtom g) s s' r]
        comp = atomSum passing
     in classify (length passing >= 2) "two or more passing atoms" $ conjoin
          [ property (passiveStep comp s s' r)
          , power (pot comp) r === sum [power (pot a) r | a <- passing]
          , property (P.secondLaw P.Transition (P.Thermodynamic (st (psi comp s)) (st (psi comp s'))))
          ]

-- | Convex glue keeps admissibility: its dissipation is non-negative, the glue fraction lies in [0, 1], and a step
-- whose residual includes the glue passes with the glue atom and is admitted by the runtime second law.
prop_gsm_convex_glue_admissible :: Property
prop_gsm_convex_glue_admissible = forAll genAtom $ \ga -> forAll genPotential $ \(a, b) ->
  forAll genQ $ \s -> forAll genQ $ \s' -> forAll genQ $ \r ->
    let atom = mkAtom ga
        g = quadAbsPotential a b
        comp = atom <> glueAtom g
        dA = power (pot atom) r
        dG = power g r
        f = glueFraction dA dG
     in conjoin
          [ property (dG >= 0)
          , property (0 <= f && f <= 1)
          , power (pot comp) r === dA + dG
          , classify (passiveStep comp s s' r) "passing composite step" $
              not (passiveStep comp s s' r)
                || P.secondLaw P.Transition (P.Thermodynamic (st (psi comp s)) (st (psi comp s')))
          ]

-- | An arbitrary glue term needs its own witness: a negative total under the passive equality balance raises the
-- free energy, and the runtime second law refuses the step.
prop_gsm_negative_glue_refused :: Property
prop_gsm_negative_glue_refused = forAll genNonNeg $ \dA -> forAll genNonNeg $ \excess -> forAll genQ $ \psi0 ->
  let dG = negate dA - excess - 1 / 100
      dTotal = dA + dG
      psi1 = psi0 - dTotal
   in counterexample (show (dA, dG, dTotal)) $
        not (P.secondLaw P.Transition (P.Thermodynamic (st psi0) (st psi1)))

-- | A glue fraction above one signals a negative glue term (with non-negative atom dissipation).
prop_gsm_glue_fraction_gt_one_negative :: Property
prop_gsm_glue_fraction_gt_one_negative = forAll genNonNeg $ \dA ->
  forAll (oneof [genQ, (\t -> negate (t * dA)) <$> genUnitish]) $ \dG ->
    classify (glueFraction dA dG > 1) "fraction above one" $ glueFraction dA dG <= 1 || dG < 0

-- | A rational in [0, 3/2]: a glue term up to one and a half times the atoms' dissipation.
genUnitish :: Gen Rational
genUnitish = (\n -> fromIntegral n / 100) <$> choose (0 :: Integer, 150)

-- | The properties with their names, for the runner.
gsmMonoidProps :: [(String, Property)]
gsmMonoidProps =
  [ ("gsm_support_closed", prop_gsm_support_closed)
  , ("gsm_power_nonneg", prop_gsm_power_nonneg)
  , ("gsm_power_homomorphism", prop_gsm_power_homomorphism)
  , ("gsm_potential_monoid_laws", prop_gsm_potential_monoid_laws)
  , ("gsm_atom_monoid_laws", prop_gsm_atom_monoid_laws)
  , ("gsm_residual_homomorphism", prop_gsm_residual_homomorphism)
  , ("gsm_combination_admissible", prop_gsm_combination_admissible)
  , ("gsm_convex_glue_admissible", prop_gsm_convex_glue_admissible)
  , ("gsm_negative_glue_refused", prop_gsm_negative_glue_refused)
  , ("gsm_glue_fraction_gt_one_negative", prop_gsm_glue_fraction_gt_one_negative)
  ]
