-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.GsmMonoid
-- Description : The composition law of GSM atoms and the glue fraction (twin of Lean/Composition/GsmMonoid.lean,
--               Coq/Composition/GsmMonoid.v and Agda/Composition/GsmMonoid.agda; W-44).
--
-- A GSM potential is carried over exact rationals in supporting-line form: @phi@ with a slope @dphi@ such that
-- phi x + dphi x * (y - x) <= phi y (convexity with a subgradient), phi >= 0 and phi 0 = 0. The dissipation power at
-- rate x is D = x * dphi x. Potentials and atoms (a convex free energy psi with a potential) are monoids under
-- pointwise sum ('<>', 'mempty') and are scaled by non-negative rationals; the power is a monoid homomorphism into
-- the non-negative rationals. Haskell carries no proofs: the QuickCheck properties of test/GsmMonoidProps.hs check
-- the laws the Lean, Coq and Agda twins prove.
module UMST.GsmMonoid
  ( -- * Potentials
    GsmPotential (..)
  , power
  , scalePotential
  , quadAbsPotential
    -- * Atoms
  , GsmAtom (..)
  , scaleAtom
  , quadAtom
  , glueAtom
  , atomSum
    -- * Passive steps
  , stepResidual
  , passiveStep
    -- * Glue
  , glueFraction
  ) where

-- | A GSM dissipation potential in supporting-line form.
data GsmPotential = GsmPotential
  { phi :: Rational -> Rational
  , dphi :: Rational -> Rational
  }

-- | Pointwise sum: the composite's potential.
instance Semigroup GsmPotential where
  GsmPotential f df <> GsmPotential g dg = GsmPotential (\x -> f x + g x) (\x -> df x + dg x)

-- | The null potential.
instance Monoid GsmPotential where
  mempty = GsmPotential (const 0) (const 0)

-- | Dissipation power at rate x: D = x * dphi x.
power :: GsmPotential -> Rational -> Rational
power p x = x * dphi p x

-- | Scaling by c; the caller supplies c >= 0 (a negative c leaves the cone, and the properties refuse it).
scalePotential :: Rational -> GsmPotential -> GsmPotential
scalePotential c (GsmPotential f df) = GsmPotential (\x -> c * f x) (\x -> c * df x)

-- | phi x = a x^2 + b |x| with a, b >= 0 (a viscous arm plus a rate-independent friction arm), with the
-- subgradient 2 a x + b signum x (0 at x = 0 lies in the subdifferential of |x|).
quadAbsPotential :: Rational -> Rational -> GsmPotential
quadAbsPotential a b = GsmPotential (\x -> a * x * x + b * abs x) (\x -> 2 * a * x + b * signum x)

-- | A GSM atom: a free energy psi convex in supporting-line form, with a potential.
data GsmAtom = GsmAtom
  { psi :: Rational -> Rational
  , dpsi :: Rational -> Rational
  , pot :: GsmPotential
  }

instance Semigroup GsmAtom where
  GsmAtom f df p <> GsmAtom g dg q = GsmAtom (\x -> f x + g x) (\x -> df x + dg x) (p <> q)

instance Monoid GsmAtom where
  mempty = GsmAtom (const 0) (const 0) mempty

-- | Scaling an atom by c >= 0.
scaleAtom :: Rational -> GsmAtom -> GsmAtom
scaleAtom c (GsmAtom f df p) = GsmAtom (\x -> c * f x) (\x -> c * df x) (scalePotential c p)

-- | psi s = k (s - s0)^2 / 2 with k >= 0, and the potential a x^2 + b |x|.
quadAtom :: Rational -> Rational -> Rational -> Rational -> GsmAtom
quadAtom k s0 a b = GsmAtom (\s -> k * (s - s0) * (s - s0) / 2) (\s -> k * (s - s0)) (quadAbsPotential a b)

-- | A convex glue term is an atom with zero free energy.
glueAtom :: GsmPotential -> GsmAtom
glueAtom = GsmAtom (const 0) (const 0)

-- | The composite of a list of atoms (each already scaled by its non-negative coefficient).
atomSum :: [GsmAtom] -> GsmAtom
atomSum = mconcat

-- | The passive-balance residual of a step s -> s' at rate r: (psi s' - psi s) + D.
stepResidual :: GsmAtom -> Rational -> Rational -> Rational -> Rational
stepResidual a s s' r = (psi a s' - psi a s) + power (pot a) r

-- | A passive step: residual <= 0.
passiveStep :: GsmAtom -> Rational -> Rational -> Rational -> Bool
passiveStep a s s' r = stepResidual a s s' r <= 0

-- | Glue fraction |D_glue| / D_total with D_total = D_atoms + D_glue; 0 when D_total = 0 (the Lean convention).
glueFraction :: Rational -> Rational -> Rational
glueFraction dAtoms dGlue
  | total == 0 = 0
  | otherwise = abs dGlue / total
  where
    total = dAtoms + dGlue
