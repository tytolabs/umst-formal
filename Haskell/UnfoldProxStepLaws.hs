-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Law L3 on exact rationals; twin of Lean/UnfoldProxStepLaws.lean, Coq/UnfoldProxStepLaws.v and
-- Agda/UnfoldProxStepLaws.agda. A scalar proximal step with the convex quadratic free energy psi x = k/2 (x - c)^2,
-- the convex dissipation potential phi v = eta/2 v^2 and the load f has the exact minimiser
-- x+ = (k c + f + (eta / tau) x0) / (k + eta / tau). test/UnfoldProxStepLawsProps.hs decides the statements on random
-- steps.
module UnfoldProxStepLaws
  ( QuadStep (..)
  , psiQ
  , phiQ
  , incrementalQ
  , proxMinimiser
  ) where

-- | A scalar step: stiffness k > 0, rest state c, viscosity eta > 0, step size tau > 0, load f, start x0.
data QuadStep = QuadStep { qk :: Rational, qc :: Rational, qeta :: Rational, qtau :: Rational, qf :: Rational, qx0 :: Rational }
  deriving (Show)

-- | The free energy psi x = k/2 (x - c)^2.
psiQ :: QuadStep -> Rational -> Rational
psiQ s x = qk s / 2 * (x - qc s) ^ (2 :: Int)

-- | The dissipation potential phi v = eta/2 v^2.
phiQ :: QuadStep -> Rational -> Rational
phiQ s v = qeta s / 2 * v ^ (2 :: Int)

-- | The incremental potential psi x - f x + tau phi ((x - x0) / tau).
incrementalQ :: QuadStep -> Rational -> Rational
incrementalQ s x = psiQ s x - qf s * x + qtau s * phiQ s ((x - qx0 s) / qtau s)

-- | The exact minimiser of the incremental potential.
proxMinimiser :: QuadStep -> Rational
proxMinimiser s = (qk s * qc s + qf s + qeta s / qtau s * qx0 s) / (qk s + qeta s / qtau s)
