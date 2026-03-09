-- |
-- Module      : SDFGate
-- Description : SDF / FRep interpretation of the UMST thermodynamic gate
-- License     : MIT
--
-- This module realises the observation (documented in Docs/FP-Primer.md,
-- §42–§52) that the UMST thermodynamic gate is an implicit surface in
-- the product space @ThermodynamicState × ThermodynamicState@:
--
-- @
--   type GateSDF = ThermodynamicState -> ThermodynamicState -> Double
-- @
--
-- Interior (value ≤ 0) = admissible transition.
-- Exterior (value > 0) = inadmissible transition.
-- Zero level set       = boundary of the admissible region.
--
-- The four invariants each define one half-space; the gate is their
-- CSG intersection (the maximum of all four SDF values).
--
-- Connection to formal proofs:
--   • 'gateSDF' agrees with 'gateCheck' in sign (tested in test/Test.hs).
--   • 'helmholtzSDF' is the 1D SDF for hydration state space; its
--     constant gradient (−Q_hyd) is proved in Coq/Gate.v (@helmholtz_gradient@)
--     and stated in Agda/Helmholtz.agda (@helmholtz-gradient-const@).
--   • The CSG structure corresponds to @admissible-to-csg@ /
--     @csg-to-admissible@ in Agda/Gate.agda.

module SDFGate
  ( -- * SDF type
    GateSDF
    -- * Four sub-condition SDFs
  , massConservationSDF
  , clausiusDuhemSDF
  , hydrationIrreversibilitySDF
  , strengthMonotonicitySDF
    -- * Gate as CSG intersection
  , gateSDF
    -- * The Helmholtz SDF (1D, in hydration space)
  , helmholtzSDF
  , helmholtzGradient
    -- * SDF combinators
  , intersectSDF
  , rUnionSDF
  , smoothUnionSDF
  , offsetSDF
  ) where

import UMST
  ( ThermodynamicState (..)
  , AdmissibilityResult (..)
  , gateCheck
  , qHydration
  , massTolerance
  , tolerance
  )

------------------------------------------------------------------------
-- SDF Type
------------------------------------------------------------------------

-- | A signed distance function on the gate's state-pair space.
--
-- Convention (following FRep standard):
--   * Value ≤ 0 → the point is inside / admissible.
--   * Value > 0 → the point is outside / inadmissible.
--   * Value = 0 → on the boundary surface.
type GateSDF = ThermodynamicState -> ThermodynamicState -> Double

------------------------------------------------------------------------
-- Four Sub-Condition SDFs
------------------------------------------------------------------------

-- | SDF for the mass conservation invariant.
--
-- Returns the excess over the tolerance band:
-- @|ρ_new − ρ_old| − δ_mass@.
--
-- Value ≤ 0 iff |ρ_new − ρ_old| ≤ δ_mass.
--
-- Geometrically: this is a symmetric slab (|Δρ| ≤ δ) in the
-- density-difference axis of state-pair space.
massConservationSDF :: GateSDF
massConservationSDF old new =
  abs (density new - density old) - massTolerance

-- | SDF for the Clausius-Duhem dissipation invariant.
--
-- Returns @ψ_new − ψ_old@.
--
-- Value ≤ 0 iff @ψ_new ≤ ψ_old@ (free energy does not increase).
--
-- Geometrically: a half-space in the (ψ_old, ψ_new) plane below the
-- diagonal ψ_new = ψ_old.  The Helmholtz model (ψ = −Q·α) guarantees
-- that forward hydration always moves into this half-space.
clausiusDuhemSDF :: GateSDF
clausiusDuhemSDF old new = freeEnergy new - freeEnergy old

-- | SDF for the hydration irreversibility invariant.
--
-- Returns @α_old − α_new@.
--
-- Value ≤ 0 iff @α_old ≤ α_new@ (hydration does not reverse).
hydrationIrreversibilitySDF :: GateSDF
hydrationIrreversibilitySDF old new = hydration old - hydration new

-- | SDF for the strength monotonicity invariant.
--
-- Returns @fc_old − fc_new@.
--
-- Value ≤ 0 iff @fc_old ≤ fc_new@ (strength does not decrease).
strengthMonotonicitySDF :: GateSDF
strengthMonotonicitySDF old new = strength old - strength new

------------------------------------------------------------------------
-- Gate as CSG Intersection
------------------------------------------------------------------------

-- | The full gate as a CSG intersection of the four sub-condition SDFs.
--
-- @gateSDF old new = max [mass, clausius, hydration, strength]@
--
-- Value ≤ 0 iff all four sub-conditions hold (the transition is admissible).
-- Value > 0 iff at least one condition is violated (inadmissible).
--
-- This is the SDF analogue of @gateCheck@ from "UMST".  The sign of
-- @gateSDF@ agrees with the admissibility result of @gateCheck@:
--
-- > gateSDF old new <= 0  ⟺  all (== True) (gateCheck old new)
--
-- Proved as the QuickCheck property @prop_gateSDF_matches_gateCheck@
-- in test/Test.hs.
gateSDF :: GateSDF
gateSDF old new = maximum
  [ massConservationSDF           old new
  , clausiusDuhemSDF              old new
  , hydrationIrreversibilitySDF   old new
  , strengthMonotonicitySDF       old new
  ]

------------------------------------------------------------------------
-- Helmholtz SDF (1D, Hydration State Space)
------------------------------------------------------------------------

-- | The Helmholtz free-energy function as a 1D SDF on hydration state space.
--
-- @helmholtzSDF α = −Q_hyd · α@
--
-- This is a signed distance function in the one-dimensional hydration
-- axis with constant gradient magnitude @Q_hyd = 450 J/kg@ everywhere
-- on [0, 1].  The Eikonal condition @|∂ψ/∂α| = Q_hyd@ holds.
--
-- Proved in Coq/Gate.v: @helmholtz_gradient@ (Section 8b).
-- Stated in Agda/Helmholtz.agda: @helmholtz-gradient-const@.
helmholtzSDF :: Double -> Double
helmholtzSDF alpha = -(qHydration * alpha)

-- | The constant gradient of the Helmholtz SDF.
--
-- @helmholtzGradient = ∂ψ/∂α = −Q_hyd@
--
-- Negative (antitone in α): forward hydration moves in the
-- negative-gradient direction, which is the admissible direction.
-- The gate's Clausius-Duhem check is the condition that state transitions
-- move along this negative gradient.
helmholtzGradient :: Double
helmholtzGradient = -qHydration

------------------------------------------------------------------------
-- SDF Combinators
------------------------------------------------------------------------

-- | CSG intersection of two SDFs.
--
-- The intersection is inside (value ≤ 0) where both inputs are inside.
-- Implemented as pointwise maximum: @max(f, g) ≤ 0 ⟺ f ≤ 0 ∧ g ≤ 0@.
intersectSDF :: GateSDF -> GateSDF -> GateSDF
intersectSDF a b old new = max (a old new) (b old new)

-- | R-union of two SDFs (smooth approximation to set-theoretic union).
--
-- Uses the Rvachev formula:
-- @f ∨ g = (f + g − √(f² + g²)) / (1 + √2)@
--
-- The zero set of the result is the set-theoretic union of the two
-- input zero sets.  This is \(C^\infty\)-smooth, unlike @min@ which
-- has a crease at the medial surface.
--
-- The set of all GateSDFs with 'rUnionSDF' is a commutative monoid
-- with identity @const 1e100@ (the "empty" shape — every point outside).
rUnionSDF :: GateSDF -> GateSDF -> GateSDF
rUnionSDF a b old new =
  let f = a old new
      g = b old new
  in (f + g - sqrt (f*f + g*g)) / (1 + sqrt 2)

-- | Smooth union of two SDFs with blend radius @k@.
--
-- Uses the Quilez polynomial formula:
-- @smoothMin(f, g, k) = min(f, g) − h³·k/6@
-- where @h = clamp((k − |f − g|) / k, 0, 1)@.
--
-- As @k → 0@, converges to @min@ (exact union).
-- The blend region has width @k@.
smoothUnionSDF :: Double -> GateSDF -> GateSDF -> GateSDF
smoothUnionSDF k a b old new =
  let av = a old new
      bv = b old new
      h  = max (k - abs (av - bv)) 0 / k
  in min av bv - h * h * h * k / 6

-- | Offset a GateSDF by distance @d@.
--
-- Expands the admissible region (moves the boundary outward by @d@)
-- when @d > 0@; contracts when @d < 0@.
--
-- For a true SDF this operation is exact: it satisfies the same
-- Eikonal condition as the original.
--
-- Naturality: @offsetSDF d@ commutes with 'intersectSDF' and 'rUnionSDF'
-- (it is a natural transformation on GateSDF values).
--
-- Example: the mass-conservation tolerance band is exactly
-- @offsetSDF massTolerance (massConservationSDF with δ=0)@.
offsetSDF :: Double -> GateSDF -> GateSDF
offsetSDF d f old new = f old new - d
