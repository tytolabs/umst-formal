-- |
-- Module      : Test
-- Description : QuickCheck property test suite for the UMST gate
-- License     : MIT
--
-- = Purpose
--
-- This test suite verifies two orthogonal things:
--
--   1. __Invariant properties__ — the pure Haskell reference gate in "UMST"
--      satisfies the four physical invariants as theorems, not just as code.
--      These tests are the Haskell-executable shadow of the Agda/Coq proofs.
--
--   2. __Specification consistency__ — for every random input, 'gateCheck'
--      returns exactly the verdict that follows from the four boolean
--      conditions.  This rules out logical bugs (wrong operator, off-by-one
--      tolerance) inside 'gateCheck' itself.
--
-- = Structure
--
-- @
--   prop_theorem1_forward   — forward hydration is always accepted
--   prop_reverse_rejected   — reverse hydration is always rejected
--   prop_mass_violation     — large density jumps are always rejected
--   prop_energy_violation   — spontaneous free-energy increase is rejected
--   prop_identity           — identity transition (old == new) is always accepted
--   prop_dissipation_sign   — D_int ≥ 0 iff the gate accepts the Clausius-Duhem check
--   prop_field_consistency  — accepted ↔ all four sub-fields are True
--   prop_tolerance_boundary — transitions exactly at tolerance are accepted
-- @
--
-- Run with @cabal test@ or directly:
-- @
--   runghc -iHaskell test/Test.hs
-- @

module Main where

import Test.QuickCheck
import System.Exit (exitSuccess, exitFailure)

import UMST

------------------------------------------------------------------------
-- Arbitrary instance for ThermodynamicState
------------------------------------------------------------------------

-- | Generate physically plausible states.
-- Ranges correspond to typical Portland cement paste at 20°C:
--   density      : 1800–2600 kg/m³ (fresh paste to fully hydrated)
--   free_energy  : −450 to 0 J/kg  (ψ = −Q·α, Q = 450, α ∈ [0,1])
--   hydration    : 0–1              (degree of hydration)
--   strength     : 0–80 MPa        (f'c for ordinary structural concrete)
--   max_strength : 80–150 MPa      (always ≥ strength)
instance Arbitrary ThermodynamicState where
  arbitrary = do
    alpha    <- choose (0.0, 1.0)
    wc       <- choose (0.35, 0.60)
    -- derived quantities follow the Powers model used by the kernel
    let rho  = 3150.0 * (1.0 - 0.32 * alpha) + 1000.0 * wc * (1.0 - alpha)
    let psi  = negate 450.0 * alpha
    let x    = 0.68 * alpha / (0.32 * alpha + wc)
    let fc   = 234.0 * x * x * x
    maxStr   <- choose (max fc 1.0, 150.0)
    pure $ ThermodynamicState
      { density    = rho
      , freeEnergy = psi
      , hydration  = alpha
      , strength   = fc
      , maxStrength = maxStr
      }

  shrink s = []

------------------------------------------------------------------------
-- Helper: advance a state by Δα hydration (always forward)
------------------------------------------------------------------------

advanceHydration :: ThermodynamicState -> Double -> ThermodynamicState
advanceHydration old deltaAlpha =
  let alpha2 = min 1.0 (hydration old + abs deltaAlpha)
      wc     = 0.45  -- reference w/c used for shrink tests
      x2     = 0.68 * alpha2 / (0.32 * alpha2 + wc)
  in old
       { hydration  = alpha2
       , freeEnergy = negate 450.0 * alpha2
       , strength   = max (strength old) (234.0 * x2^(3::Int))
       , density    = density old  -- mass is conserved
       }

------------------------------------------------------------------------
-- prop 1: Theorem 1 — forward hydration is always accepted
------------------------------------------------------------------------

-- | Corresponds to Theorem 1 (categorical safety) proved in Agda/Coq.
-- For any state and any positive Δα, the gate must return 'accepted'.
prop_theorem1_forward :: ThermodynamicState -> Positive Double -> Property
prop_theorem1_forward old (Positive da) =
  let new = advanceHydration old da
      dt  = 3600.0  -- 1 hour
      res = gateCheck old new dt
  in counterexample
       (unlines [ "Theorem 1 violated for:"
                , "  old = " ++ show old
                , "  new = " ++ show new
                , "  result = " ++ show res
                ])
     $ accepted res

------------------------------------------------------------------------
-- prop 2: reverse hydration is always rejected
------------------------------------------------------------------------

prop_reverse_rejected :: ThermodynamicState -> Positive Double -> Property
prop_reverse_rejected old (Positive da) =
  -- Only test when old hydration is large enough to reverse
  hydration old > 0.05 ==>
  let new = old { hydration  = hydration old - abs da * 0.1
                , freeEnergy = freeEnergy old + abs da * 45.0  -- ψ increases
                }
      res = gateCheck old new 3600.0
  in counterexample
       (unlines [ "Reverse hydration should be rejected:"
                , "  old.alpha = " ++ show (hydration old)
                , "  new.alpha = " ++ show (hydration new)
                , "  result = " ++ show res
                ])
     $ not (accepted res)

------------------------------------------------------------------------
-- prop 3: mass violation is always rejected
------------------------------------------------------------------------

prop_mass_violation :: ThermodynamicState -> Property
prop_mass_violation old =
  let new = old { density = density old + 200.0 }  -- 200 kg/m³ jump: far outside δ
      res = gateCheck old new 3600.0
  in counterexample
       (unlines [ "Mass violation should be rejected:"
                , "  old.rho = " ++ show (density old)
                , "  new.rho = " ++ show (density new)
                , "  result  = " ++ show res
                ])
     $ not (accepted res)

------------------------------------------------------------------------
-- prop 4: energy violation is always rejected
------------------------------------------------------------------------

-- | Spontaneous increase in free energy violates Clausius-Duhem (D_int < 0).
prop_energy_violation :: ThermodynamicState -> Positive Double -> Property
prop_energy_violation old (Positive bump) =
  let bigBump = bump * 100.0 + 50.0       -- ensure it exceeds tolerance
      new     = old { freeEnergy = freeEnergy old + bigBump }
      res     = gateCheck old new 3600.0
  in counterexample
       (unlines [ "Free-energy increase should be rejected:"
                , "  ΔΨ = " ++ show bigBump
                , "  D_int = " ++ show (dissipation res)
                , "  result = " ++ show res
                ])
     $ not (accepted res)

------------------------------------------------------------------------
-- prop 5: identity transition is always accepted
------------------------------------------------------------------------

prop_identity :: ThermodynamicState -> Property
prop_identity s =
  let res = gateCheck s s 3600.0
  in counterexample ("Identity rejected: " ++ show s)
     $ accepted res

------------------------------------------------------------------------
-- prop 6: dissipation sign matches energyPositive flag
------------------------------------------------------------------------

-- | The 'energyPositive' field must be True iff D_int ≥ −tolerance.
prop_dissipation_sign :: ThermodynamicState -> ThermodynamicState -> Positive Double -> Property
prop_dissipation_sign old new (Positive dt) =
  let res  = gateCheck old new dt
      -- dissipation > −tolerance is exactly the gate's check
      manualOk = dissipation res >= negate tolerance
  in counterexample
       (unlines [ "dissipation flag mismatch:"
                , "  D_int         = " ++ show (dissipation res)
                , "  energyPositive = " ++ show (energyPositive res)
                , "  manual check   = " ++ show manualOk
                ])
     $ energyPositive res == manualOk

------------------------------------------------------------------------
-- prop 7: accepted ↔ all four sub-fields are True
------------------------------------------------------------------------

-- | The overall verdict must be the conjunction of the four sub-checks.
-- This rules out logic bugs (e.g. accepted = True when one sub-check is False).
prop_field_consistency :: ThermodynamicState -> ThermodynamicState -> Positive Double -> Property
prop_field_consistency old new (Positive dt) =
  let res      = gateCheck old new dt
      allTrue  = massConserved res && energyPositive res
              && hydrationOk res   && strengthOk res
  in counterexample
       (unlines [ "accepted ↔ all-sub-checks mismatch:"
                , "  accepted       = " ++ show (accepted res)
                , "  massConserved  = " ++ show (massConserved res)
                , "  energyPositive = " ++ show (energyPositive res)
                , "  hydrationOk    = " ++ show (hydrationOk res)
                , "  strengthOk     = " ++ show (strengthOk res)
                ])
     $ accepted res == allTrue

------------------------------------------------------------------------
-- prop 8: boundary — transition exactly at mass tolerance is accepted
------------------------------------------------------------------------

-- | A density change of exactly massTolerance (100 kg/m³) should be accepted.
-- This validates that the gate uses ≤, not <, at the boundary.
prop_tolerance_boundary :: ThermodynamicState -> Property
prop_tolerance_boundary old =
  -- advance hydration slightly so all other invariants hold
  let new = (advanceHydration old 0.01)
              { density = density old + massTolerance }
      res = gateCheck old new 3600.0
  in counterexample
       (unlines [ "Boundary transition rejected:"
                , "  Δρ = massTolerance = " ++ show massTolerance
                , "  result = " ++ show res
                ])
     $ massConserved res

------------------------------------------------------------------------
-- Main: run all properties
------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "Running UMST gate property tests..."
  let args = stdArgs { maxSuccess = 500, maxShrinks = 100 }

  results <- sequence
    [ quickCheckWithResult args (withMaxSuccess 500 prop_theorem1_forward)
    , quickCheckWithResult args prop_reverse_rejected
    , quickCheckWithResult args prop_mass_violation
    , quickCheckWithResult args prop_energy_violation
    , quickCheckWithResult args prop_identity
    , quickCheckWithResult args (withMaxSuccess 500 prop_dissipation_sign)
    , quickCheckWithResult args (withMaxSuccess 500 prop_field_consistency)
    , quickCheckWithResult args prop_tolerance_boundary
    ]

  let failures = filter (not . isSuccess) results
  if null failures
    then do
      putStrLn "\nAll properties passed."
      exitSuccess
    else do
      putStrLn $ "\n" ++ show (length failures) ++ " property/ies failed."
      exitFailure
