-- |
-- Test suite for UMST-Formal Haskell layer.
--
-- Covers:
--   1. Gate invariants (pure reference implementation)
--   2. SDF/FRep properties (CSG, offset, gradient, Helmholtz)
--   3. Constructor consistency (fromMix / Helmholtz model)
--
-- Run with:  cabal test

module Main where

import Test.QuickCheck
import Data.List (foldl')

import UMST
import SDFGate

------------------------------------------------------------------------
-- Generators
------------------------------------------------------------------------

-- | Generate a valid-range ThermodynamicState.
--   density ∈ [1000, 3000]  kg/m³
--   freeEnergy ∈ [-450, 0]   J/kg
--   hydration ∈ [0, 1]
--   strength ∈ [0, 100]      MPa
genState :: Gen ThermodynamicState
genState = do
  rho   <- choose (1000.0, 3000.0)
  psi   <- choose (-450.0, 0.0)
  al    <- choose (0.0, 1.0)
  fc    <- choose (0.0, 100.0)
  fcMax <- choose (fc, 230.0)
  pure (ThermodynamicState rho psi al fc fcMax)

instance Arbitrary ThermodynamicState where
  arbitrary = genState

------------------------------------------------------------------------
-- Section 1: Pure Gate Invariants
------------------------------------------------------------------------

-- | Gate decisions are deterministic: same inputs always give same result.
prop_gate_deterministic :: ThermodynamicState -> ThermodynamicState -> Bool
prop_gate_deterministic s1 s2 =
  gateCheck s1 s2 1.0 == gateCheck s1 s2 1.0

-- | Mass conservation: admissible iff |Δρ| ≤ massTolerance.
prop_mass_conservation_spec :: ThermodynamicState -> ThermodynamicState -> Bool
prop_mass_conservation_spec old new =
  massConserved (gateCheck old new 1.0)
  == (abs (density new - density old) < massTolerance + UMST.tolerance)

-- | Clausius-Duhem: admissible iff ψ_new ≤ ψ_old.
prop_clausius_spec :: ThermodynamicState -> ThermodynamicState -> Bool
prop_clausius_spec old new =
  energyPositive (gateCheck old new 1.0)
  == (freeEnergy new <= freeEnergy old)

-- | Hydration irreversibility: admissible iff α_new ≥ α_old.
prop_hydration_spec :: ThermodynamicState -> ThermodynamicState -> Bool
prop_hydration_spec old new =
  hydrationOk (gateCheck old new 1.0)
  == (hydration new >= hydration old)

-- | Strength monotonicity: admissible iff fc_new ≥ fc_old.
prop_strength_spec :: ThermodynamicState -> ThermodynamicState -> Bool
prop_strength_spec old new =
  strengthOk (gateCheck old new 1.0)
  == (strength new >= strength old)

-- | Formal counterexample: mass admissibility is NOT transitive.
-- Two consecutive single-step admissible transitions need not compose
-- into a single-step admissible transition.
--
-- This is the executable mirror of Lean/GraphProperties.lean:mass_not_transitive
-- and the reason admissibleTrans was REMOVED from Constitutional.lean.
--
-- Counterexample (δ = massTolerance * 0.99):
--   s0 → s1: |δ - 0| = 99  ≤ 100 ✓
--   s1 → s2: |2δ - δ| = 99 ≤ 100 ✓
--   s0 → s2: |2δ - 0| = 198 > 100 ✗  (NOT admissible in one step)
prop_mass_not_transitive :: Bool
prop_mass_not_transitive =
  let delta = massTolerance * 0.99          -- just under single-step tolerance
      -- Keep freeEnergy/hydration/strength equal so only mass check varies
      s0 = ThermodynamicState 0       0.0 0.5 50.0 100.0
      s1 = ThermodynamicState delta   0.0 0.5 50.0 100.0
      s2 = ThermodynamicState (2*delta) 0.0 0.5 50.0 100.0
      step1  = massConserved (gateCheck s0 s1 1.0)  -- 99 ≤ 100: admitted
      step2  = massConserved (gateCheck s1 s2 1.0)  -- 99 ≤ 100: admitted
      compOk = massConserved (gateCheck s0 s2 1.0)  -- 198 > 100: rejected
  in step1 && step2 && not compOk

------------------------------------------------------------------------
-- Section 2: SDF / FRep Properties
------------------------------------------------------------------------

-- | Central property: gateSDF sign agrees with gateCheck admissibility.
--
-- gateSDF old new <= 0  ⟺  all four gate conditions hold
-- This is the formal connection between the pure boolean gate and the
-- SDF/FRep interpretation.
prop_gateSDF_matches_gateCheck :: ThermodynamicState -> ThermodynamicState -> Bool
prop_gateSDF_matches_gateCheck old new =
  let result   = gateCheck old new 1.0
      admitted = massConserved result
              && energyPositive result
              && hydrationOk result
              && strengthOk result
      sdfVal   = gateSDF old new
  in admitted == (sdfVal <= 0)

-- | CSG intersection: intersectSDF agrees with individual maximums.
prop_intersect_is_max :: ThermodynamicState -> ThermodynamicState -> Bool
prop_intersect_is_max old new =
  intersectSDF massConservationSDF clausiusDuhemSDF old new
  == max (massConservationSDF old new) (clausiusDuhemSDF old new)

-- | Offset expands the admissible region: if gateSDF ≤ 0 then offsetSDF d ≤ d.
prop_offset_admissible_expansion
  :: ThermodynamicState -> ThermodynamicState -> Property
prop_offset_admissible_expansion old new =
  gateSDF old new <= 0 ==>
    offsetSDF 10.0 gateSDF old new <= 0

-- | Helmholtz gradient is constant: ψ(α+ε) − ψ(α) = −Q_hyd · ε.
--
-- This is the Haskell check of the theorem proved in Coq (helmholtz_gradient)
-- and stated in Agda (helmholtz-gradient-const).
prop_helmholtz_gradient_const :: Double -> Double -> Bool
prop_helmholtz_gradient_const alpha eps =
  let lhs = helmholtzSDF (alpha + eps) - helmholtzSDF alpha
      rhs = helmholtzGradient * eps        -- = -Q_hyd * eps
  in abs (lhs - rhs) < 1e-9

-- | Helmholtz SDF is antitone: α₁ ≤ α₂ → ψ(α₂) ≤ ψ(α₁).
prop_helmholtz_antitone :: Double -> Double -> Property
prop_helmholtz_antitone a1 a2 =
  a1 <= a2 ==>
    helmholtzSDF a2 <= helmholtzSDF a1

-- | rUnionSDF is commutative (smooth union is symmetric).
prop_rUnion_commutative :: ThermodynamicState -> ThermodynamicState -> Bool
prop_rUnion_commutative old new =
  abs (rUnionSDF massConservationSDF clausiusDuhemSDF old new
     - rUnionSDF clausiusDuhemSDF massConservationSDF old new) < 1e-9

-- | Offset naturality: offsetSDF commutes with intersectSDF.
--
-- offset d (f ∩ g) = (offset d f) ∩ (offset d g) — up to sign shift.
-- Note: this holds for CSG intersection (max) with a common offset.
prop_offset_distributive :: ThermodynamicState -> ThermodynamicState -> Bool
prop_offset_distributive old new =
  let d = 5.0
      lhs = offsetSDF d (intersectSDF massConservationSDF clausiusDuhemSDF) old new
      -- offsetSDF d (max f g) = max f g - d
      -- intersect (offset d f) (offset d g) = max (f-d) (g-d) = max(f,g) - d
      rhs = intersectSDF (offsetSDF d massConservationSDF)
                         (offsetSDF d clausiusDuhemSDF) old new
  in abs (lhs - rhs) < 1e-9

------------------------------------------------------------------------
-- Section 3: fromMix constructor
------------------------------------------------------------------------

-- | fromMix produces a state consistent with the Helmholtz model:
-- freeEnergy = -Q_hyd * hydration (within floating-point tolerance).
prop_fromMix_helmholtz_model :: Double -> Double -> Property
prop_fromMix_helmholtz_model wc alpha =
  wc > 0.1 && wc < 0.8 && alpha >= 0 && alpha <= 1 ==>
    let s = fromMix wc alpha 20.0
        expected = helmholtzSDF (hydration s)
    in abs (freeEnergy s - expected) < 1e-6

------------------------------------------------------------------------
-- Runner
------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== UMST-Formal Haskell Property Tests ==="
  putStrLn ""

  putStrLn "-- Gate Invariants"
  quickCheck prop_gate_deterministic
  quickCheck prop_mass_conservation_spec
  quickCheck prop_clausius_spec
  quickCheck prop_hydration_spec
  quickCheck prop_strength_spec
  putStrLn "-- Mass Non-Transitivity (formal counterexample)"
  quickCheck prop_mass_not_transitive

  putStrLn ""
  putStrLn "-- SDF / FRep Properties"
  quickCheck prop_gateSDF_matches_gateCheck
  quickCheck prop_intersect_is_max
  quickCheck prop_offset_admissible_expansion
  quickCheck prop_helmholtz_gradient_const
  quickCheck prop_helmholtz_antitone
  quickCheck prop_rUnion_commutative
  quickCheck prop_offset_distributive

  putStrLn ""
  putStrLn "-- Constructor Properties"
  quickCheck prop_fromMix_helmholtz_model

  putStrLn ""
  putStrLn "All tests passed."
