-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
{-# OPTIONS_GHC -Wno-orphans #-}
-- QuickCheck generators for library types live in this test executable; nothing imports it, so
-- the orphan instances cannot meet a second instance.
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
import PropertyRunner (check, finish, newRunner)

import UMST
import SDFGate
import InfoTheory
import LandauerExtension
import qualified MonoidalState
import qualified PrimeSpectralGuidance
import CoordinationContractProps
import qualified UMST.Constants.SI as SI
import qualified UMST.Process as P
import CreditGreedy
import Dignity
import EtaCog
import RhoEstimator
import MedianConvergence
import OrderStatisticsBand
import MeasurementCost (mutualInformationBits, measurementEnergyLowerBound)

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

-- | Strictly positive weights, normalized to sum @1@ (length @n@).
genProbDist :: Int -> Gen [Double]
genProbDist n =
  do
    xs <- vectorOf n (choose (1.0e-3, 1.0))
    let s = sum xs
    pure (map (/ s) xs)

nearList :: Double -> [Double] -> [Double] -> Bool
nearList eps a b =
  length a == length b && and (zipWith (\x y -> abs (x - y) <= eps) a b)

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
-- The pair is built inside the gate (a random pair almost never is): density moves by at most half
-- the mass tolerance, free energy does not rise, hydration and strength do not fall.
prop_offset_admissible_expansion :: Property
prop_offset_admissible_expansion =
  forAll genAdmissibleStep $ \(old, new) ->
    gateSDF old new <= 0 && offsetSDF 10.0 gateSDF old new <= 0

-- | A transition the gate admits.
genAdmissibleStep :: Gen (ThermodynamicState, ThermodynamicState)
genAdmissibleStep = do
  old <- genState
  dRho <- choose (-massTolerance / 2, massTolerance / 2)
  dPsi <- choose (0.0, 50.0)
  al' <- choose (hydration old, 1.0)
  fc' <- choose (strength old, maxStrength old)
  pure (old, old { density = density old + dRho, freeEnergy = freeEnergy old - dPsi
                 , hydration = al', strength = fc' })

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
prop_fromMix_helmholtz_model :: Property
prop_fromMix_helmholtz_model =
  forAll (choose (0.1001, 0.7999)) $ \wc -> forAll (choose (0.0, 1.0)) $ \alpha ->
    let s = fromMix wc alpha 20.0
        expected = helmholtzSDF (hydration s)
    in abs (freeEnergy s - expected) < 1e-6

------------------------------------------------------------------------
-- Section 4: Info theory (mirror of @Lean/InfoTheory.lean@ product laws)
------------------------------------------------------------------------

-- | Product joint masses sum to @1@ when both marginals do.
prop_info_product_joint_sum_one :: Property
prop_info_product_joint_sum_one =
  forAll (choose (1, 6)) $ \na ->
    forAll (choose (1, 6)) $ \nb ->
      forAll (genProbDist na) $ \p ->
        forAll (genProbDist nb) $ \q ->
          let j = productJoint p q
              eps = 1.0e-9
           in abs (jointMassesSum j - 1.0) <= eps

-- | @marginalFirst (productJoint p q) ≈ p@ (Lean @marginalX_product@).
prop_info_marginal_first_product :: Property
prop_info_marginal_first_product =
  forAll (choose (1, 6)) $ \na ->
    forAll (choose (1, 6)) $ \nb ->
      forAll (genProbDist na) $ \p ->
        forAll (genProbDist nb) $ \q ->
          let j = productJoint p q
              eps = 1.0e-9
           in nearList eps (marginalFirst j) p

-- | @marginalSecond (productJoint p q) ≈ q@ (Lean @marginalY_product@).
prop_info_marginal_second_product :: Property
prop_info_marginal_second_product =
  forAll (choose (1, 6)) $ \na ->
    forAll (choose (1, 6)) $ \nb ->
      forAll (genProbDist na) $ \p ->
        forAll (genProbDist nb) $ \q ->
          let j = productJoint p q
              eps = 1.0e-9
           in nearList eps (marginalSecond j) q

------------------------------------------------------------------------
-- Section 5: LandauerExtension
------------------------------------------------------------------------

-- | Energy mono: T1 <= T2 => E(T1) <= E(T2)
prop_landauer_energy_mono :: Property
prop_landauer_energy_mono =
  forAll (choose (0.0, 1000.0)) $ \t1 ->
    forAll (choose (t1, 2000.0)) $ \t2 ->
      landauerEnergyMono t1 t2

-- | N-bit bound scales linearly
prop_landauer_nBit_scales :: Property
prop_landauer_nBit_scales =
  forAll (choose (1, 20 :: Int)) $ \n ->
    forAll (choose (1.0, 1000.0)) $ \t ->
      let nBit = landauerBound_nBit n t
          oneBit = LandauerExtension.landauerBitEnergy t
      in abs (nBit - fromIntegral n * oneBit) < 1e-30

-- | 300K positivity
prop_landauer_300K_pos :: Bool
prop_landauer_300K_pos = landauerEnergy_300K_pos

------------------------------------------------------------------------
-- Section 6: MonoidalState
------------------------------------------------------------------------

genMonoidalState :: Gen MonoidalState.ThermodynamicState
genMonoidalState = do
  rho <- choose (1000.0, 3000.0)
  psi <- choose (-450.0, 0.0)
  al  <- choose (0.0, 1.0)
  fc  <- choose (0.0, 100.0)
  pure (MonoidalState.TS rho psi al fc)

-- | combine 1 s1 s2 ≈ s1
prop_combine_one :: Property
prop_combine_one =
  forAll genMonoidalState $ \s1 ->
    forAll genMonoidalState $ \s2 ->
      MonoidalState.combine_one_check s1 s2

-- | combine 0 s1 s2 ≈ s2
prop_combine_zero :: Property
prop_combine_zero =
  forAll genMonoidalState $ \s1 ->
    forAll genMonoidalState $ \s2 ->
      MonoidalState.combine_zero_check s1 s2

-- | Combined density is between the two inputs
prop_combine_density_interp :: Property
prop_combine_density_interp =
  forAll (choose (0.0, 1.0)) $ \w ->
    forAll genMonoidalState $ \s1 ->
      forAll genMonoidalState $ \s2 ->
        MonoidalState.combine_density_between w s1 s2

-- | Free energy of combination does not exceed max of inputs
prop_combine_freeEnergy_convex :: Property
prop_combine_freeEnergy_convex =
  forAll (choose (0.0, 1.0)) $ \w ->
    forAll genMonoidalState $ \s1 ->
      forAll genMonoidalState $ \s2 ->
        MonoidalState.combine_freeEnergy_le w s1 s2

------------------------------------------------------------------------
-- Section 6b: PrimeSpectralGuidance
------------------------------------------------------------------------

genChannel :: Int -> Gen PrimeSpectralGuidance.MultiplicativeChannel
genChannel n = do
  vals <- vectorOf n (choose (-10.0, 10.0))
  pure (PrimeSpectralGuidance.MC vals)

genWeights :: Int -> Gen [Double]
genWeights n = vectorOf n (choose (0.5, 1.5))

-- | Identity spectral filter preserves channel values.
prop_spectralFilter_id :: Property
prop_spectralFilter_id =
  forAll (choose (1, 12)) $ \n ->
    forAll (genChannel n) $ \mc ->
      PrimeSpectralGuidance.spectralFilter_id_check mc

-- | Perturbation identity at each index.
prop_spectralFilter_perturb :: Property
prop_spectralFilter_perturb =
  forAll (choose (1, 12)) $ \n ->
    forAll (genChannel n) $ \mc ->
      forAll (genWeights n) $ \ws ->
        PrimeSpectralGuidance.spectralFilter_perturb_check ws mc

-- | mangoldtWeightedSum is additive on padded vectors.
prop_mangoldtWeightedSum_add :: Property
prop_mangoldtWeightedSum_add =
  forAll (choose (1, 12)) $ \n ->
    forAll (vectorOf n (choose (-5.0, 5.0))) $ \f ->
      forAll (vectorOf n (choose (-5.0, 5.0))) $ \g ->
        PrimeSpectralGuidance.mangoldtWeightedSum_add_check f g

------------------------------------------------------------------------
-- Section 7: MeasurementCost
------------------------------------------------------------------------

-- | MI of a uniform 2x2 joint is zero (independent uniform)
prop_mc_uniform_joint_zero_mi :: Bool
prop_mc_uniform_joint_zero_mi =
  let joint = [[0.25, 0.25], [0.25, 0.25]]
  in abs (mutualInformationBits joint) < 1e-9

-- | Energy lower bound is nonneg for T > 0
prop_mc_energy_nonneg :: Property
prop_mc_energy_nonneg =
  forAll (choose (1.0, 1000.0)) $ \t ->
    forAll (genProbDist 2) $ \p ->
      forAll (genProbDist 2) $ \q ->
        let joint = productJoint p q
        in measurementEnergyLowerBound t joint >= 0 - 1e-15

------------------------------------------------------------------------
-- Burden / exploration (Lean @BurdenRecursionIsAdmissible@ / @StochasticBurdenExpectation@)
------------------------------------------------------------------------

burdenState :: Double -> ThermodynamicState
burdenState b = ThermodynamicState b 0 0 0 intrinsicStrength

-- | Symmetric two-point noise: expectation factor is @1 + μ@ (Lean @burden_expectation_symmetric_two_point@).
prop_burden_symmetric_expectation :: Double -> Double -> Double -> Bool
prop_burden_symmetric_expectation b mu sig =
  let lhs = 0.5 * (b * (1 + mu + sig)) + 0.5 * (b * (1 + mu - sig))
      rhs = b * (1 + mu)
  in abs (lhs - rhs) <= 1e-12

-- | Schematic burden step admissible when @|g - ε| ≤ massTolerance@ (density channel only).
prop_burden_recursion_admissible :: Double -> Double -> Double -> Property
prop_burden_recursion_admissible b g e =
  abs (g - e) <= massTolerance ==>
    accepted (gateCheck (burdenState b) (burdenState (b + g - e)) 1.0)

-- | Geometric factor @(1+μ)^n@ shrinks when @0 ≤ 1+μ < 1@ (fixed @μ = -0.4@, @n = 60@).
prop_burden_geom_decay :: Bool
prop_burden_geom_decay =
  let mu = -0.4 :: Double
      r = 1 + mu
      v = r ^ (60 :: Int)
  in v >= 0 && v < 1e-3

------------------------------------------------------------------------
-- Economic layer (Lean @Economic.HorizonAwareGrounding@ / @NPVIsSpecialCaseOfThermodynamicBurden@)
------------------------------------------------------------------------

-- | Horizon convex combo lies between endpoints when @α ∈ [0,1]@.
prop_econ_horizon_in_min_max :: Double -> Double -> Double -> Property
prop_econ_horizon_in_min_max alpha cL cG =
  alpha >= 0 && alpha <= 1 ==>
    let hc = alpha * cL + (1 - alpha) * cG
        lo = min cL cG
        hi = max cL cG
    in hc >= lo - 1e-12 && hc <= hi + 1e-12

-- | @B + n g@ iteration without entropy tax (Lean @npv_as_burden_iterate_no_entropy@), small @n@.
prop_econ_npv_iterate :: Double -> Double -> Int -> Property
prop_econ_npv_iterate b g n =
  n >= 0 && n <= 50 ==>
    let go k x
          | k <= 0 = x
          | otherwise = go (k - 1) (x + g)
    in abs (go n b - (b + fromIntegral n * g)) <= 1e-9

-- | Creativity slack monotone in @Δ@ (Lean @creativityBudget_monotoneΔ@).
prop_econ_creativity_monotone :: Double -> Double -> Double -> Double -> Property
prop_econ_creativity_monotone q qa d1 d2 =
  d1 <= d2 && q <= qa + d1 ==>
    q <= qa + d2 + 1e-12

-- | Sum of nonnegative parts is nonnegative (Lean @cost_split_nonneg_of_nonneg@).
prop_econ_cost_split_nonneg :: Double -> Double -> Property
prop_econ_cost_split_nonneg qp qw =
  qp >= 0 && qw >= 0 ==>
    qp + qw >= 0 - 1e-15

------------------------------------------------------------------------
-- Runner
------------------------------------------------------------------------

-- The one second law (UMST.Process): entropy values, Landauer bound, tight witness, refusal, sequence, SI bound.
prop_process_entropies :: Property
prop_process_entropies = once $
  P.shannon2 P.dirac0 == 0 && abs (P.shannon2 P.uniform2 - log 2) < 1e-15

prop_process_landauer_bound :: Positive Double -> Double -> Property
prop_process_landauer_bound (Positive t) w =
  P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) w)) (P.Erasure P.uniform2) ==> t * log 2 <= w * (1 + 1e-12) + 1e-300

prop_process_tight :: Positive Double -> Property
prop_process_tight (Positive t) =
  let e = P.landauerTightErasure (P.HeatBath t)
   in property $ abs (P.work e / t - log 2) <= 1e-12 * log 2

prop_process_refuses_wrong_prior :: Double -> Double -> Property
prop_process_refuses_wrong_prior w mi =
  property $ not (P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath 300) w)) (P.Feedback mi))

prop_process_sequential :: Positive Double -> Double -> Double -> Property
prop_process_sequential (Positive t) w1 w2 =
  let law w = P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) w)) (P.Erasure P.uniform2)
   in (law w1 && law w2) ==> 2 * log 2 <= (w1 + w2) / t + 1e-12

prop_process_si_bound :: Positive Double -> Double -> Property
prop_process_si_bound (Positive t) w =
  P.eraseSecondLawSI t (log 2) w ==> P.kB * t * log 2 <= w * (1 + 1e-12) + 1e-300

main :: IO ()
main = do
  r <- newRunner
  putStrLn "=== UMST-Formal Haskell Property Tests ==="
  putStrLn ""

  putStrLn "-- Gate Invariants"
  check r prop_gate_deterministic
  check r prop_mass_conservation_spec
  check r prop_clausius_spec
  check r prop_hydration_spec
  check r prop_strength_spec
  putStrLn "-- Mass Non-Transitivity (formal counterexample)"
  check r prop_mass_not_transitive

  putStrLn ""
  putStrLn "-- SDF / FRep Properties"
  check r prop_gateSDF_matches_gateCheck
  check r prop_intersect_is_max
  check r prop_offset_admissible_expansion
  check r prop_helmholtz_gradient_const
  check r prop_helmholtz_antitone
  check r prop_rUnion_commutative
  check r prop_offset_distributive

  putStrLn ""
  putStrLn "-- Constructor Properties"
  check r prop_fromMix_helmholtz_model

  putStrLn ""
  putStrLn "-- InfoTheory (product joint / marginals)"
  check r prop_info_product_joint_sum_one
  check r prop_info_marginal_first_product
  check r prop_info_marginal_second_product

  putStrLn ""
  putStrLn "-- LandauerExtension"
  check r prop_landauer_energy_mono
  check r prop_landauer_nBit_scales
  check r prop_landauer_300K_pos

  putStrLn ""
  putStrLn "-- MonoidalState"
  check r prop_combine_one
  check r prop_combine_zero
  check r prop_combine_density_interp
  check r prop_combine_freeEnergy_convex

  putStrLn ""
  putStrLn "-- PrimeSpectralGuidance"
  check r prop_spectralFilter_id
  check r prop_spectralFilter_perturb
  check r prop_mangoldtWeightedSum_add

  putStrLn ""
  putStrLn "-- MeasurementCost"
  check r prop_mc_uniform_joint_zero_mi
  check r prop_mc_energy_nonneg

  putStrLn ""
  putStrLn "-- Burden / stochastic exploration"
  check r prop_burden_symmetric_expectation
  check r prop_burden_recursion_admissible
  check r prop_burden_geom_decay

  putStrLn ""
  putStrLn "-- Economic layer (Wave 6.5.2)"
  check r prop_econ_horizon_in_min_max
  check r prop_econ_npv_iterate
  check r prop_econ_creativity_monotone
  check r prop_econ_cost_split_nonneg

  putStrLn ""
  putStrLn "-- CreditGreedyOptimal (Phase M4)"
  check r prop_credit_greedy_optimal
  check r prop_credit_mass_nonneg
  check r prop_credit_mass_append

  putStrLn ""
  putStrLn "-- Dignity (Phase N3-FPD-a)"
  check r prop_dignity_try_range
  check r prop_dignity_step_honest_non_decreasing
  check r prop_dignity_step_sub_landauer_fixed
  check r prop_dignity_step_monotone_mi
  check r prop_dignity_list_sum_nonneg

  putStrLn ""
  putStrLn "-- EtaCog (Phase N3-FPD-b)"
  check r prop_eta_cog_nonneg
  check r prop_eta_cog_monotone_dignity
  check r prop_eta_cog_monotone_mi
  check r prop_eta_cog_antitone_energy
  check r prop_eta_cog_energy_zero_shape
  check r prop_eta_cog_frozen_dignity_path

  putStrLn ""
  putStrLn "-- RhoEstimator (Phase FPD-RhoEstimator)"
  check r prop_rho_mi_formula_matches_log2
  check r prop_rho_mi_nonneg_interior
  check r prop_rho_mi_monotone_abs_rho
  check r prop_rho_mi_zero_at_zero
  check r prop_rho_mi_bounded_by_rho_max

  putStrLn ""
  putStrLn "-- MedianConvergence (Phase FPD-MedianConvergence)"
  check r prop_n_warmup_monotone_in_epsilon
  check r prop_n_warmup_monotone_in_delta
  check r prop_sqrt_window_matches_engine
  check r prop_n_warmup_positive
  check r prop_bound_inverse_square_epsilon

  putStrLn ""
  putStrLn "-- OrderStatisticsBand (Phase FPD-OrderStatisticsBand)"
  check r prop_quantile_separation_split_sample
  check r prop_n_quantile_monotone_in_epsilon
  check r prop_n_quantile_monotone_in_delta

  putStrLn ""
  putStrLn "-- Constants (exact SI values; derived constants and CODATA cross-checks)"
  mapM_ (\(name, ok) -> check r (once (counterexample name ok))) SI.derivations
  check r prop_process_entropies
  check r prop_process_landauer_bound
  check r prop_process_tight
  check r prop_process_refuses_wrong_prior
  check r prop_process_sequential
  check r prop_process_si_bound

  putStrLn "-- CoordinationContract (Lean, Coq and Agda laws; umst-ucrs runtime model)"
  check r prop_cost_nonneg
  check r prop_cost_additive
  check r prop_admitted_cost_bounded
  check r prop_gatedSync_second_law
  check r prop_clockRun_monotone
  check r prop_honestCredits_append_faulty
  check r prop_wireIter_seq
  check r prop_bestPeer_highest_healthy_credit
  check r prop_failed_sync_drops_credit
  check r prop_gate_rejects_over_budget
  check r prop_cost_monotone_in_bits

  putStrLn ""
  finish r
