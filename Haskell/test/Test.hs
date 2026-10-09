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
import qualified UMST.Constants.Bounds as Bounds
import qualified UMST.Process as P
import qualified UMST.Chem.SecondLaw as CS
import qualified UMST.Excitement as X
import qualified UMST.OneInequality as O
import qualified UMST.CoarseGraining as CG
import qualified UMST.Semantic as SM
import qualified UMST.CostOfInformation as CI
import qualified UMST.Chem.Kleisli as K
import qualified UMST.UrgeAdmitKleisli as UA
import qualified UMST.UrgeProvenancePreserve as UP
import CreditGreedy
import Dignity
import EtaCog
import RhoEstimator
import MedianConvergence
import OrderStatisticsBand
import MeasurementCost (mutualInformationBits, measurementEnergyLowerBound)
import SecondLawBoundsProps
import SecondLawConstantsProps
import SecondLawSolidInelasticProps
import SecondLawPoroContinuumProps
import ConstantsBoundsProps (boundProperties)
import PhiGrammarProps
import GsmMonoidProps (gsmMonoidProps)
import PowersCapillaryProps (powersCapillaryProps)
import ChemProcessFunctorProps (chemProcessFunctorProps)
import FluctuationProps (fluctuationProps)

------------------------------------------------------------------------
-- Generators
------------------------------------------------------------------------

-- | Generate a valid-range ThermodynamicState.
--   density ∈ [1000, 3000]  kg/m³
--   freeEnergy ∈ [-Q_hyd, 0]  J/g (Q_hyd the table's default)
--   hydration ∈ [0, 1]
--   strength ∈ [0, 100]      MPa
genState :: Gen ThermodynamicState
genState = do
  rho   <- choose (1000.0, 3000.0)
  psi   <- choose (negate qHydration, 0.0)
  al    <- choose (0.0, 1.0)
  fc    <- choose (0.0, 100.0)
  fcMax <- choose (fc, intrinsicStrength)
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

-- The gate admits a step within its tolerance of each order law (UMST.tolerance); outside that band it agrees with
-- the exact law (Lean ConcreteAdmissible): a step obeying the law passes, a step breaking it by more than the band
-- fails.

-- | Clausius-Duhem: ψ_new ≤ ψ_old passes; ψ rising beyond the band fails.
prop_clausius_spec :: ThermodynamicState -> ThermodynamicState -> Bool
prop_clausius_spec old new =
  let ok = energyPositive (gateCheck old new 1.0)
   in (freeEnergy new <= freeEnergy old) <= ok && (freeEnergy new - freeEnergy old > UMST.tolerance) <= not ok

-- | Hydration irreversibility: α_new ≥ α_old passes; α falling beyond the band fails.
prop_hydration_spec :: ThermodynamicState -> ThermodynamicState -> Bool
prop_hydration_spec old new =
  let ok = hydrationOk (gateCheck old new 1.0)
   in (hydration new >= hydration old) <= ok && (hydration old - hydration new > UMST.tolerance) <= not ok

-- | Strength monotonicity: fc_new ≥ fc_old passes; fc falling beyond the band fails.
prop_strength_spec :: ThermodynamicState -> ThermodynamicState -> Bool
prop_strength_spec old new =
  let ok = strengthOk (gateCheck old new 1.0)
   in (strength new >= strength old) <= ok && (strength old - strength new > UMST.tolerance) <= not ok

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
-- Rounding error grows with the size of the terms, so the tolerance is relative to them.
prop_burden_symmetric_expectation :: Double -> Double -> Double -> Bool
prop_burden_symmetric_expectation b mu sig =
  let lhs = 0.5 * (b * (1 + mu + sig)) + 0.5 * (b * (1 + mu - sig))
      rhs = b * (1 + mu)
      magnitude = abs b * (1 + abs mu + abs sig)
  in abs (lhs - rhs) <= 1e-12 * max 1 magnitude

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
        tol = 1e-12 * max 1 (abs cL + abs cG)
    in hc >= lo - tol && hc <= hi + tol

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
-- Urge history moves on the one second law (UMST.UrgeAdmitKleisli, UMST.UrgeProvenancePreserve)
------------------------------------------------------------------------

-- A history move whose head move passes the gate (the identity step or a small step) and whose erasure dissipates
-- between half and twice the Landauer floor of the erased distribution, so both verdicts occur often.
genTransition :: Gen UA.HistoryTransition
genTransition = do
  old <- genState
  new <- oneof [pure old, genStepFrom old]
  c0 <- choose (0, 50)
  c1 <- choose (0, 50)
  temp <- choose (1, 1000)
  p <- choose (0, 1)
  factor <- choose (0.5, 2)
  let erased = P.ProbDist2 p
      e = P.ErasureProcess (P.HeatBath temp) (factor * temp * P.shannon2 erased)
  maybe discard pure (UA.mkHistoryTransition (UA.HistorySnapshot c0 old) (UA.HistorySnapshot c1 new) e erased)

-- Admissibility is the Clausius bound of the erasure (twin of admissibleHistoryTransition_iff).
prop_urge_admit_clausius :: Property
prop_urge_admit_clausius = forAll genTransition $ \t ->
  let e = UA.erasureProcess t
      adm = UA.admissibleHistoryTransition t
   in cover 20 adm "admissible" $ cover 20 (not adm) "refused" $
        adm === (P.shannon2 (UA.erasedDist t) <= P.work e / P.bathTemp (P.erasureBath e))

-- Head moves are Kleisli arrows over thermodynamic states: the identity, a shift, a gate-checked shift, a shift
-- below a density cutoff, and the arrow that always refuses.
genArrow :: Gen K.KleisliArrow
genArrow = do
  dRho <- choose (-150, 150)
  dAl <- choose (-0.02, 0.1)
  cutoff <- choose (1000, 3000)
  let shift (ThermodynamicState rho psi al fc fcMax) = ThermodynamicState (rho + dRho) psi (al + dAl) fc fcMax
  frequency
    [ (3, pure UA.admitIdentity)
    , (4, pure (Just . shift))
    , (2, pure (K.makeGateArrow shift))
    , (2, pure (\s -> if density s < cutoff then Just (shift s) else Nothing))
    , (1, pure (const Nothing))
    ]

forAllArrow :: Testable p => (K.KleisliArrow -> p) -> Property
forAllArrow = forAllShow genArrow (const "<arrow>")

prop_urge_kleisli_assoc :: Property
prop_urge_kleisli_assoc = forAllArrow $ \f -> forAllArrow $ \g -> forAllArrow $ \h -> forAll genState $ \s ->
  let r = K.kleisliCompose (K.kleisliCompose f g) h s
   in cover 25 (r /= Nothing) "composite succeeds" $ r === K.kleisliCompose f (K.kleisliCompose g h) s

prop_urge_kleisli_left_unit :: Property
prop_urge_kleisli_left_unit = forAllArrow $ \f -> forAll genState $ \s ->
  cover 40 (f s /= Nothing) "arrow succeeds" $ K.kleisliCompose UA.admitIdentity f s === f s

prop_urge_kleisli_right_unit :: Property
prop_urge_kleisli_right_unit = forAllArrow $ \f -> forAll genState $ \s ->
  cover 40 (f s /= Nothing) "arrow succeeds" $ K.kleisliCompose f UA.admitIdentity s === f s

-- Provenance aligned to a move's prior commit, with a random stamp chain and witness.
genProvenanceAt :: Int -> Gen UP.Provenance
genProvenanceAt c = UP.Provenance <$> listOf (choose (0, 50)) <*> pure c <*> frequency [(7, pure True), (3, pure False)]

-- A candidate post provenance: the one the move produces, the same without its witness, or an arbitrary one.
genPost :: UA.HistoryTransition -> UP.Provenance -> Gen UP.Provenance
genPost t prior = frequency
  [ (5, pure (UP.postProvenance t prior))
  , (2, pure (UP.postProvenance t prior) { UP.landauerWitness = False })
  , (1, UP.Provenance <$> listOf (choose (0, 50)) <*> choose (0, 50) <*> arbitrary)
  ]

prop_urge_preserves_chain_append :: Property
prop_urge_preserves_chain_append = forAll genTransition $ \t ->
  forAll (genProvenanceAt (UA.commitId (UA.priorSnapshot t))) $ \prior -> forAll (genPost t prior) $ \post ->
    UP.preserves t prior post ==> UP.ucrsChain post === UP.ucrsChain prior ++ [UP.dagCommit prior]

prop_urge_preserves_witness_retained :: Property
prop_urge_preserves_witness_retained = forAll genTransition $ \t ->
  forAll (genProvenanceAt (UA.commitId (UA.priorSnapshot t))) $ \prior -> forAll (genPost t prior) $ \post ->
    UP.preserves t prior post && UP.landauerWitness prior ==> UP.landauerWitness post

prop_urge_post_provenance_preserves :: Property
prop_urge_post_provenance_preserves = forAll genTransition $ \t ->
  forAll (oneof [pure (UA.commitId (UA.priorSnapshot t)), choose (0, 50)]) $ \c ->
  forAll (genProvenanceAt c) $ \prior ->
    UP.dagCommit prior == UA.commitId (UA.priorSnapshot t) && UA.admissibleHistoryTransition t
      ==> UP.preserves t prior (UP.postProvenance t prior)

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


prop_process_si_bound :: Positive Double -> Double -> Property
prop_process_si_bound (Positive t) w =
  P.eraseSecondLawSI t (log 2) w ==> P.kB * t * log 2 <= w * (1 + 1e-12) + 1e-300

-- The Landauer bounds for every entropy drop (twins of Agda landauerBound and landauerBoundSI, whose erasure prior
-- carries the entropy it removes): an erasure of an n-state prior to a point mass that obeys the law dissipates at
-- least T times the entropy removed, and k_B T times it in joules. Work is drawn on both sides of that floor.
prop_process_landauer_bound_any_drop :: Positive Double -> Property
prop_process_landauer_bound_any_drop (Positive t) = forAll (choose (1, 8)) $ \n -> forAll (genDist n) $ \p ->
  forAll (choose (0, 2)) $ \k ->
    let point = P.ProbDist (1 : replicate (n - 1) 0)
        dS = P.shannon p - P.shannon point
        w = k * t * dS
     in P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) w)) (P.Transformation p point)
          ==> t * dS <= w * (1 + 1e-12) + 1e-300

prop_process_si_bound_any_drop :: Positive Double -> Property
prop_process_si_bound_any_drop (Positive t) = forAll (choose (0, 3)) $ \dS -> forAll (choose (0, 2)) $ \k ->
  let w = k * P.kB * t * dS
   in P.eraseSecondLawSI t dS w ==> P.kB * t * dS <= w * (1 + 1e-12) + 1e-300

-- n-state transformations (UMST.Process): the binary case, identity and composition.
genDist :: Int -> Gen P.ProbDist
genDist n = do
  xs <- vectorOf n (choose (0, 1 :: Double)) `suchThat` (\ys -> sum ys > 1e-6)
  pure (P.ProbDist (map (/ sum xs) xs))

prop_process_binary_is_transformation :: Property
prop_process_binary_is_transformation = forAll (choose (0, 1)) $ \p ->
  abs (P.shannon (P.asProbDist (P.ProbDist2 p)) - P.shannon2 (P.ProbDist2 p)) < 1e-12

prop_process_transformation_id :: Positive Double -> Property
prop_process_transformation_id (Positive t) = forAll (choose (1, 8)) $ \n -> forAll (genDist n) $ \p ->
  P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) 0)) (P.Transformation p p)

prop_process_transformation_comp :: Positive Double -> Property
prop_process_transformation_comp (Positive t) = forAll (choose (1, 8)) $ \n ->
  forAll (genDist n) $ \p -> forAll (genDist n) $ \q -> forAll (genDist n) $ \r ->
    let w1 = t * (P.shannon p - P.shannon q) + 1e-9
        w2 = t * (P.shannon q - P.shannon r) + 1e-9
        law w a b = P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) w)) (P.Transformation a b)
     in (law w1 p q && law w2 q r) ==> law (w1 + w2 + 1e-9 * t) p r

-- Selection under cost (twins of select_empty, select_minimal, select_descent, select_perm_invariant and
-- select_secondLaw). Candidates are moves the gate admits from a source, with distinct ids; the joint free energy is
-- the state's free energy, exact.
stateEnergy :: ThermodynamicState -> Rational
stateEnergy = toRational . freeEnergy

genCands :: ThermodynamicState -> Gen [X.Cand ThermodynamicState]
genCands src = do
  n <- choose (0, 8)
  steps <- vectorOf n (suchThat (genStepFrom src) (\s -> accepted (gateCheck src s 1)))
  ledgers <- vectorOf n (fromInteger <$> choose (-20, 20))
  tags <- vectorOf n (frequency [(4, pure True), (1, pure False)])
  ids <- shuffle [0 .. n - 1]
  pure (zipWith4 X.Cand ids steps ledgers tags)
  where zipWith4 f (a : as) (b : bs) (c : cs) (d : ds) = f a b c d : zipWith4 f as bs cs ds
        zipWith4 _ _ _ _ _ = []

prop_select_empty :: ThermodynamicState -> Bool
prop_select_empty src = case X.select stateEnergy src [] of { Right X.NoCandidates -> True; _ -> False }

prop_select_minimal :: Property
prop_select_minimal = forAll genState $ \src -> forAll (genCands src) $ \cands ->
  case X.select stateEnergy src cands of
    Left c -> X.evidenceTagged c && any ((== X.cid c) . X.cid) cands
      && and [X.candEnergy stateEnergy c <= X.candEnergy stateEnergy c' | c' <- cands, X.evidenceTagged c']
    Right _ -> True

prop_select_descent :: Property
prop_select_descent = forAll genState $ \src -> forAll (genCands src) $ \cands ->
  case X.select stateEnergy src cands of
    Left c -> cover 5 True "selected" (X.candEnergy stateEnergy c < stateEnergy src)
    Right _ -> property True

prop_select_perm_invariant :: Property
prop_select_perm_invariant = forAll genState $ \src -> forAll (genCands src) $ \cands -> forAll (shuffle cands) $ \cands' ->
  let key = either (Left . X.cid) Right in key (X.select stateEnergy src cands) == key (X.select stateEnergy src cands')

prop_select_secondLaw :: Property
prop_select_secondLaw = forAll genState $ \src -> forAll (genCands src) $ \cands ->
  case X.select stateEnergy src cands of
    Left c -> P.secondLaw P.Transition (P.Thermodynamic src (X.tgt c))
    Right _ -> True

-- Units bridge: the erase instance at work W (k_B·K) is the SI form at k_B·W joules (twin of
-- SecondLaw_transformation_iff_SI); work sits a relative margin from the bound, where both comparisons agree.
prop_process_units_bridge :: Property
prop_process_units_bridge = forAll (choose (1, 1000)) $ \t -> forAll (choose (1, 8)) $ \n ->
  forAll (genDist n) $ \p -> forAll (genDist n) $ \q -> forAll (elements [-0.5, -1e-3, 1e-3, 0.5]) $ \delta ->
    let d = P.shannon p - P.shannon q
        w = t * d + delta * (abs (t * d) + 1)
     in P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) w)) (P.Transformation p q)
          == P.eraseSecondLawSI t d (P.kB * w)

-- The one inequality dF <= W_in + k_B T I (twins of Lean/OneInequalitySecondLaw.lean). Values sit a relative margin
-- from each bound, where floating-point comparisons agree with the exact law.
genMargin :: Gen Double
genMargin = elements [-0.5, -1e-3, 1e-3, 0.5]

admissibleStep :: P.HeatBath -> Gen O.Step
admissibleStep b = do
  w <- choose (-10, 10)
  i <- choose (0, 3)
  slack <- choose (1e-6, 5)
  let bound = w + P.kB * P.bathTemp b * i
  pure (O.Step b (bound - slack * (abs bound + 1)) w i)

prop_oneineq_chain :: Property
prop_oneineq_chain = forAll (choose (1, 1000)) $ \t -> let b = P.HeatBath t in
  forAll (admissibleStep b) $ \s1 -> forAll (admissibleStep b) $ \s2 -> O.oneInequality (O.chain s1 s2)

prop_oneineq_erase_iff :: Property
prop_oneineq_erase_iff = forAll (choose (1, 1000)) $ \t -> forAll (choose (1, 8)) $ \n ->
  forAll (genDist n) $ \p -> forAll (genDist n) $ \q -> forAll genMargin $ \delta ->
    let d = P.shannon p - P.shannon q
        e = P.ErasureProcess (P.HeatBath t) (t * d + delta * (abs (t * d) + 1))
     in P.secondLaw (P.Erase e) (P.Transformation p q) == O.oneInequality (O.eraseStep e p q)

prop_oneineq_feedback_iff :: Property
prop_oneineq_feedback_iff = forAll (choose (1, 1000)) $ \t -> forAll (choose (-5, 5)) $ \df ->
  forAll (choose (0, 3)) $ \mi -> forAll genMargin $ \delta ->
    let bound = negate df + P.kB * t * mi
        f = P.FeedbackProcess (P.HeatBath t) (bound + delta * (abs bound + 1)) df
     in P.secondLaw (P.MeasureFeedback f) (P.Feedback mi) == O.oneInequality (O.feedbackStep f mi)

-- Off the gate's tolerance band: free energy moves by at least 10^-3, density by at most 50.
prop_oneineq_transition_iff :: Property
prop_oneineq_transition_iff = forAll genState $ \old -> forAll (genStepFrom old) $ \new ->
  abs (freeEnergy new - freeEnergy old) > 1e-3 && abs (density new - density old) < 50 ==>
    P.secondLaw P.Transition (P.Thermodynamic old new) == O.oneInequality (O.transitionStepAt (P.HeatBath 300) old new)

prop_oneineq_transition_erase_chain :: Property
prop_oneineq_transition_erase_chain = forAll genState $ \old -> forAll (genStepFrom old) $ \new ->
  forAll (choose (1, 1000)) $ \t -> forAll (choose (1, 8)) $ \n -> forAll (genDist n) $ \p -> forAll (genDist n) $ \q ->
    let d = P.shannon p - P.shannon q
        e = P.ErasureProcess (P.HeatBath t) (t * d + 1e-3 * (abs (t * d) + 1))
     in (P.secondLaw P.Transition (P.Thermodynamic old new) && freeEnergy new <= freeEnergy old) ==>
          O.oneInequality (O.chain (O.transitionStepAt (P.HeatBath t) old new) (O.eraseStep e p q))

prop_oneineq_secondlaw_implies :: Property
prop_oneineq_secondlaw_implies = forAll (choose (1, 1000)) $ \t -> forAll (choose (1, 8)) $ \n ->
  forAll (genDist n) $ \p -> forAll (genDist n) $ \q ->
    let d = P.shannon p - P.shannon q
        e = P.ErasureProcess (P.HeatBath t) (t * d + 1e-3 * (abs (t * d) + 1))
     in case O.stepOf (P.Erase e) (P.Transformation p q) of
          Just st -> P.secondLaw (P.Erase e) (P.Transformation p q) && O.oneInequality st
          Nothing -> False

prop_oneineq_szilard_chain :: Positive Double -> Bool
prop_oneineq_szilard_chain (Positive t0) =
  let t = 1 + t0
      b = P.HeatBath t
      st = O.chain (O.feedbackStep (P.szilardEngine b) (P.mutualInformation2 P.szilardJoint))
                   (O.eraseStep (P.landauerTightErasure b) (P.asProbDist P.uniform2) (P.asProbDist P.dirac0))
      bound = O.wIn st + P.kB * t * O.infoI st
   in O.deltaF st <= bound + 1e-9 * abs bound

-- Coarse graining (twins of Lean/CoarseGraining.lean). The sharpening map meets the Esposito conditions.
genProb2 :: Gen P.ProbDist2
genProb2 = P.ProbDist2 <$> choose (0, 1)

prop_cg_coarse_from_fine :: Property
prop_cg_coarse_from_fine = forAll (choose (1, 1000)) $ \t -> forAll genProb2 $ \p -> forAll (choose (0, 1)) $ \s ->
  forAll (choose (0, 2)) $ \k ->
    let e = P.Erase (P.ErasureProcess (P.HeatBath t) (k * t))
        cg = CG.sharpenMap s
     in P.secondLaw e (P.Erasure p) ==> P.secondLaw (CG.mapProcess cg e) (CG.mapPrior cg (P.Erasure p))

-- The identity coarse graining preserves every verdict (twin of espositoConditions_id).
prop_cg_id :: Property
prop_cg_id = forAll (choose (1, 1000)) $ \t -> forAll genProb2 $ \p -> forAll (choose (0, 2)) $ \k ->
  let e = P.Erase (P.ErasureProcess (P.HeatBath t) (k * t))
      cg = CG.idCoarseGrainMap
   in P.secondLaw (CG.mapProcess cg e) (CG.mapPrior cg (P.Erasure p)) == P.secondLaw e (P.Erasure p)

prop_cg_refusal_sound :: Property
prop_cg_refusal_sound = forAll (choose (1, 1000)) $ \t -> forAll genProb2 $ \p -> forAll (choose (0, 1)) $ \s ->
  forAll (choose (0, 2)) $ \k ->
    let e = P.Erase (P.ErasureProcess (P.HeatBath t) (k * t))
        cg = CG.sharpenMap s
     in not (P.secondLaw (CG.mapProcess cg e) (CG.mapPrior cg (P.Erasure p))) ==> not (P.secondLaw e (P.Erasure p))

prop_cg_product_entropy :: Property
prop_cg_product_entropy = forAll genProb2 $ \p -> forAll genProb2 $ \q ->
  let h = P.jointEntropy2 (CG.productJoint2 p q)
   in abs (h - (P.shannon2 p + P.shannon2 q)) <= 1e-12 && P.shannon2 p <= h + 1e-12

prop_cg_lump_coarse_from_fine :: Property
prop_cg_lump_coarse_from_fine = forAll (choose (1, 1000)) $ \t -> forAll genProb2 $ \p -> forAll genProb2 $ \q ->
  let w = t * P.jointEntropy2 (CG.productJoint2 p q) * (1 + 1e-9) + 1e-12
   in P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) w)) (P.Erasure p)

-- The semantic second law (twins of Lean/SemanticSecondLaw.lean).
prop_semantic_iff :: Property
prop_semantic_iff = forAll (choose (1, 1000)) $ \t -> forAll (choose (1, 6)) $ \n -> forAll (genDist n) $ \p ->
  forAll (genDist n) $ \q -> forAll (choose (-3, 3)) $ \w -> forAll genProb2 $ \a -> forAll genProb2 $ \b ->
    forAll (elements [0, 1]) $ \defect -> forAll (choose (-0.1, 0.1)) $ \thr ->
      let tr = SM.CommunicativeTransition (P.HeatBath t) p q w defect
          j = CG.productJoint2 a b
       in SM.semanticSecondLaw thr tr j
            == (SM.structurallyConsistent tr && P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) w)) (P.Transformation p q)
                  && SM.miPreserved thr j)

prop_semantic_from_physical :: Property
prop_semantic_from_physical = forAll physicalErasure $ \e ->
  let tr = SM.CommunicativeTransition (P.erasureBath e) (P.asProbDist P.uniform2) (P.asProbDist P.dirac0) (P.work e) 0
   in obeysErase e ==> SM.semanticSecondLaw (-1) tr (CG.productJoint2 P.uniform2 P.uniform2)

prop_semantic_landauer_bound :: Property
prop_semantic_landauer_bound = forAll physicalErasure $ \e ->
  let temp = P.bathTemp (P.erasureBath e)
   in obeysErase e ==> P.work e >= temp * log 2 - 1e-12 * temp

prop_semantic_p0 :: Property
prop_semantic_p0 = once $ SM.modelUncertaintyDrop SM.consistentP0Transition == 0 && SM.structurallyConsistent SM.consistentP0Transition

prop_semantic_product_mi_zero :: Property
prop_semantic_product_mi_zero = forAll genProb2 $ \a -> forAll genProb2 $ \b ->
  abs (P.mutualInformation2 (CG.productJoint2 a b)) <= 1e-12

-- The cost of information (twins of Lean/CostOfInformation.lean).
prop_cost_uniform_entropy :: Property
prop_cost_uniform_entropy = forAll (choose (1, 64)) $ \n ->
  abs (P.shannon (CI.uniformN n) - log (fromIntegral n)) <= 1e-12 * (1 + log (fromIntegral n))

prop_cost_entropy_drop_joules :: Property
prop_cost_entropy_drop_joules = forAll (choose (1, 1000)) $ \t -> forAll (choose (1, 6)) $ \n ->
  forAll (genDist n) $ \p -> forAll (genDist n) $ \q -> forAll (choose (-3, 3)) $ \w ->
    let b = P.HeatBath t
     in P.secondLaw (P.Erase (P.ErasureProcess b w)) (P.Transformation p q)
          ==> CI.entropyDropJoules b p q <= P.kB * w * (1 + 1e-12) + 1e-35

prop_cost_info_per_joule :: Property
prop_cost_info_per_joule = forAll (choose (1, 1000)) $ \t -> forAll (choose (1, 6)) $ \n ->
  forAll (genDist n) $ \p -> forAll (genDist n) $ \q -> forAll (choose (1e-3, 3)) $ \w ->
    let b = P.HeatBath t
     in P.secondLaw (P.Erase (P.ErasureProcess b w)) (P.Transformation p q)
          ==> CI.informationPerJoule w p q <= (1 / (P.kB * t)) * (1 + 1e-9)

prop_cost_bit_erasure :: Property
prop_cost_bit_erasure = forAll (choose (1, 1000)) $ \t -> forAll (choose (0, 6)) $ \bits -> forAll (choose (0, 3000)) $ \w ->
  let b = P.HeatBath t
   in P.secondLaw (P.Erase (P.ErasureProcess b w)) (CI.bitErasure bits)
        ==> fromIntegral bits * landauerJoulesPerBit t <= P.kB * w * (1 + 1e-12) + 1e-35

-- A claim of b bits paid by an erasure obeying the predicate spends honestly, and its score is at most its dignity
-- over the Landauer bit energy.
prop_cost_honest_spend_of_secondLaw :: Property
prop_cost_honest_spend_of_secondLaw = forAll (choose (1, 1000)) $ \t -> forAll (choose (0, 6)) $ \bits ->
  forAll (choose (0, 3000)) $ \w ->
    let b = P.HeatBath t
        mi = fromIntegral bits
        e = P.kB * w * (1 + 1e-12) + 1e-35
     in P.secondLaw (P.Erase (P.ErasureProcess b w)) (CI.bitErasure bits) ==> honestSpend t mi e

prop_cost_eta_cog_le_of_honest :: Property
prop_cost_eta_cog_le_of_honest = forAll (choose (1, 1000)) $ \t -> forAll (choose (0, 10)) $ \d ->
  forAll (choose (0, 64)) $ \mi -> forAll (choose (0, 10)) $ \slack ->
    let e = landauerJoulesPerBit t * (mi + slack)
     in honestSpend t mi e ==> etaCog t d mi e <= d / landauerJoulesPerBit t * (1 + 1e-12)

prop_cost_eta_cog_le_of_secondLaw :: Property
prop_cost_eta_cog_le_of_secondLaw = forAll (choose (1, 1000)) $ \t -> forAll (choose (0, 10)) $ \d ->
  forAll (choose (0, 6)) $ \bits -> forAll (choose (0, 3000)) $ \w ->
    let b = P.HeatBath t
     in P.secondLaw (P.Erase (P.ErasureProcess b w)) (CI.bitErasure bits)
          ==> etaCog t d (fromIntegral bits) (P.kB * w) <= d / landauerJoulesPerBit t * (1 + 1e-9)

-- The Szilard witness (twins of szilardJoint, its marginals, entropy and mutual information, and the engine).
prop_szilard_joint :: Property
prop_szilard_joint = once $
  let j = P.szilardJoint in all (>= 0) [P.j00 j, P.j01 j, P.j10 j, P.j11 j] && P.j00 j + P.j01 j + P.j10 j + P.j11 j == 1

prop_szilard_marginal_x :: Property
prop_szilard_marginal_x = once $ P.p0 (P.marginalX2 P.szilardJoint) == P.p0 P.uniform2

prop_szilard_marginal_y :: Property
prop_szilard_marginal_y = once $ P.p0 (P.marginalY2 P.szilardJoint) == P.p0 P.uniform2

prop_szilard_entropy :: Property
prop_szilard_entropy = once $ abs (P.jointEntropy2 P.szilardJoint - log 2) <= 1e-15

prop_szilard_mutual_information :: Property
prop_szilard_mutual_information = once $ abs (P.mutualInformation2 P.szilardJoint - log 2) <= 1e-15

prop_szilard_engine :: Positive Double -> Bool
prop_szilard_engine (Positive t) = P.extWork (P.szilardEngine (P.HeatBath t)) == P.kB * t * log 2

-- The engine obeys the second law, at equality up to rounding, judged against its joint's information.
prop_szilard_second_law :: Positive Double -> Bool
prop_szilard_second_law (Positive t) =
  let e = P.szilardEngine (P.HeatBath t)
      e' = e {P.extWork = P.extWork e * (1 - 1e-12)}
   in P.secondLaw (P.MeasureFeedback e') (P.Feedback (P.mutualInformation2 P.szilardJoint))
        && not (P.secondLaw (P.MeasureFeedback e {P.extWork = P.extWork e * (1 + 1e-9)}) (P.Feedback (P.mutualInformation2 P.szilardJoint)))

-- The chemical second law is coherence and the Clausius bound on the assemblage (twin of chemSecondLaw_iff).
prop_chem_secondlaw_iff :: Positive Double -> Double -> Bool -> Property
prop_chem_secondlaw_iff (Positive t) w coherent = forAll (choose (1, 8)) $ \n ->
  forAll (genDist n) $ \p -> forAll (genDist n) $ \q ->
    let tr = CS.ThermochemicalTransition (P.HeatBath t) p q w (if coherent then 0 else 1)
     in CS.chemSecondLaw tr == (CS.structurallyCoherent tr && CS.assemblageEntropyDrop tr <= w / t)

-- An update whose work sits a relative margin 'delta' from its floor T·ΔS (floating-point comparisons of T·ΔS ≤ W
-- and ΔS ≤ W / T agree away from the boundary).
genAccounted :: Gen (CS.ThermochemicalTransition, Bool)
genAccounted = do
  t <- choose (1, 1000)
  n <- choose (1, 8)
  p <- genDist n
  q <- genDist n
  delta <- elements [-0.5, -1e-3, 1e-3, 0.5]
  coherent <- arbitrary
  let floor' = t * (P.shannon p - P.shannon q)
      w = floor' + delta * (abs floor' + 1)
  pure (CS.ThermochemicalTransition (P.HeatBath t) p q w (if coherent then 0 else 1), delta > 0)

-- Refinement work is the erase case of the second law (twin of refinementWorkAccounted_iff).
prop_chem_refinement_accounted_iff :: Property
prop_chem_refinement_accounted_iff = forAll genAccounted $ \(tr, above) ->
  CS.refinementWorkAccounted tr == above
    && CS.refinementWorkAccounted tr == P.secondLaw (P.Erase (CS.erasureOf tr)) (P.Transformation (CS.tcPrior tr) (CS.tcPost tr))

-- The refinement floor is the chemical second law (twin of chemSecondLaw_iff_accounted).
prop_chem_secondlaw_iff_accounted :: Property
prop_chem_secondlaw_iff_accounted = forAll genAccounted $ \(tr, _) ->
  CS.chemSecondLaw tr == (CS.structurallyCoherent tr && CS.refinementWorkAccounted tr)

-- A physical binary erasure obeying the erase instance discharges the chemical second law of the update it
-- realises (twins of chem_entropy_bound_from_physical, refinementLandauerBound, chemSecondLaw_from_physical).
physicalErasure :: Gen P.ErasureProcess
physicalErasure = do { t <- choose (1, 1000); k <- choose (0, 2); pure (P.ErasureProcess (P.HeatBath t) (k * t)) }

obeysErase :: P.ErasureProcess -> Bool
obeysErase e = P.secondLaw (P.Erase e) (P.Erasure P.uniform2)

prop_chem_entropy_bound_from_physical :: Property
prop_chem_entropy_bound_from_physical = forAll physicalErasure $ \e ->
  let tr = CS.pcTransition (CS.physicalChemBridge e)
   in obeysErase e ==> P.secondLaw (P.Erase (CS.erasureOf tr)) (P.Transformation (CS.tcPrior tr) (CS.tcPost tr))

prop_chem_refinement_landauer_bound :: Property
prop_chem_refinement_landauer_bound = forAll physicalErasure $ \e ->
  let tr = CS.pcTransition (CS.physicalChemBridge e)
      temp = P.bathTemp (CS.tcBath tr)
   in obeysErase e ==> CS.tcWork tr >= temp * log 2 - 1e-12 * temp

prop_chem_secondlaw_from_physical :: Property
prop_chem_secondlaw_from_physical = forAll physicalErasure $ \e ->
  obeysErase e ==> CS.chemSecondLaw (CS.pcTransition (CS.physicalChemBridge e))

-- The coherent identity fixture (twins of coherentP0_zero_entropy_drop, _structurallyCoherent, _chemSecondLaw).
prop_chem_p0_zero_entropy_drop :: Property
prop_chem_p0_zero_entropy_drop = once $ CS.assemblageEntropyDrop CS.coherentP0Transition == 0

prop_chem_p0_coherent :: Property
prop_chem_p0_coherent = once $ CS.structurallyCoherent CS.coherentP0Transition

prop_chem_p0_secondlaw :: Property
prop_chem_p0_secondlaw = once $ CS.chemSecondLaw CS.coherentP0Transition

-- The chemical second law composes like the predicate it instantiates.
prop_chem_secondlaw_comp :: Positive Double -> Property
prop_chem_secondlaw_comp (Positive t) = forAll (choose (1, 8)) $ \n ->
  forAll (genDist n) $ \p -> forAll (genDist n) $ \q -> forAll (genDist n) $ \r ->
    let b = P.HeatBath t
        t1 = CS.ThermochemicalTransition b p q (t * (P.shannon p - P.shannon q) + 1e-9) 0
        t2 = CS.ThermochemicalTransition b q r (t * (P.shannon q - P.shannon r) + 1e-9) 0
     in (CS.chemSecondLaw t1 && CS.chemSecondLaw t2) ==>
          P.secondLaw (P.Erase (P.ErasureProcess b (CS.tcWork t1 + CS.tcWork t2 + 1e-9 * t))) (P.Transformation p r)

-- A state move that changes nothing is admissible; the predicate is satisfiable.
prop_process_transition_refl :: Property
prop_process_transition_refl = forAll (choose (0.3, 0.6)) $ \wc -> forAll (choose (0, 0.95)) $ \a ->
  forAll (choose (5, 40)) $ \temp -> let s = fromMix wc a temp in P.secondLaw P.Transition (P.Thermodynamic s s)

-- Cement admissibility is the transition instance with hydration and strength non-decreasing
-- (twin of Lean/Concrete/SecondLaw.lean concreteAdmissible_iff_secondLaw).
prop_concrete_admissible_iff_secondLaw :: ThermodynamicState -> ThermodynamicState -> Bool
prop_concrete_admissible_iff_secondLaw old new =
  let v = gateCheck old new 1
   in accepted v == (P.secondLaw P.Transition (P.Thermodynamic old new) && hydrationOk v && strengthOk v)

-- A step the gate passes is a member of the predicate (twin of gateCheck_secondLaw).
-- The second state is a small step from the first, each component moving either way, so both verdicts occur often.
prop_concrete_gate_secondLaw :: Property
prop_concrete_gate_secondLaw = forAll genState $ \old -> forAll (genStepFrom old) $ \new ->
  let passed = accepted (gateCheck old new 1)
   in cover 5 passed "gate passes" (not passed || P.secondLaw P.Transition (P.Thermodynamic old new))

genStepFrom :: ThermodynamicState -> Gen ThermodynamicState
genStepFrom (ThermodynamicState rho psi al fc fcMax) = do
  dRho <- choose (-150, 150)
  dPsi <- choose (-20, 5)
  dAl <- choose (-0.02, 0.1)
  dFc <- choose (-2, 10)
  pure (ThermodynamicState (rho + dRho) (psi + dPsi) (al + dAl) (fc + dFc) fcMax)

-- Hydration is irreversible by the second law: for Helmholtz states (ψ = −Q_hyd·α) at one density, a step is a member
-- of the predicate exactly when hydration does not go backwards (twin of helmholtz_secondLaw_iff). Degrees of hydration
-- on a grid of 0.01 keep every step outside the runtime tolerance band.
prop_concrete_helmholtz_secondLaw_iff :: Property
prop_concrete_helmholtz_secondLaw_iff =
  forAll (choose (1000, 3000)) $ \rho -> forAll (choose (0, 100 :: Int)) $ \i -> forAll (choose (0, 100 :: Int)) $ \j ->
    let state k = let a = fromIntegral k / 100 in ThermodynamicState rho (negate (qHydration * a)) a 0 intrinsicStrength
     in P.secondLaw P.Transition (P.Thermodynamic (state i) (state j)) == (i <= j)

prop_process_satisfiable :: Property
prop_process_satisfiable = once $
  P.secondLaw (P.Erase (P.landauerTightErasure (P.HeatBath 300))) (P.Erasure P.uniform2)

-- Independent erasures: the entropy both remove is at most the entropy both dissipate.
prop_process_erasure_additive :: Positive Double -> Double -> Double -> Property
prop_process_erasure_additive (Positive t) w1 w2 =
  let law w = P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) w)) (P.Erasure P.uniform2)
   in (law w1 && law w2) ==> 2 * log 2 <= (w1 + w2) / t + 1e-12

-- Powers' gel-space ratio x = 68·α / (32·α + 100·w) (twin of Lean/Concrete/Powers.lean gelSpaceRatio).
gelSpaceRatioQ :: Rational -> Rational -> Rational
gelSpaceRatioQ alpha wc = 68 * alpha / (32 * alpha + 100 * wc)

-- The gel fits its space exactly when w ≥ 0.36·α (twin of gelSpaceRatio_le_one_iff).
prop_powers_gel_fits_iff :: Property
prop_powers_gel_fits_iff = forAll genRat $ \alpha -> forAll (suchThat genRat (> 0)) $ \wc ->
  (gelSpaceRatioQ alpha wc <= 1) == (36 * alpha <= 100 * wc)

-- The runtime strength of a mix is S·x³ with the same x (the cited S = 234 MPa).
prop_powers_runtime_strength :: Property
prop_powers_runtime_strength = forAll (choose (0.3, 0.6)) $ \wc -> forAll (choose (0, 1)) $ \alpha ->
  let x = fromRational (gelSpaceRatioQ (toRational alpha) (toRational wc)) :: Double
      expected = fromRational SI.powersGelStrength * x ^ (3 :: Int)
   in abs (strength (fromMix wc alpha 20) - expected) <= 1e-9 * (1 + expected)

-- Powers' volume model in exact Rational arithmetic (twin of Lean/Concrete/PowersVolume.lean).
genRat :: Gen Rational
genRat = do { n <- choose (0, 1000 :: Integer); pure (fromInteger n / 1000) }

powersPhases :: Rational -> Rational -> [Rational]
powersPhases p a =
  [ (1 - p) * (1 - a), SI.gelSolidsVolume * (1 - p) * a, SI.gelWaterVolume * (1 - p) * a
  , p - SI.capillaryConsumption * (1 - p) * a, SI.shrinkageVolume * (1 - p) * a ]

waterFraction :: Rational -> Rational
waterFraction w = w * SI.densityRatio / (w * SI.densityRatio + 1)

prop_powers_coefficient_balance :: Property
prop_powers_coefficient_balance = once $
  SI.gelSolidsVolume + SI.gelWaterVolume + SI.shrinkageVolume - SI.capillaryConsumption == 1

-- Per unit volume of cement (twin of capillaryPerCement and spacePerCement).
capillaryPerCement, spacePerCement :: Rational -> Rational
capillaryPerCement w = w * SI.densityRatio - SI.capillaryConsumption
spacePerCement w = capillaryPerCement w + SI.shrinkageVolume

prop_powers_per_cement_sealed :: Property
prop_powers_per_cement_sealed = forAll genRat $ \w -> (capillaryPerCement w >= 0) == (SI.criticalWcSealed <= w)

prop_powers_per_cement_space :: Property
prop_powers_per_cement_space = forAll genRat $ \w -> (spacePerCement w >= 0) == (SI.criticalWcSpace <= w)

-- The paste fractions are the per-cement volumes over the paste volume w d + 1.
prop_powers_fraction_per_cement :: Property
prop_powers_fraction_per_cement = forAll genRat $ \w ->
  let ph = powersPhases (waterFraction w) 1
      paste = w * SI.densityRatio + 1
   in ph !! 3 == capillaryPerCement w / paste && ph !! 3 + ph !! 4 == spacePerCement w / paste

prop_powers_volume_balance :: Property
prop_powers_volume_balance = forAll genRat $ \p -> forAll genRat $ \a -> sum (powersPhases p a) == 1

prop_powers_sealed_threshold :: Property
prop_powers_sealed_threshold = forAll genRat $ \w ->
  let capillary = powersPhases (waterFraction w) 1 !! 3
   in (capillary >= 0) == (SI.criticalWcSealed <= w)

prop_powers_space_threshold :: Property
prop_powers_space_threshold = forAll genRat $ \w ->
  let ph = powersPhases (waterFraction w) 1
   in (ph !! 3 + ph !! 4 >= 0) == (SI.criticalWcSpace <= w)

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
  check r prop_dignity_d_max

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
  check r prop_sqrt_window_warmup_is_admissible

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
  check r prop_process_si_bound
  check r prop_process_landauer_bound_any_drop
  check r prop_process_si_bound_any_drop
  putStrLn "-- Second-law bounds on elastic constants (Constants.SecondLawElastic)"
  check r prop_bound_stiffness_nonneg
  check r prop_bound_modulus_pos
  check r prop_bound_two_mode_nonneg
  check r prop_bound_isotropic_poisson
  check r prop_bound_isotropic_young
  check r prop_bound_sls_relaxed
  check r prop_bound_orthotropic_poisson
  putStrLn "-- Second-law bounds on dissipation coefficients (Constants.SecondLawDissipation)"
  check r prop_bound_dissipation_coefficient
  check r prop_bound_viscosity
  check r prop_bound_bingham
  check r prop_bound_loss_modulus
  putStrLn "-- Second-law bound on restitution (ConvexPhiChannels, Constants.SecondLawRestitution)"
  check r prop_bound_restitution
  check r prop_bound_restitution_energy_loss
  putStrLn "-- The Landauer factor fixed by the second law (Constants.SecondLawLandauerFactor)"
  check r prop_uniform_binary_entropy
  check r prop_landauer_factor_iff
  check r prop_landauer_factor_least
  putStrLn "-- Second-law bounds on electromagnetic constants (Constants.SecondLawElectromagnetic)"
  check r prop_bound_electric_relaxation
  check r prop_bound_magnetic_relaxation
  check r prop_bound_conductance_dissipation
  check r prop_bound_resistance_dissipation
  check r prop_si_vacuum_permittivity_relaxation
  check r prop_si_vacuum_permeability_relaxation
  check r prop_si_conductance_quantum_dissipation
  check r prop_si_von_klitzing_dissipation
  putStrLn "-- Second-law bounds on inelastic-solid parameters (Constants.SecondLawSolidInelastic)"
  check r prop_bound_coupled_well
  check r prop_bound_double_well
  check r prop_bound_griffith_energy
  check r prop_bound_griffith_toughness
  check r prop_bound_norton
  check r prop_bound_parabolic_rate
  check r prop_bound_frictional_bond
  putStrLn "-- Second-law bounds on transport, reaction and poroelastic constants (Constants.SecondLawPoroContinuum)"
  check r prop_bound_reaction_rate
  check r prop_bound_reaction_rate_constant
  check r prop_bound_fick_diffusivity
  check r prop_bound_darcy_permeability
  check r prop_bound_biot_coefficient
  check r prop_bound_biot_storage
  check r prop_bound_isotropic_moduli_pos
  putStrLn "-- Second-law bounds of the constants table (Constants.Bounds): each bound with its theorem's property"
  mapM_ (\(name, p) -> check r (counterexample name p)) boundProperties
  mapM_ (\(name, ok) -> check r (once (counterexample name ok))) Bounds.boundChecks
  putStrLn "-- Convex-by-construction dissipation potentials (Convex.PhiGrammar)"
  check r prop_phi_zero
  check r prop_phi_nonneg
  check r prop_phi_chord_convex
  check r prop_phi_subgradient
  check r prop_phi_dissipation_nonneg
  check r prop_phi_passive_second_law
  check r prop_phi_capped_not_convex
  putStrLn "-- GENERIC entropy production (Generic.EntropyProduction)"
  check r prop_generic_energy_rate_zero
  check r prop_generic_entropy_rate_nonneg
  check r prop_generic_free_energy_descent
  putStrLn "-- Composition law of GSM atoms and the glue fraction (Composition.GsmMonoid)"
  mapM_ (\(name, p) -> check r (counterexample name p)) gsmMonoidProps
  putStrLn "-- Powers' capillary porosity and its rounded coefficients (Concrete.PowersCapillary)"
  mapM_ (\(name, p) -> check r (counterexample name p)) powersCapillaryProps
  putStrLn "-- Chemistry as an instance of the one predicate (Chem.ProcessFunctor)"
  mapM_ (\(name, p) -> check r (counterexample name p)) chemProcessFunctorProps
  putStrLn "-- Fluctuation theorem and thermodynamic uncertainty relation (Lean, Coq and Agda twins)"
  mapM_ (\(name, p) -> check r (counterexample name p)) fluctuationProps
  check r prop_process_binary_is_transformation
  check r prop_process_transformation_id
  check r prop_process_transformation_comp
  check r prop_select_empty
  check r prop_select_minimal
  check r prop_select_descent
  check r prop_select_perm_invariant
  check r prop_select_secondLaw
  check r prop_process_units_bridge
  check r prop_oneineq_chain
  check r prop_oneineq_erase_iff
  check r prop_oneineq_feedback_iff
  check r prop_oneineq_transition_iff
  check r prop_oneineq_transition_erase_chain
  check r prop_oneineq_secondlaw_implies
  check r prop_oneineq_szilard_chain
  check r prop_cg_coarse_from_fine
  check r prop_cg_id
  check r prop_cg_refusal_sound
  check r prop_cg_product_entropy
  check r prop_cg_lump_coarse_from_fine
  check r prop_semantic_iff
  check r prop_semantic_from_physical
  check r prop_semantic_landauer_bound
  check r prop_semantic_p0
  check r prop_semantic_product_mi_zero
  check r prop_cost_uniform_entropy
  check r prop_cost_entropy_drop_joules
  check r prop_cost_info_per_joule
  check r prop_cost_bit_erasure
  check r prop_cost_honest_spend_of_secondLaw
  check r prop_cost_eta_cog_le_of_honest
  check r prop_cost_eta_cog_le_of_secondLaw
  check r prop_szilard_joint
  check r prop_szilard_marginal_x
  check r prop_szilard_marginal_y
  check r prop_szilard_entropy
  check r prop_szilard_mutual_information
  check r prop_szilard_engine
  check r prop_szilard_second_law
  check r prop_chem_secondlaw_comp
  check r prop_chem_secondlaw_iff
  check r prop_chem_refinement_accounted_iff
  check r prop_chem_secondlaw_iff_accounted
  check r prop_chem_entropy_bound_from_physical
  check r prop_chem_refinement_landauer_bound
  check r prop_chem_secondlaw_from_physical
  check r prop_chem_p0_zero_entropy_drop
  check r prop_chem_p0_coherent
  check r prop_chem_p0_secondlaw
  check r prop_process_transition_refl
  check r prop_process_satisfiable
  check r prop_concrete_admissible_iff_secondLaw
  check r prop_concrete_gate_secondLaw
  check r prop_concrete_helmholtz_secondLaw_iff
  check r prop_process_erasure_additive
  check r prop_urge_admit_clausius
  check r prop_urge_kleisli_assoc
  check r prop_urge_kleisli_left_unit
  check r prop_urge_kleisli_right_unit
  check r prop_urge_preserves_chain_append
  check r prop_urge_preserves_witness_retained
  check r prop_urge_post_provenance_preserves
  check r prop_powers_coefficient_balance
  check r prop_powers_volume_balance
  check r prop_powers_gel_fits_iff
  check r prop_powers_runtime_strength
  check r prop_powers_per_cement_sealed
  check r prop_powers_per_cement_space
  check r prop_powers_fraction_per_cement
  check r prop_powers_sealed_threshold
  check r prop_powers_space_threshold

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
