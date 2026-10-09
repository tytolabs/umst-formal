-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of chemistry as an instance of the one predicate (twins of Lean/Chem/ProcessFunctor.lean, with its
-- Coq and Agda twins). Every property runs the runtime second law 'P.secondLaw' on the image of an update: the
-- erasure that pays for it, judged against the transformation of its state distribution.
module ChemProcessFunctorProps
  ( chemProcessFunctorProps
  ) where

import Test.QuickCheck

import qualified UMST.Chem.ProcessFunctor as F
import qualified UMST.Chem.SecondLaw as CS
import qualified UMST.Process as P

genDist :: Int -> Gen P.ProbDist
genDist n = do
  xs <- vectorOf n (choose (0, 1 :: Double)) `suchThat` (\ys -> sum ys > 1e-6)
  pure (P.ProbDist (map (/ sum xs) xs))

-- | An update whose work sits a relative margin from its floor T·ΔS, so the floating-point comparisons of T·ΔS ≤ W and
-- ΔS ≤ W / T agree.
genUpdate :: Gen CS.ThermochemicalTransition
genUpdate = do
  t <- choose (1, 1000)
  n <- choose (1, 8)
  p <- genDist n
  q <- genDist n
  delta <- elements [-0.5, -1e-3, 1e-3, 0.5]
  coherent <- arbitrary
  let floor' = t * (P.shannon p - P.shannon q)
  pure (CS.ThermochemicalTransition (P.HeatBath t) p q (floor' + delta * (abs floor' + 1)) (if coherent then 0 else 1))

-- | An update with integer work and defect, so sums of updates are exact in floating point.
genIntegral :: P.HeatBath -> P.ProbDist -> P.ProbDist -> Gen CS.ThermochemicalTransition
genIntegral b p q = do
  w <- choose (-50, 50 :: Int)
  d <- choose (-3, 3 :: Int)
  pure (CS.ThermochemicalTransition b p q (fromIntegral w) (fromIntegral d))

sameUpdate :: CS.ThermochemicalTransition -> CS.ThermochemicalTransition -> Bool
sameUpdate s t =
  P.bathTemp (CS.tcBath s) == P.bathTemp (CS.tcBath t) && P.mass (CS.tcPrior s) == P.mass (CS.tcPrior t)
    && P.mass (CS.tcPost s) == P.mass (CS.tcPost t) && CS.tcWork s == CS.tcWork t && CS.tcDefect s == CS.tcDefect t

-- The chemical second law is coherence and membership of the image in SecondLaw (chemSecondLaw_iff_process).
prop_chem_functor_iff_process :: Property
prop_chem_functor_iff_process = forAll genUpdate $ \t ->
  CS.chemSecondLaw t == (CS.structurallyCoherent t && P.secondLaw (F.processOf t) (F.transformationOf t))

-- The Landauer work floor is the erase case (secondLaw_iff_workFloor, refinementWorkAccounted_iff).
prop_chem_functor_iff_work_floor :: Property
prop_chem_functor_iff_work_floor = forAll genUpdate $ \t ->
  P.secondLaw (F.processOf t) (F.transformationOf t) == CS.refinementWorkAccounted t

-- The updates form a category: identities on both sides and associativity of the composite.
prop_chem_functor_category :: Property
prop_chem_functor_category = forAll (choose (1, 1000)) $ \temp -> forAll (choose (1, 6)) $ \n ->
  forAll (vectorOf 4 (genDist n)) $ \ds -> case ds of
    [p, q, r, s] ->
      let b = P.HeatBath temp
       in forAll (genIntegral b p q) $ \t1 -> forAll (genIntegral b q r) $ \t2 -> forAll (genIntegral b r s) $ \t3 ->
            sameUpdate (F.composite (F.idAt b p) t1) t1 && sameUpdate (F.composite t1 (F.idAt b q)) t1
              && sameUpdate (F.composite (F.composite t1 t2) t3) (F.composite t1 (F.composite t2 t3))
    _ -> property False

-- Identities are admissible (chemSecondLaw_idAt) and admissibility is closed under composition (chemSecondLaw_seq).
prop_chem_functor_admissible :: Positive Double -> Property
prop_chem_functor_admissible (Positive temp) = forAll (choose (1, 8)) $ \n ->
  forAll (genDist n) $ \p -> forAll (genDist n) $ \q -> forAll (genDist n) $ \r ->
    let b = P.HeatBath temp
        t1 = CS.ThermochemicalTransition b p q (temp * (P.shannon p - P.shannon q) + 1e-9) 0
        t2 = CS.ThermochemicalTransition b q r (temp * (P.shannon q - P.shannon r) + 1e-9) 0
     in CS.chemSecondLaw (F.idAt b p)
          .&&. ((CS.chemSecondLaw t1 && CS.chemSecondLaw t2) ==> CS.chemSecondLaw (F.composite t1 t2))

-- The bridge preserves and reflects admissibility (PhysicalChemBridge.secondLaw_iff); the work sits away from the
-- Landauer floor T ln 2.
prop_chem_functor_bridge_iff :: Property
prop_chem_functor_bridge_iff = forAll (choose (1, 1000)) $ \temp -> forAll (elements [0, 0.5, 0.69, 0.7, 1, 2]) $ \k ->
  let b = CS.physicalChemBridge (P.ErasureProcess (P.HeatBath temp) (k * temp))
   in F.bridgeSecondLaw b == F.realisedSecondLaw b

-- An identity transformation obeys the erase case exactly at non-negative work (secondLaw_identity_iff_work_nonneg).
prop_chem_functor_identity_work_nonneg :: Property
prop_chem_functor_identity_work_nonneg = forAll (choose (1, 1000)) $ \temp -> forAll (choose (1, 8)) $ \n ->
  forAll (genDist n) $ \p -> forAll (choose (-10, 10)) $ \w ->
    P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath temp) w)) (P.Transformation p p) == (w >= 0)

-- An update and its reverse obey the erase case at zero work exactly when it removes no entropy
-- (zeroWork_reversible_iff); the generator draws the post equal to the prior half the time.
prop_chem_functor_zero_work_reversible :: Property
prop_chem_functor_zero_work_reversible = forAll (choose (1, 1000)) $ \temp -> forAll (choose (1, 8)) $ \n ->
  forAll (genDist n) $ \p -> forAll (oneof [pure p, genDist n]) $ \q ->
    let b = P.HeatBath temp
        t = CS.ThermochemicalTransition b p q 0 0
        idle = P.Erase (P.ErasureProcess b 0)
     in (P.secondLaw idle (P.Transformation p q) && P.secondLaw idle (P.Transformation q p))
          == (CS.assemblageEntropyDrop t == 0)

-- The P0 fixture is the identity update; it is admissible exactly at non-negative work and reversible at zero work.
prop_chem_functor_p0 :: Property
prop_chem_functor_p0 = forAll (choose (-10, 10)) $ \w ->
  let p0 = CS.coherentP0Transition
      at w' = P.Erase (P.ErasureProcess (CS.tcBath p0) w')
   in sameUpdate p0 (F.idAt (CS.tcBath p0) (CS.tcPrior p0))
        && P.secondLaw (at w) (F.transformationOf p0) == (w >= 0)
        && P.secondLaw (at 0) (P.Transformation (CS.tcPrior p0) (CS.tcPost p0))
        && P.secondLaw (at 0) (P.Transformation (CS.tcPost p0) (CS.tcPrior p0))

chemProcessFunctorProps :: [(String, Property)]
chemProcessFunctorProps =
  [ ("chem_functor_iff_process", prop_chem_functor_iff_process)
  , ("chem_functor_iff_work_floor", prop_chem_functor_iff_work_floor)
  , ("chem_functor_category", prop_chem_functor_category)
  , ("chem_functor_admissible", property prop_chem_functor_admissible)
  , ("chem_functor_bridge_iff", prop_chem_functor_bridge_iff)
  , ("chem_functor_identity_work_nonneg", prop_chem_functor_identity_work_nonneg)
  , ("chem_functor_zero_work_reversible", prop_chem_functor_zero_work_reversible)
  , ("chem_functor_p0", prop_chem_functor_p0)
  ]
