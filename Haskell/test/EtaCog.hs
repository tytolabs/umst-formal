-- | Engineering mirror of `Lean/EtaCog.lean` (MI-per-Joule frugality, dignity-weighted).
module EtaCog where

import Test.QuickCheck

import Dignity (dignityStep, honestSpend, landauerJoulesPerBit)

-- | η_cog = dignity · ΔMI / (ΔE + k_B T ln 2) — denominator case **(i)** (COCKPIT_DESIGN_BRIEF §5).
etaCog :: Double -> Double -> Double -> Double -> Double
etaCog tK dignity mi e =
  let lb = landauerJoulesPerBit tK
      denom = e + lb
   in if denom > 0 && dignity >= 0 && mi >= 0 && e >= 0 && tK > 0
        then dignity * mi / denom
        else 0

prop_eta_cog_nonneg :: Double -> Double -> Double -> Double -> Property
prop_eta_cog_nonneg tK d mi e =
  let tK' = abs tK + 1e-6
      d' = abs (sin d) * 9.99
      mi' = abs mi
      e' = abs e
   in property $ etaCog tK' d' mi' e' >= -1e-15

prop_eta_cog_monotone_dignity :: Double -> Double -> Double -> Double -> Double -> Property
prop_eta_cog_monotone_dignity tK d1 d2 mi e =
  let tK' = 200 + abs (sin tK) * 100
      lo = min (abs d1) (abs d2)
      hi = max (abs d1) (abs d2)
      mi' = abs (sin mi)
      e' = landauerJoulesPerBit tK' * mi' + abs e + 1e-9
   in lo <= hi ==> etaCog tK' lo mi' e' <= etaCog tK' hi mi' e' + 1e-12

prop_eta_cog_monotone_mi :: Double -> Double -> Double -> Double -> Double -> Property
prop_eta_cog_monotone_mi tK d mi1 mi2 e =
  let tK' = 250 + abs (cos tK) * 50
      d' = abs (sin d) * 5
      m1 = abs (sin mi1)
      m2 = m1 + abs (cos mi2)
      e' = landauerJoulesPerBit tK' * m2 + 1.0
   in property $ etaCog tK' d' m1 e' <= etaCog tK' d' m2 e' + 1e-12

prop_eta_cog_antitone_energy :: Double -> Double -> Double -> Double -> Double -> Property
prop_eta_cog_antitone_energy tK d mi e1 e2 =
  let tK' = 300 + abs (sin tK) * 20
      d' = abs (cos d) * 7
      mi' = abs (sin mi) + 0.01
      lo = abs (sin e1)
      hi = lo + abs (cos e2) + 0.5
   in property $ etaCog tK' d' mi' hi <= etaCog tK' d' mi' lo + 1e-12

-- | At ΔE = 0, η equals dignity·ΔMI / Landauer floor only.
prop_eta_cog_energy_zero_shape :: Double -> Double -> Double -> Property
prop_eta_cog_energy_zero_shape tK d mi =
  let tK' = 280 + abs (sin tK) * 40
      d' = abs (cos d) * 4 + 0.01
      mi' = abs (sin mi) + 0.02
      lb = landauerJoulesPerBit tK'
      y = etaCog tK' d' mi' 0
      y' = d' * mi' / lb
   in property $ abs (y - y') <= 1e-9

-- | Dishonest dignity step freezes value ⇒ same η on a fixed cockpit claim.
prop_eta_cog_frozen_dignity_path :: Double -> Double -> Double -> Double -> Double -> Property
prop_eta_cog_frozen_dignity_path tK cur mi e ecMi =
  let tK' = 260 + abs (sin tK) * 30
      cur' = abs (sin cur) * 6
      mi' = abs (sin mi) + 0.05
      e' = abs (sin e) + 0.01
   in not (honestSpend tK' mi' e') ==>
        let dAfter = dignityStep tK' cur' mi' e'
            ecMi' = abs (sin ecMi) + 0.01
            ecE' = landauerJoulesPerBit tK' * ecMi' + abs (cos e) + 0.5
         in property $ abs (etaCog tK' dAfter ecMi' ecE' - etaCog tK' cur' ecMi' ecE') <= 1e-12
