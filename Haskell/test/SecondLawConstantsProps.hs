-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of the constants the second law fixes or bounds in Constants.SecondLawLandauerFactor and
-- Constants.SecondLawElectromagnetic (Lean, Coq and Agda twins), and of the entropy of the uniform bit.
--
-- Each property runs the runtime second law ('P.secondLaw'): the erase case on the uniform bit for the Landauer
-- factor, and the transition case on a passive step (a vacuum field relaxing to zero, or a Joule step dissipating
-- out of the free energy) for the electromagnetic coefficients. A bound property checks that the law admits the
-- step exactly when the bound holds; an SI property checks that the law admits every step at the exact SI value
-- of "UMST.Constants.SI". Fields, voltages and currents are drawn so that the energies sit far outside the gate's
-- 1e-6 tolerance.
module SecondLawConstantsProps
  ( prop_uniform_binary_entropy
  , prop_landauer_factor_iff
  , prop_landauer_factor_least
  , prop_bound_electric_relaxation
  , prop_bound_magnetic_relaxation
  , prop_bound_conductance_dissipation
  , prop_bound_resistance_dissipation
  , prop_si_vacuum_permittivity_relaxation
  , prop_si_vacuum_permeability_relaxation
  , prop_si_conductance_quantum_dissipation
  , prop_si_von_klitzing_dissipation
  ) where

import Test.QuickCheck

import UMST.Concrete (ThermodynamicState (..))
import qualified UMST.Constants.SI as SI
import qualified UMST.Process as P

-- | The second law on a passive step from free energy @psi@ to @psi'@ at fixed density.
passiveStep :: Double -> Double -> Bool
passiveStep psi psi' = P.secondLaw P.Transition (P.Thermodynamic (st psi) (st psi'))
  where
    st f = ThermodynamicState {density = 2400, freeEnergy = f, hydration = 0.5, strength = 30, maxStrength = 100}

-- | The second law on erasing the uniform bit at temperature @t@ with work per kelvin @r@.
erasesUniformBit :: Double -> Double -> Bool
erasesUniformBit t r = P.secondLaw (P.Erase (P.ErasureProcess (P.HeatBath t) (t * r))) (P.Erasure P.uniform2)

-- | A coefficient of magnitude in [0.01, 1000] with either sign.
genCoefficient :: Gen Double
genCoefficient = (*) <$> elements [1, -1] <*> choose (0.01, 1000)

-- | A nonzero field, voltage or current of magnitude in [0.1, 10] with either sign.
genLoad :: Gen Double
genLoad = (*) <$> elements [1, -1] <*> choose (0.1, 10)

-- | The uniform bit carries ln 2 nats (twin of LandauerLaw.uniformBinaryEntropy).
prop_uniform_binary_entropy :: Property
prop_uniform_binary_entropy = once $ abs (P.shannon2 P.uniform2 - log 2) <= 1e-15

-- | Erasing the uniform bit with work per kelvin r obeys the law exactly when ln 2 <= r
-- (twin of secondLaw_uniformBit_iff). The draw keeps r at least 1e-9 from ln 2, outside rounding.
prop_landauer_factor_iff :: Property
prop_landauer_factor_iff = forAll (choose (1, 1000)) $ \t -> forAll (choose (0, 2)) $ \r ->
  abs (r - log 2) > 1e-9 ==> erasesUniformBit t r === (log 2 <= r)

-- | ln 2 is admitted, and nothing below it is (twin of landauerFactor_isLeast).
prop_landauer_factor_least :: Property
prop_landauer_factor_least = forAll (choose (1, 1000)) $ \t -> forAll (choose (1e-6, 0.5)) $ \gap ->
  erasesUniformBit t (log 2 + 1e-12) && not (erasesUniformBit t (log 2 - gap))

-- | A field storing ½·ε·E² relaxes exactly when ε ≥ 0 (twin of electricRelaxation_secondLaw_iff).
prop_bound_electric_relaxation :: Property
prop_bound_electric_relaxation = forAll genCoefficient $ \eps -> forAll genLoad $ \e ->
  passiveStep (0.5 * eps * e * e) 0 === (eps >= 0)

-- | A field storing B²/(2μ) relaxes exactly when μ > 0 (twin of magneticRelaxation_secondLaw_iff).
prop_bound_magnetic_relaxation :: Property
prop_bound_magnetic_relaxation = forAll genCoefficient $ \mu -> forAll (choose (1, 10)) $ \b ->
  passiveStep (b * b / (2 * mu)) 0 === (mu > 0)

-- | A Joule step dissipating G·V²·dt is admitted exactly when G ≥ 0 (twin of conductanceDissipation_secondLaw_iff).
prop_bound_conductance_dissipation :: Property
prop_bound_conductance_dissipation = forAll genCoefficient $ \g -> forAll genLoad $ \v ->
  forAll (choose (0.1, 10)) $ \dt -> forAll (choose (-100, 100)) $ \psi ->
    passiveStep psi (psi - g * v * v * dt) === (g >= 0)

-- | A Joule step dissipating R·I²·dt is admitted exactly when R ≥ 0 (twin of resistanceDissipation_secondLaw_iff).
prop_bound_resistance_dissipation :: Property
prop_bound_resistance_dissipation = forAll genCoefficient $ \r -> forAll genLoad $ \i ->
  forAll (choose (0.1, 10)) $ \dt -> forAll (choose (-100, 100)) $ \psi ->
    passiveStep psi (psi - r * i * i * dt) === (r >= 0)

-- | Every field relaxes at the exact ε₀ (twin of vacuumPermittivity_relaxation_secondLaw); fields of 1e6 to 1e8 V/m.
prop_si_vacuum_permittivity_relaxation :: Property
prop_si_vacuum_permittivity_relaxation = forAll (choose (1e6, 1e8)) $ \e ->
  SI.vacuumPermittivity > 0 && passiveStep (0.5 * fromRational SI.vacuumPermittivity * e * e) 0

-- | Every field relaxes at the exact μ₀ (twin of vacuumPermeability_relaxation_secondLaw); flux densities of 0.01 to
-- 10 T.
prop_si_vacuum_permeability_relaxation :: Property
prop_si_vacuum_permeability_relaxation = forAll (choose (0.01, 10)) $ \b ->
  SI.vacuumPermeability > 0 && passiveStep (b * b / (2 * fromRational SI.vacuumPermeability)) 0

-- | Every Joule step is admitted at the exact G₀ (twin of conductanceQuantum_dissipation_secondLaw); 10 to 1000 V.
prop_si_conductance_quantum_dissipation :: Property
prop_si_conductance_quantum_dissipation = forAll (choose (10, 1000)) $ \v -> forAll (choose (1, 10)) $ \dt ->
  SI.conductanceQuantum > 0 && passiveStep 0 (negate (fromRational SI.conductanceQuantum * v * v * dt))

-- | Every Joule step is admitted at the exact R_K (twin of vonKlitzing_dissipation_secondLaw); 0.01 to 1 A.
prop_si_von_klitzing_dissipation :: Property
prop_si_von_klitzing_dissipation = forAll (choose (0.01, 1)) $ \i -> forAll (choose (1, 10)) $ \dt ->
  SI.vonKlitzing > 0 && passiveStep 0 (negate (fromRational SI.vonKlitzing * i * i * dt))
