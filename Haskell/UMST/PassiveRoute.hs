-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Module      : UMST.PassiveRoute
-- Description : The passive route into the transition case of the second law (twin of
--               Lean/Convex/PassiveRoute.lean and the passive cartridge law of Lean/ConvexPhiDissipation.lean, with
--               Coq/Convex/PassiveRoute.v and Agda/Convex/PassiveRoute.agda).
--
-- A passive step supplies no power: its free energy falls by the dissipation D (Δψ + D = 0) and nothing else of
-- the state changes. The Lean, Coq and Agda twins prove that the transition case of the second law holds on such a
-- step exactly when D ≥ 0. Here the step is built from a state and its dissipation, the runtime second law
-- ('P.secondLaw' on the transition case) judges it, and the QuickCheck properties of test/PassiveRouteProps.hs check
-- the equivalence and the convex cartridge law. Haskell carries no proofs.
module UMST.PassiveRoute
  ( -- * Passive steps
    stepSecondLaw
  , dissipatingStep
  , releasedFreeEnergy
  , passiveSecondLaw
  , relaxationSecondLaw
    -- * The convex cartridge law
  , gsmCartridgePassiveSecondLaw
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.GsmMonoid (GsmPotential, power)
import qualified UMST.Process as P

-- | The runtime transition case of the second law on a step from @old@ to @new@.
stepSecondLaw :: ThermodynamicState -> ThermodynamicState -> Bool
stepSecondLaw old new = P.secondLaw P.Transition (P.Thermodynamic old new)

-- | The passive step from @old@ that dissipates @d@: the free energy falls by @d@ and nothing else changes, so the
-- balance Δψ + d = 0 holds by construction.
dissipatingStep :: ThermodynamicState -> Double -> ThermodynamicState
dissipatingStep old d = old {freeEnergy = freeEnergy old - d}

-- | The dissipation a step names through its energy balance: ψ_old − ψ_new.
releasedFreeEnergy :: ThermodynamicState -> ThermodynamicState -> Double
releasedFreeEnergy old new = freeEnergy old - freeEnergy new

-- | The passive route: the second law on the passive step from @old@ dissipating @d@ (twin of
-- passive_secondLaw_iff, which states that it holds exactly when d ≥ 0).
passiveSecondLaw :: ThermodynamicState -> Double -> Bool
passiveSecondLaw old d = stepSecondLaw old (dissipatingStep old d)

-- | The passive relaxation of @old@ to the natural state (free energy zero) dissipates its stored free energy (twin
-- of relaxation_stored_nonneg).
relaxationSecondLaw :: ThermodynamicState -> Bool
relaxationSecondLaw old = passiveSecondLaw old (freeEnergy old)

-- | The passive cartridge law: a GSM potential at rate @x@ dissipates its power x · dphi x, and the passive step
-- from @old@ dissipating that power passes the second law (twin of gsmCartridge_passive_secondLaw).
gsmCartridgePassiveSecondLaw :: GsmPotential -> Rational -> ThermodynamicState -> Bool
gsmCartridgePassiveSecondLaw p x old = passiveSecondLaw old (fromRational (power p x))
