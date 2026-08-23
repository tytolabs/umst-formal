-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Chem.Kleisli
-- Description : Meso/acting chemistry — Kleisli @Interact@ morphism laws.
--
-- Mirrors @Agda/Chem/KleisliInteract.agda@ and @Lean/Chem/KleisliInteract.lean@
-- on @umst-formal/meso_acting@: Kleisli arrows over cement
-- 'UMST.Concrete.ThermodynamicState', graded gate admissibility, identity /
-- associativity / unit coherence.
--
-- @physics_green@ stays false — thermo witnesses remain Unwired until FORMAL BAR.
module UMST.Chem.Kleisli
  ( -- * Carriers
    KleisliArrow
    -- * Well-typing (gate admissibility)
  , admissibleStep
  , wellTypedAt
  , makeGateArrow
  , gateArrowWellTyped
    -- * Kleisli algebra
  , interactIdentity
  , kleisliCompose
  , kleisliFold
    -- * Laws (identity / assoc / coherence)
  , kleisliComposeAssoc
  , kleisliLeftUnit
  , kleisliRightUnit
  , kleisliComposeWellTypedAt
  , kleisliCoherenceUnits
    -- * Meso acting bridge (second law + conservation spine)
  , chemPhysicsGreen
  , chemPhysicsGreenFalse
  , kleisliInteractProductionWired
  , kleisliInteractProductionWiredFalse
  , kleisliInteractModuleWitness
  ) where

import UMST.Concrete
  ( AdmissibilityResult (..)
  , ThermodynamicState (..)
  , gateCheck
  )

-- | Nominal chemistry step Δt for gate evaluation (seconds).
chemStepDt :: Double
chemStepDt = 3600.0

-- | Kleisli arrow over thermodynamic states (meso acting carrier).
type KleisliArrow = ThermodynamicState -> Maybe ThermodynamicState

-- | Single-step gate admissibility (lifts 'gateCheck' / Agda 'Admissible').
admissibleStep :: ThermodynamicState -> ThermodynamicState -> Bool
admissibleStep old new = accepted (gateCheck old new chemStepDt)

-- | Well-typed at a witness pair: successful output implies admissible step.
wellTypedAt :: KleisliArrow -> ThermodynamicState -> ThermodynamicState -> Bool
wellTypedAt f s s' = f s == Just s' && admissibleStep s s'

-- | Gate-checked Kleisli arrow from a state proposal (Lean 'makeGateArrow').
makeGateArrow :: (ThermodynamicState -> ThermodynamicState) -> KleisliArrow
makeGateArrow propose s =
  let s' = propose s
   in if admissibleStep s s' then Just s' else Nothing

-- | Every successful 'makeGateArrow' step is admissible.
gateArrowWellTyped :: (ThermodynamicState -> ThermodynamicState) -> ThermodynamicState -> Bool
gateArrowWellTyped propose s =
  case makeGateArrow propose s of
    Nothing -> True
    Just s' -> admissibleStep s s'

-- | Kleisli identity (refuse ill-typed identity-cost propagation).
interactIdentity :: KleisliArrow
interactIdentity = Just

-- | Kleisli composition (Lean 'kleisliCompose' / Agda 'kleisli-compose').
kleisliCompose :: KleisliArrow -> KleisliArrow -> KleisliArrow
kleisliCompose f g s =
  case f s of
    Nothing -> Nothing
    Just s' -> g s'

-- | Fold a non-empty Kleisli chain (Lean 'kleisliFold').
kleisliFold :: [KleisliArrow] -> KleisliArrow
kleisliFold [] = interactIdentity
kleisliFold [f] = f
kleisliFold (f : rest) = kleisliCompose f (kleisliFold rest)

-- | Pointwise associativity (Agda 'kleisli-compose-assoc').
kleisliComposeAssoc :: KleisliArrow -> KleisliArrow -> KleisliArrow -> ThermodynamicState -> Bool
kleisliComposeAssoc f g h s =
  kleisliCompose (kleisliCompose f g) h s == kleisliCompose f (kleisliCompose g h) s

-- | Left unit law (Agda 'kleisli-left-unit').
kleisliLeftUnit :: KleisliArrow -> ThermodynamicState -> Bool
kleisliLeftUnit f s = kleisliCompose interactIdentity f s == f s

-- | Right unit law (Agda 'kleisli-right-unit').
kleisliRightUnit :: KleisliArrow -> ThermodynamicState -> Bool
kleisliRightUnit f s = kleisliCompose f interactIdentity s == f s

-- | Composition preserves admissibility when both legs succeed admissibly.
kleisliComposeWellTypedAt :: KleisliArrow -> KleisliArrow -> ThermodynamicState -> Bool
kleisliComposeWellTypedAt f g s =
  case (f s, kleisliCompose f g s) of
    (Just s', Just s'')
      -> admissibleStep s s' && admissibleStep s' s''
    _ -> True

-- | Left and right units agree on endpoints when both compose (Coq coherence).
kleisliCoherenceUnits :: KleisliArrow -> ThermodynamicState -> Bool
kleisliCoherenceUnits f s =
  case (kleisliCompose interactIdentity f s, kleisliCompose f interactIdentity s) of
    (Just g, Just h) -> g == h
    _                -> True

-- | Physics GREEN unauthorized on this scaffold.
chemPhysicsGreen :: Bool
chemPhysicsGreen = False

-- | Lean/Coq: @chem_physics_green_false@.
chemPhysicsGreenFalse :: Bool
chemPhysicsGreenFalse = not chemPhysicsGreen

-- | Production wiring stays open (CAT-00 lift only).
kleisliInteractProductionWired :: Bool
kleisliInteractProductionWired = False

-- | Lean/Coq: @kleisli_interact_production_wired_false@.
kleisliInteractProductionWiredFalse :: Bool
kleisliInteractProductionWiredFalse = not kleisliInteractProductionWired

-- | Catalog witness: meso chemistry Kleisli Interact module present.
kleisliInteractModuleWitness :: Bool
kleisliInteractModuleWitness = True
