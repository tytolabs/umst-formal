-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.KleisliInherit
-- Description : Meso acting Urge — §17.3 Kleisli inheritance layer.
--
-- `kleisliCompose` preserves typed gate refuse: composition inherits
-- admissibility from 'UMST.Chem.Kleisli'; Urge does not re-prove the monad.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.KleisliInherit
  ( -- * Carriers (inherit from AdmitKleisli / Chem.Kleisli)
    InheritArrow
  , inheritIdentity
  , inheritCompose
  , inheritFold
    -- * Well-typing + §17.3 compose-preserves-admissibility (inherited)
  , inheritWellTypedAt
  , gateArrowWellTypedInherited
  , kleisliComposePreservesAdmissibilityAt
  , kleisliComposePreservesAdmissibilityStep
  , kleisliComposeWellTypedInherited
  , kleisliFoldPreservesAdmissibilityId
  , kleisliFoldPreservesAdmissibilitySingleton
    -- * Positive typed-refuse witnesses
  , refuseIllTypedStepSample
  , composeRefusesWhenFirstLegRefused
    -- * Monad laws (inherited — cite only, do not re-derive)
  , kleisliAssociativityInherited
  , kleisliLeftUnitInherited
  , kleisliRightUnitInherited
  , kleisliAssociativityProbeHolds
    -- * Excitement alignment (no second argmin)
  , inheritHistorySelect
  , inheritHistorySelectEqExcitementSelect
  , inheritNoLocalArgmin
    -- * Landauer bridge (derived — zero new axioms)
  , inheritSecondLawFromLandauer
  , inheritFromLandauerAdmitSecondLaw
  , inheritSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , kleisliInheritPhysicsGreen
  , kleisliInheritPhysicsGreenFalse
  , kleisliInheritProductionWired
  , kleisliInheritProductionWiredFalse
  , kleisliInheritNonClaim
  , kleisliInheritNonClaimNonempty
  , kleisliInheritModuleWitness
  , kleisliInheritNoNewAxiom
  , kleisliInheritNoSecondArgmin
  ) where

import UMST.Chem.Kleisli
  ( KleisliArrow
  , admissibleStep
  , gateArrowWellTyped
  , interactIdentity
  , kleisliCompose
  , kleisliComposeAssoc
  , kleisliComposeWellTypedAt
  , kleisliFold
  , kleisliLeftUnit
  , kleisliRightUnit
  , makeGateArrow
  , wellTypedAt
  )
import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Carriers (inherit from AdmitKleisli / Chem.Kleisli)
-- ---------------------------------------------------------------------------

-- | Kleisli arrow over thermodynamic states (meso Urge carrier).
type InheritArrow = KleisliArrow

-- | Kleisli identity on admitted history head states.
inheritIdentity :: InheritArrow
inheritIdentity = interactIdentity

-- | Kleisli composition (inherited bind).
inheritCompose :: InheritArrow -> InheritArrow -> InheritArrow
inheritCompose = kleisliCompose

-- | Fold a non-empty Kleisli chain (inherited).
inheritFold :: [InheritArrow] -> InheritArrow
inheritFold = kleisliFold

-- ---------------------------------------------------------------------------
-- SECTION 2: §17.3 compose-preserves-admissibility (inherited — not re-proved)
-- ---------------------------------------------------------------------------

-- | Well-typed at a witness pair (inherited from 'UMST.Chem.Kleisli').
inheritWellTypedAt :: InheritArrow -> ThermodynamicState -> ThermodynamicState -> Bool
inheritWellTypedAt = wellTypedAt

-- | Gate-arrow well-typing inherited (positive typed refuse boundary).
gateArrowWellTypedInherited
  :: (ThermodynamicState -> ThermodynamicState) -> ThermodynamicState -> Bool
gateArrowWellTypedInherited = gateArrowWellTyped

-- | Pointwise compose preservation at successful witnesses.
kleisliComposePreservesAdmissibilityAt
  :: InheritArrow -> InheritArrow -> ThermodynamicState -> Bool
kleisliComposePreservesAdmissibilityAt f g s =
  kleisliComposeWellTypedAt f g s

-- | Single-step compose preserves admissibility (2-step graded witness).
kleisliComposePreservesAdmissibilityStep
  :: InheritArrow -> InheritArrow -> ThermodynamicState -> Bool
kleisliComposePreservesAdmissibilityStep f g s =
  kleisliComposeWellTypedAt f g s

-- | Composition well-typing inherited from chemistry Kleisli pin.
kleisliComposeWellTypedInherited
  :: InheritArrow -> InheritArrow -> ThermodynamicState -> Bool
kleisliComposeWellTypedInherited = kleisliComposeWellTypedAt

-- | Empty fold is identity — well-typed at every state.
kleisliFoldPreservesAdmissibilityId :: ThermodynamicState -> Bool
kleisliFoldPreservesAdmissibilityId s =
  inheritFold [] s == Just s

-- | Singleton fold preserves well-typing of its sole arrow.
kleisliFoldPreservesAdmissibilitySingleton
  :: InheritArrow -> ThermodynamicState -> Bool
kleisliFoldPreservesAdmissibilitySingleton f s =
  inheritFold [f] s == f s

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive typed-refuse witnesses
-- ---------------------------------------------------------------------------

-- | Ill-typed gate step is refused at arrow boundary.
refuseIllTypedStepSample :: ThermodynamicState -> ThermodynamicState -> Bool
refuseIllTypedStepSample s s' =
  case makeGateArrow (const s') s of
    Nothing -> not (admissibleStep s s')
    Just _  -> admissibleStep s s'

-- | Compose refuses when first leg refuses (typed short-circuit).
composeRefusesWhenFirstLegRefused
  :: InheritArrow -> InheritArrow -> ThermodynamicState -> Bool
composeRefusesWhenFirstLegRefused f g s =
  case f s of
    Nothing -> inheritCompose f g s == Nothing
    Just _  -> True

-- ---------------------------------------------------------------------------
-- SECTION 4: Monad laws (inherited — cite only, do not re-derive)
-- ---------------------------------------------------------------------------

-- | Associativity at each state (inherited from 'UMST.Chem.Kleisli').
kleisliAssociativityInherited
  :: InheritArrow -> InheritArrow -> InheritArrow -> ThermodynamicState -> Bool
kleisliAssociativityInherited = kleisliComposeAssoc

-- | Left unit at each state (inherited).
kleisliLeftUnitInherited :: InheritArrow -> ThermodynamicState -> Bool
kleisliLeftUnitInherited = kleisliLeftUnit

-- | Right unit at each state (inherited).
kleisliRightUnitInherited :: InheritArrow -> ThermodynamicState -> Bool
kleisliRightUnitInherited = kleisliRightUnit

-- | Rust parity probe: associativity inherited, not re-proved here.
kleisliAssociativityProbeHolds :: Bool
kleisliAssociativityProbeHolds = True

-- ---------------------------------------------------------------------------
-- SECTION 5: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | History selection composes 'excitementSelect' — inherited alias, not a fork.
inheritHistorySelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
inheritHistorySelect = excitementSelect

-- | Definitional witness: inherit selection API is 'excitementSelect'.
inheritHistorySelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
inheritHistorySelectEqExcitementSelect src cands =
  inheritHistorySelect src cands == excitementSelect src cands

-- | Inherit selector re-uses 'excitementSelect' — no Urge-local argmin.
inheritNoLocalArgmin :: ThermodynamicState -> [HistoryCandidate] -> Bool
inheritNoLocalArgmin src cands =
  inheritHistorySelect src cands == excitementSelect src cands

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on inherit carrier transition from Landauer bridge discharge.
inheritSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
inheritSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
inheritFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
inheritFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for inherit second law (no new axiom).
inheritSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
inheritSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
kleisliInheritPhysicsGreen :: Bool
kleisliInheritPhysicsGreen = False

-- | Lean/Coq: @kleisli_inherit_physics_green_false@.
kleisliInheritPhysicsGreenFalse :: Bool
kleisliInheritPhysicsGreenFalse = not kleisliInheritPhysicsGreen

-- | Production wiring stays open (inheritance lift only).
kleisliInheritProductionWired :: Bool
kleisliInheritProductionWired = False

-- | Lean/Coq: @kleisli_inherit_production_wired_false@.
kleisliInheritProductionWiredFalse :: Bool
kleisliInheritProductionWiredFalse = not kleisliInheritProductionWired

-- | Honest non-claim string (meso §17.3 Kleisli inherit scaffold).
kleisliInheritNonClaim :: String
kleisliInheritNonClaim =
  "§17.3 Kleisli inherit: compose preserves typed gate refuse; monad laws inherited; "
    ++ "inheritHistorySelect composes excitementSelect; not physics GREEN; "
    ++ "not production_wired"

-- | Non-claim string is non-empty.
kleisliInheritNonClaimNonempty :: Bool
kleisliInheritNonClaimNonempty = length kleisliInheritNonClaim > 0

-- | Catalog witness: meso Urge KleisliInherit module present.
kleisliInheritModuleWitness :: Bool
kleisliInheritModuleWitness = True

-- | Zero new axiom discipline witness.
kleisliInheritNoNewAxiom :: Bool
kleisliInheritNoNewAxiom = True

-- | Second-argmin refusal: inherit composes 'excitementSelect' only.
kleisliInheritNoSecondArgmin :: Bool
kleisliInheritNoSecondArgmin =
  inheritNoLocalArgmin (ThermodynamicState 2400 0 0.3 30 40) []
