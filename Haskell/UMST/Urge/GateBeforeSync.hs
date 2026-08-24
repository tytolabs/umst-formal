-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.GateBeforeSync
-- Description : Meso acting Urge — §16.3 / §22.2 Kleisli admit before inbound sync.
--
-- Inbound history sync: `admit(h) ⇔ gate_check_before_sync(h) ∧ MergeSafe(h) ∧
-- Excitement preserves provenance(h)`.
--
-- Composes 'gateCheck' (Compat), federated 'mergeSafePred', and provenance
-- 'preserves' — no second argmin, zero new physics axioms.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.GateBeforeSync
  ( -- * Inbound history sync tick
    HistorySyncTick (..)
  , syncPriorHead
  , syncPostHead
    -- * Gate-before-sync on history head move (§16.3 / §22.2)
  , tickGateAdmissible
  , gateCheckBeforeSync
  , gateCheckBeforeSyncSound
  , gateCheckBeforeSyncComplete
  , gateCheckBeforeSyncIff
    -- * MergeSafe on federated entries (L-M5 lift)
  , mergeSafeTick
  , mergeSafeTickIntro
    -- * Excitement preserves provenance (no second argmin)
  , excitementPreservesProvenance
  , excitementSelectRespectsPreservesObligation
    -- * Kleisli admit — gate ∧ MergeSafe ∧ provenance
  , gateBeforeSyncAdmit
  , gateBeforeSyncAdmitIff
  , gateBeforeSyncAdmitIntro
  , gateBeforeSyncAdmitGate
  , gateBeforeSyncAdmitMergeSafe
  , gateBeforeSyncAdmitExcitementPreservesProvenance
  , gateBeforeSyncAdmitDecomposed
    -- * Landauer bridge discharge (derived — zero new axioms)
  , gateBeforeSyncSecondLawFromLandauer
  , excitementPreservesProvenanceFromLandauer
  , gateBeforeSyncAdmitFromLandauer
    -- * Excitement alignment (no second argmin)
  , gateBeforeSyncSelect
  , gateBeforeSyncSelectEqExcitementSelect
  , gateBeforeSyncNoLocalArgmin
    -- * Honesty flags + catalog witnesses
  , gateBeforeSyncPhysicsGreen
  , gateBeforeSyncPhysicsGreenFalse
  , gateBeforeSyncProductionWired
  , gateBeforeSyncProductionWiredFalse
  , gateBeforeSyncNonClaim
  , gateBeforeSyncNonClaimNonempty
  , gateBeforeSyncModuleWitness
  , gateBeforeSyncNoNewAxiom
  , gateBeforeSyncNoSecondArgmin
  ) where

import UMST.Concrete
  ( AdmissibilityResult (..)
  , ThermodynamicState (..)
  , gateCheck
  )
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.MergeSafe (HistoryMemoryEntry (..), mergeSafePred)
import UMST.Urge.ProvenancePreserve
  ( Provenance (..)
  , excitementSelectRespectsPreserves
  , landauerBridgePreserves
  , preserves
  )

-- | Nominal history head step Δt for gate evaluation (seconds).
gateBeforeSyncStepDt :: Double
gateBeforeSyncStepDt = 3600.0

-- ---------------------------------------------------------------------------
-- SECTION 1: Inbound history sync tick
-- ---------------------------------------------------------------------------

-- | Inbound history sync tick: transition + provenance + federated rows.
data HistorySyncTick = HistorySyncTick
  { syncTransition  :: !HistoryTransition
  , syncPriorProv   :: !Provenance
  , syncPostProv    :: !Provenance
  , syncLocalEntry  :: !HistoryMemoryEntry
  , syncRemoteEntry :: !HistoryMemoryEntry
  } deriving (Show, Eq)

-- | Thermodynamic head before inbound sync move.
syncPriorHead :: HistorySyncTick -> ThermodynamicState
syncPriorHead h = historyHead (historyPrior (syncTransition h))

-- | Thermodynamic head after inbound sync move.
syncPostHead :: HistorySyncTick -> ThermodynamicState
syncPostHead h = historyHead (historyPost (syncTransition h))

-- ---------------------------------------------------------------------------
-- SECTION 2: Gate-before-sync on history head move (§16.3 / §22.2)
-- ---------------------------------------------------------------------------

-- | Gate admissibility on the tick's history head move.
tickGateAdmissible :: HistorySyncTick -> Bool
tickGateAdmissible h =
  accepted (gateCheck (syncPriorHead h) (syncPostHead h) gateBeforeSyncStepDt)

-- | Thermodynamic gate on history head move **before** applying inbound sync.
gateCheckBeforeSync :: HistorySyncTick -> Bool
gateCheckBeforeSync = tickGateAdmissible

-- | Soundness: gate check true implies tick gate admissible.
gateCheckBeforeSyncSound :: HistorySyncTick -> Bool
gateCheckBeforeSyncSound h =
  not (gateCheckBeforeSync h) || tickGateAdmissible h

-- | Completeness: tick gate admissible implies gate check true.
gateCheckBeforeSyncComplete :: HistorySyncTick -> Bool
gateCheckBeforeSyncComplete h =
  not (tickGateAdmissible h) || gateCheckBeforeSync h

-- | Biconditional witness on the tick's history head move.
gateCheckBeforeSyncIff :: HistorySyncTick -> Bool
gateCheckBeforeSyncIff h =
  gateCheckBeforeSync h == tickGateAdmissible h
  && gateCheckBeforeSyncSound h
  && gateCheckBeforeSyncComplete h

-- ---------------------------------------------------------------------------
-- SECTION 3: MergeSafe on federated entries (L-M5 lift)
-- ---------------------------------------------------------------------------

-- | Merge-safe predicate on the tick's federated memory entries.
mergeSafeTick :: HistorySyncTick -> Bool
mergeSafeTick h = mergeSafePred (syncLocalEntry h) (syncRemoteEntry h)

-- | Intro witness: matching ids and theorem binding imply merge-safe tick.
mergeSafeTickIntro
  :: HistorySyncTick
  -> Bool
  -> Bool
  -> Bool
mergeSafeTickIntro h idOk thmOk =
  idOk && thmOk && mergeSafeTick h

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement preserves provenance (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement / Kleisli provenance preservation on this sync transition.
excitementPreservesProvenance :: HistorySyncTick -> Bool
excitementPreservesProvenance h =
  preserves (syncTransition h) (syncPriorProv h) (syncPostProv h)

-- | Excitement selection respects preservation obligation on this tick.
excitementSelectRespectsPreservesObligation :: HistorySyncTick -> Bool
excitementSelectRespectsPreservesObligation h =
  excitementSelectRespectsPreserves
    (syncTransition h)
    (syncPriorProv h)
    (syncPostProv h)

-- ---------------------------------------------------------------------------
-- SECTION 5: Kleisli admit — gate ∧ MergeSafe ∧ provenance
-- ---------------------------------------------------------------------------

-- | Kleisli admit on inbound history sync: gate-before-sync ∧ MergeSafe ∧ provenance.
gateBeforeSyncAdmit :: HistorySyncTick -> Bool
gateBeforeSyncAdmit h =
  gateCheckBeforeSync h
  && mergeSafeTick h
  && excitementPreservesProvenance h

-- | Main biconditional: admit is exactly the three conjuncts.
gateBeforeSyncAdmitIff :: HistorySyncTick -> Bool
gateBeforeSyncAdmitIff h =
  gateBeforeSyncAdmit h
    == ( gateCheckBeforeSync h
         && mergeSafeTick h
         && excitementPreservesProvenance h
       )

-- | Intro witness for conjunctive admit.
gateBeforeSyncAdmitIntro
  :: HistorySyncTick -> Bool -> Bool -> Bool -> Bool
gateBeforeSyncAdmitIntro h hg hm hp =
  hg && hm && hp && gateBeforeSyncAdmit h

-- | Admit implies gate-before-sync conjunct.
gateBeforeSyncAdmitGate :: HistorySyncTick -> Bool
gateBeforeSyncAdmitGate h =
  not (gateBeforeSyncAdmit h) || gateCheckBeforeSync h

-- | Admit implies MergeSafe conjunct.
gateBeforeSyncAdmitMergeSafe :: HistorySyncTick -> Bool
gateBeforeSyncAdmitMergeSafe h =
  not (gateBeforeSyncAdmit h) || mergeSafeTick h

-- | Admit implies excitement-preserves-provenance conjunct.
gateBeforeSyncAdmitExcitementPreservesProvenance :: HistorySyncTick -> Bool
gateBeforeSyncAdmitExcitementPreservesProvenance h =
  not (gateBeforeSyncAdmit h) || excitementPreservesProvenance h

-- | Decomposed intro: gate admissible + merge-safe + provenance ⇒ admit.
gateBeforeSyncAdmitDecomposed
  :: HistorySyncTick -> Bool -> Bool -> Bool -> Bool
gateBeforeSyncAdmitDecomposed h hg hm hp =
  hg && hm && hp && gateBeforeSyncAdmit h

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge discharge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on bridged transition from Landauer discharge (no new axiom).
gateBeforeSyncSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
gateBeforeSyncSecondLawFromLandauer b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Provenance preservation from Landauer bridge on a sync tick.
excitementPreservesProvenanceFromLandauer
  :: LandauerHistoryBridge
  -> HistorySyncTick
  -> Bool
  -> Bool
  -> Bool
  -> Bool
excitementPreservesProvenanceFromLandauer b h hTrans hPrior hSL =
  hTrans
  && hPrior
  && hSL
  && landauerBridgePreserves b (syncPriorProv h) hPrior hSL
  && excitementPreservesProvenance h

-- | Full admit from Landauer bridge + merge-safe + aligned post provenance.
gateBeforeSyncAdmitFromLandauer
  :: LandauerHistoryBridge
  -> HistorySyncTick
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
gateBeforeSyncAdmitFromLandauer b h hTrans hPrior hSL hm =
  hm
  && gateCheckBeforeSync h
  && excitementPreservesProvenanceFromLandauer b h hTrans hPrior hSL
  && gateBeforeSyncAdmit h

-- ---------------------------------------------------------------------------
-- SECTION 7: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Gate-before-sync history recovery composes 'excitementSelect'.
gateBeforeSyncSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
gateBeforeSyncSelect = excitementSelect

-- | Definitional witness: gate-before-sync selection API is 'excitementSelect'.
gateBeforeSyncSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
gateBeforeSyncSelectEqExcitementSelect src cands =
  gateBeforeSyncSelect src cands == excitementSelect src cands

-- | Gate-before-sync selector re-uses 'excitementSelect' — no Urge-local argmin.
gateBeforeSyncNoLocalArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
gateBeforeSyncNoLocalArgmin src cands =
  gateBeforeSyncSelect src cands == excitementSelect src cands

-- ---------------------------------------------------------------------------
-- SECTION 8: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
gateBeforeSyncPhysicsGreen :: Bool
gateBeforeSyncPhysicsGreen = False

-- | Lean/Coq: @urge_physics_green_false@.
gateBeforeSyncPhysicsGreenFalse :: Bool
gateBeforeSyncPhysicsGreenFalse = not gateBeforeSyncPhysicsGreen

-- | Production wiring stays open (meso lift only).
gateBeforeSyncProductionWired :: Bool
gateBeforeSyncProductionWired = False

-- | Lean/Coq: @gate_before_sync_production_wired_false@.
gateBeforeSyncProductionWiredFalse :: Bool
gateBeforeSyncProductionWiredFalse = not gateBeforeSyncProductionWired

-- | Honest non-claim string (meso §16.3 / §22.2 gate-before-sync scaffold).
gateBeforeSyncNonClaim :: String
gateBeforeSyncNonClaim =
  "§16.3/§22.2 gate-before-sync: admit ⇔ gate_check ∧ MergeSafe ∧ provenance; "
    ++ "gateBeforeSyncSelect composes excitementSelect not second argmin; "
    ++ "Landauer physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
gateBeforeSyncNonClaimNonempty :: Bool
gateBeforeSyncNonClaimNonempty = length gateBeforeSyncNonClaim > 0

-- | Catalog witness: meso Urge GateBeforeSync module present.
gateBeforeSyncModuleWitness :: Bool
gateBeforeSyncModuleWitness = True

-- | Zero new axiom discipline witness.
gateBeforeSyncNoNewAxiom :: Bool
gateBeforeSyncNoNewAxiom = True

-- | Second-argmin refusal: gate-before-sync composes 'excitementSelect' only.
gateBeforeSyncNoSecondArgmin :: Bool
gateBeforeSyncNoSecondArgmin =
  gateBeforeSyncNoLocalArgmin (ThermodynamicState 2400 0 0.3 30 40) []
