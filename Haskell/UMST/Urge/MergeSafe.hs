-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.MergeSafe
-- Description : Meso acting Urge — §4 / §12 federated history merge safety.
--
-- History merge **is** 'mergeSafePred' on typed history objects; honest 'Err'
-- on mismatch — no CRDT fork. Predicate mirrors Lean @Memory.Federation.mergeSafePred@
-- (import-only pin). Composes 'excitementSelect' — no local argmin re-derivation.
--
-- Sole physics axiom remains on Lean @LandauerLaw@ (cited, not restated).
-- Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives on
-- @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.MergeSafe
  ( -- * History memory carriers (parallel to Rust HistoryObject)
    HistoryMemoryEntry (..)
  , HistoryObject (..)
  , toMemoryEntry
    -- * Merge-safe predicate (L-M5 / GMD-8 mirror)
  , mergeSafePred
  , historyMergeSafePred
  , historyMergeSafePredEqImported
    -- * Honest merge attempt (no CRDT auto-merge)
  , MergeRefusal (..)
  , mergeHistoryAttempt
  , mergeHistoryAttemptOk
  , mergeHistoryAttemptCommitErr
  , mergeHistoryAttemptTheoremErr
  , mergeHistoryAttemptAdmitsPred
    -- * Computational verdict (honest refuse on mismatch)
  , MergeSafeVerdict (..)
  , mergeSafe
  , mergeSafeAdmitIffPred
    -- * Excitement composition (no local argmin re-derivation)
  , MergeKleisliCtx (..)
  , mergeHistorySelect
  , mergeHistorySelectCtx
  , mergeHistorySelectEqExcitementSelect
  , mergeHistorySelectNoLocalArgmin
    -- * CRDT positive refuse
  , CrdtAutoMergeRefused (..)
  , refuseCrdtAutoMerge
    -- * Lean Memory.MergeSafe pin + honesty flags
  , memoryMergeSafeLeanPin
  , memoryMergeSafeLeanPinMarker
  , urgeMergeSafePhysicsGreen
  , urgeMergeSafePhysicsGreenFalse
  , mergeSafeProductionWired
  , mergeSafeProductionWiredFalse
  , mergeSafeHistoryMarker
  , mergeSafeModuleWitness
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , excitementSelect
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: History memory carriers (parallel to Rust HistoryObject)
-- ---------------------------------------------------------------------------

-- | Federated history object: content-addressed snapshot + theorem registry id.
data HistoryObject = HistoryObject
  { historySnapshot :: !HistorySnapshot
  , historyTheoremId :: !String
  } deriving (Show, Eq)

-- | Minimal history memory row (parallel to Rust @MemoryEntry@ theorem-bound row).
data HistoryMemoryEntry = HistoryMemoryEntry
  { memoryId        :: !Int
  , memoryTheoremId :: !String
  } deriving (Show, Eq)

-- | Embed history object into federated memory entry (imported carrier — no fork).
toMemoryEntry :: HistoryObject -> HistoryMemoryEntry
toMemoryEntry h = HistoryMemoryEntry
  { memoryId        = historyCommitId (historySnapshot h)
  , memoryTheoremId = historyTheoremId h
  }

-- ---------------------------------------------------------------------------
-- SECTION 2: Merge-safe predicate (L-M5 / GMD-8 mirror)
-- ---------------------------------------------------------------------------

-- | Merge-safe predicate: same canonical content id and same theorem binding.
mergeSafePred :: HistoryMemoryEntry -> HistoryMemoryEntry -> Bool
mergeSafePred eA eB =
  memoryId eA == memoryId eB && memoryTheoremId eA == memoryTheoremId eB

-- | History merge-safe predicate: imported 'mergeSafePred' on embedded entries.
historyMergeSafePred :: HistoryObject -> HistoryObject -> Bool
historyMergeSafePred hA hB = mergeSafePred (toMemoryEntry hA) (toMemoryEntry hB)

-- | Definitional witness: history predicate is imported 'mergeSafePred'.
historyMergeSafePredEqImported :: HistoryObject -> HistoryObject -> Bool
historyMergeSafePredEqImported hA hB =
  historyMergeSafePred hA hB == mergeSafePred (toMemoryEntry hA) (toMemoryEntry hB)

-- ---------------------------------------------------------------------------
-- SECTION 3: Honest merge attempt (no CRDT auto-merge)
-- ---------------------------------------------------------------------------

-- | Refusal reasons for history merge (extensional mismatch only).
data MergeRefusal
  = CommitMismatch
  | TheoremMismatch
  deriving (Show, Eq)

-- | Merge attempt: 'Right' when merge-safe; 'Left' with honest reason otherwise.
mergeHistoryAttempt :: HistoryObject -> HistoryObject -> Either MergeRefusal HistoryObject
mergeHistoryAttempt hA hB
  | historyCommitId (historySnapshot hA) /= historyCommitId (historySnapshot hB) =
      Left CommitMismatch
  | historyTheoremId hA /= historyTheoremId hB =
      Left TheoremMismatch
  | otherwise =
      Right hA

-- | Successful merge when commit ids and theorem ids agree.
mergeHistoryAttemptOk :: HistoryObject -> HistoryObject -> Bool
mergeHistoryAttemptOk hA hB =
  mergeHistoryAttempt hA hB == Right hA

-- | Commit mismatch yields honest 'CommitMismatch' refusal.
mergeHistoryAttemptCommitErr :: HistoryObject -> HistoryObject -> Bool
mergeHistoryAttemptCommitErr hA hB =
  historyCommitId (historySnapshot hA) /= historyCommitId (historySnapshot hB)
  && mergeHistoryAttempt hA hB == Left CommitMismatch

-- | Theorem mismatch yields honest 'TheoremMismatch' refusal.
mergeHistoryAttemptTheoremErr :: HistoryObject -> HistoryObject -> Bool
mergeHistoryAttemptTheoremErr hA hB =
  historyCommitId (historySnapshot hA) == historyCommitId (historySnapshot hB)
  && historyTheoremId hA /= historyTheoremId hB
  && mergeHistoryAttempt hA hB == Left TheoremMismatch

-- | Successful merge attempt implies merge-safe predicate.
mergeHistoryAttemptAdmitsPred :: HistoryObject -> HistoryObject -> Bool
mergeHistoryAttemptAdmitsPred hA hB =
  case mergeHistoryAttempt hA hB of
    Right _ -> historyMergeSafePred hA hB
    Left _  -> True

-- ---------------------------------------------------------------------------
-- SECTION 4: Computational verdict (honest refuse on mismatch)
-- ---------------------------------------------------------------------------

-- | Merge-safe computational verdict — no silent CRDT swallow.
data MergeSafeVerdict
  = MergeSafeAdmit
  | MergeSafeRefuseMismatch
  deriving (Show, Eq)

-- | Computational merge-safe check — honest refuse on any mismatch.
mergeSafe :: HistoryMemoryEntry -> HistoryMemoryEntry -> MergeSafeVerdict
mergeSafe left right
  | mergeSafePred left right = MergeSafeAdmit
  | otherwise                = MergeSafeRefuseMismatch

-- | Admit verdict iff merge-safe predicate holds.
mergeSafeAdmitIffPred :: HistoryMemoryEntry -> HistoryMemoryEntry -> Bool
mergeSafeAdmitIffPred left right =
  (mergeSafe left right == MergeSafeAdmit) == mergeSafePred left right

-- ---------------------------------------------------------------------------
-- SECTION 5: Excitement composition (no local argmin re-derivation)
-- ---------------------------------------------------------------------------

-- | Context for merge Kleisli selection: prior head + admissible successors.
data MergeKleisliCtx = MergeKleisliCtx
  { mergePrior       :: !ThermodynamicState
  , mergeSuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Merge history selection composes 'excitementSelect' — not a second argmin.
mergeHistorySelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
mergeHistorySelect = excitementSelect

-- | Contextual merge selection — same selector, no re-derivation.
mergeHistorySelectCtx :: MergeKleisliCtx -> Either ExcitementResidue HistoryCandidate
mergeHistorySelectCtx ctx =
  excitementSelect (mergePrior ctx) (mergeSuccessors ctx)

-- | Definitional witness: merge selection API is 'excitementSelect'.
mergeHistorySelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
mergeHistorySelectEqExcitementSelect src cands =
  mergeHistorySelect src cands == excitementSelect src cands

-- | Merge selector re-uses 'excitementSelect' — no Urge-local argmin.
mergeHistorySelectNoLocalArgmin :: MergeKleisliCtx -> Bool
mergeHistorySelectNoLocalArgmin ctx =
  mergeHistorySelectCtx ctx
    == excitementSelect (mergePrior ctx) (mergeSuccessors ctx)

-- ---------------------------------------------------------------------------
-- SECTION 6: CRDT positive refuse
-- ---------------------------------------------------------------------------

-- | Positive refuse tag: CRDT auto-merge is forbidden.
data CrdtAutoMergeRefused = CrdtAutoMergeRefused deriving (Show, Eq)

-- | CRDT auto-merge refusal witness (not silent swallow).
refuseCrdtAutoMerge :: CrdtAutoMergeRefused
refuseCrdtAutoMerge = CrdtAutoMergeRefused

-- ---------------------------------------------------------------------------
-- SECTION 7: Lean Memory.MergeSafe pin + honesty flags
-- ---------------------------------------------------------------------------

-- | Conceptual pin — Lean @Memory.MergeSafe@ (proof import-only).
memoryMergeSafeLeanPin :: Int
memoryMergeSafeLeanPin = 0

-- | Lean/Coq: @memory_merge_safe_lean_pin_marker@.
memoryMergeSafeLeanPinMarker :: Bool
memoryMergeSafeLeanPinMarker = memoryMergeSafeLeanPin == 0

-- | Physics GREEN unauthorized on this scaffold.
urgeMergeSafePhysicsGreen :: Bool
urgeMergeSafePhysicsGreen = False

-- | Lean/Coq: @urge_merge_safe_physics_green_false@.
urgeMergeSafePhysicsGreenFalse :: Bool
urgeMergeSafePhysicsGreenFalse = not urgeMergeSafePhysicsGreen

-- | Production wiring stays open (meso lift only).
mergeSafeProductionWired :: Bool
mergeSafeProductionWired = False

-- | Lean/Coq: @merge_safe_production_wired_false@.
mergeSafeProductionWiredFalse :: Bool
mergeSafeProductionWiredFalse = not mergeSafeProductionWired

-- | History merge marker (catalog pin).
mergeSafeHistoryMarker :: Int
mergeSafeHistoryMarker = 1

-- | Catalog witness: meso Urge MergeSafe module present.
mergeSafeModuleWitness :: Bool
mergeSafeModuleWitness = True
