-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.AppendOnly
-- Description : Meso acting Urge — §17.6 append-only admitted history invariant.
--
-- Admitted history is append-only; silent rewrite refused as an honest 'Bool'
-- witness. Self-healing adds an Excitement arrow; it does not mutate prior
-- admitted objects. Composes 'excitementSelect' — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw@ (cited, not restated).
-- Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives on
-- @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.AppendOnly
  ( -- * Append-only commit moves (§17.6)
    appendOnlyCommitMove
  , appendOnlyInvariant
  , silentRewrite
  , silentRewriteRefused
  , appendOnlyNotSilentRewrite
    -- * Admitted append-only transitions
  , appendOnlyAdmittedTransition
  , appendOnlyHistoryChain
  , appendOnlyHistoryChainRefusesSilentRewrite
    -- * Recovery / self-heal append-only
  , recoveryAppendOnly
  , silentRewriteSnapshots
  , recoveryAppendOnlyRefusesSilentRewrite
  , selfHealAppendOnly
  , selfHealAppendOnlyEqAppendOnlyInvariant
  , selfHealNotSilentRewrite
    -- * Landauer bridge (derived — zero new axioms)
  , appendOnlyAdmittedFromLandauer
  , silentRewriteRefusedFromLandauer
    -- * Excitement composition (no second argmin)
  , AppendOnlyRecoveryCtx (..)
  , appendOnlyRecoverySelect
  , appendOnlyRecoverySelectCtx
  , appendOnlyRecoverySelectEqExcitementSelect
  , appendOnlyRecoverySelectNoLocalArgmin
    -- * Honesty flags + catalog witnesses
  , urgeAppendOnlyPhysicsGreen
  , urgeAppendOnlyPhysicsGreenFalse
  , appendOnlyProductionWired
  , appendOnlyProductionWiredFalse
  , appendOnlyModuleWitness
  , appendOnlySilentRewriteRefused
  , appendOnlyNoNewAxiom
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admissibleHistoryTransition
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Append-only commit moves (§17.6)
-- ---------------------------------------------------------------------------

-- | Monotone commit-id move: prior strictly before post (append-only head).
appendOnlyCommitMove :: HistoryTransition -> Bool
appendOnlyCommitMove t =
  historyCommitId (historyPrior t) < historyCommitId (historyPost t)

-- | §17.6 append-only invariant on a single admitted transition.
appendOnlyInvariant :: HistoryTransition -> Bool
appendOnlyInvariant = appendOnlyCommitMove

-- | Silent rewrite: post does not strictly extend prior commit id.
silentRewrite :: HistoryTransition -> Bool
silentRewrite t =
  historyCommitId (historyPost t) <= historyCommitId (historyPrior t)

-- | Silent rewrite refused when append-only discipline holds.
silentRewriteRefused :: HistoryTransition -> Bool
silentRewriteRefused t =
  not (appendOnlyCommitMove t) || not (silentRewrite t)

-- | Append-only and silent rewrite are mutually exclusive.
appendOnlyNotSilentRewrite :: HistoryTransition -> Bool
appendOnlyNotSilentRewrite t =
  appendOnlyCommitMove t == not (silentRewrite t)

-- ---------------------------------------------------------------------------
-- SECTION 2: Admitted append-only transitions
-- ---------------------------------------------------------------------------

-- | Admitted history transition with append-only discipline (§17.6).
appendOnlyAdmittedTransition :: HistoryTransition -> Bool
appendOnlyAdmittedTransition t =
  admissibleHistoryTransition t && appendOnlyInvariant t

-- | Every transition in a chain respects append-only commit moves.
appendOnlyHistoryChain :: [HistoryTransition] -> Bool
appendOnlyHistoryChain ts = all appendOnlyCommitMove ts

-- | Chain append-only ⇒ no transition in the chain is a silent rewrite.
appendOnlyHistoryChainRefusesSilentRewrite :: [HistoryTransition] -> Bool
appendOnlyHistoryChainRefusesSilentRewrite ts =
  appendOnlyHistoryChain ts
  && all (not . silentRewrite) ts

-- ---------------------------------------------------------------------------
-- SECTION 3: Recovery / self-heal append-only
-- ---------------------------------------------------------------------------

-- | Recovery snapshot must strictly extend prior commit id (new arrow, not rewrite).
recoveryAppendOnly :: HistorySnapshot -> HistorySnapshot -> Bool
recoveryAppendOnly prior post =
  historyCommitId prior < historyCommitId post

-- | Silent rewrite on bare snapshots (no thermodynamic accounting).
silentRewriteSnapshots :: HistorySnapshot -> HistorySnapshot -> Bool
silentRewriteSnapshots prior post =
  historyCommitId post <= historyCommitId prior

-- | Recovery append-only refuses silent rewrite on snapshots.
recoveryAppendOnlyRefusesSilentRewrite
  :: HistorySnapshot -> HistorySnapshot -> Bool
recoveryAppendOnlyRefusesSilentRewrite prior post =
  not (recoveryAppendOnly prior post) || not (silentRewriteSnapshots prior post)

-- | Self-heal discipline: recovery transition obeys append-only.
selfHealAppendOnly :: HistoryTransition -> Bool
selfHealAppendOnly t =
  recoveryAppendOnly (historyPrior t) (historyPost t)

-- | Definitional witness: self-heal equals append-only invariant.
selfHealAppendOnlyEqAppendOnlyInvariant :: HistoryTransition -> Bool
selfHealAppendOnlyEqAppendOnlyInvariant t =
  selfHealAppendOnly t == appendOnlyInvariant t

-- | Self-heal transition refuses snapshot-level silent rewrite.
selfHealNotSilentRewrite :: HistoryTransition -> Bool
selfHealNotSilentRewrite t =
  recoveryAppendOnlyRefusesSilentRewrite
    (historyPrior t)
    (historyPost t)

-- ---------------------------------------------------------------------------
-- SECTION 4: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Landauer-bridged transition is append-only admitted.
appendOnlyAdmittedFromLandauer
  :: LandauerHistoryBridge -> Bool -> Bool -> Bool
appendOnlyAdmittedFromLandauer b hAppend hSL =
  hAppend
  && hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && appendOnlyCommitMove (landauerTransition b)

-- | Landauer bridge forbids silent rewrite on the bridged transition.
silentRewriteRefusedFromLandauer
  :: LandauerHistoryBridge -> Bool -> Bool -> Bool
silentRewriteRefusedFromLandauer b hAppend hSL =
  hAppend
  && hSL
  && silentRewriteRefused (landauerTransition b)

-- ---------------------------------------------------------------------------
-- SECTION 5: Excitement composition (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for append-only recovery: prior head + admissible successors.
data AppendOnlyRecoveryCtx = AppendOnlyRecoveryCtx
  { appendOnlyPrior      :: !ThermodynamicState
  , appendOnlySuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Self-heal recovery composes 'excitementSelect' — not a second argmin.
appendOnlyRecoverySelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
appendOnlyRecoverySelect = excitementSelect

-- | Contextual append-only recovery — same selector, no re-derivation.
appendOnlyRecoverySelectCtx
  :: AppendOnlyRecoveryCtx
  -> Either ExcitementResidue HistoryCandidate
appendOnlyRecoverySelectCtx ctx =
  excitementSelect (appendOnlyPrior ctx) (appendOnlySuccessors ctx)

-- | Definitional witness: recovery API is 'excitementSelect'.
appendOnlyRecoverySelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
appendOnlyRecoverySelectEqExcitementSelect src cands =
  appendOnlyRecoverySelect src cands == excitementSelect src cands

-- | Recovery selector re-uses 'excitementSelect' — no Urge-local argmin.
appendOnlyRecoverySelectNoLocalArgmin :: AppendOnlyRecoveryCtx -> Bool
appendOnlyRecoverySelectNoLocalArgmin ctx =
  appendOnlyRecoverySelectCtx ctx
    == excitementSelect (appendOnlyPrior ctx) (appendOnlySuccessors ctx)

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
urgeAppendOnlyPhysicsGreen :: Bool
urgeAppendOnlyPhysicsGreen = False

-- | Lean/Coq: @urge_append_only_physics_green_false@.
urgeAppendOnlyPhysicsGreenFalse :: Bool
urgeAppendOnlyPhysicsGreenFalse = not urgeAppendOnlyPhysicsGreen

-- | Production wiring stays open (meso lift only).
appendOnlyProductionWired :: Bool
appendOnlyProductionWired = False

-- | Lean/Coq: @append_only_production_wired_false@.
appendOnlyProductionWiredFalse :: Bool
appendOnlyProductionWiredFalse = not appendOnlyProductionWired

-- | Catalog witness: meso Urge AppendOnly module present.
appendOnlyModuleWitness :: Bool
appendOnlyModuleWitness = True

-- | §17.6 named obligation: append-only invariant refuses silent rewrite.
appendOnlySilentRewriteRefused :: HistoryTransition -> Bool
appendOnlySilentRewriteRefused t =
  not (appendOnlyInvariant t) || not (silentRewrite t)

-- | Zero new axiom discipline witness.
appendOnlyNoNewAxiom :: Bool
appendOnlyNoNewAxiom = True
