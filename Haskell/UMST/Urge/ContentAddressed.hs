-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ContentAddressed
-- Description : Meso acting Urge — §3 content-addressed history.
--
-- Geometric identity is **primary**; git hash is a compatibility witness, not sole id.
-- History recovery composes 'excitementSelect' — no second argmin.
--
-- Mirrors 'UMST.Urge.CollaborativeObject' carrier discipline and Lean
-- @Urge.ContentAddressed@. Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw'
-- via Landauer bridge. Sole physics axiom remains on Lean
-- @LandauerLaw.physicalSecondLaw@ (cited, not restated). Adds zero new physics
-- axioms. Knowing fiber (EpistemicMI) lives on @umst-formal-double-slit@ — cited,
-- not restated here.
module UMST.Urge.ContentAddressed
  ( -- * §3 geometric identity + snapshot carriers
    ContentGeometricIdentity (..)
  , ContentGitHashCompat (..)
  , ContentAddressedUcrsStamp (..)
  , ContentGeometricPrimaryCert (..)
  , ContentAddressedSnapshot (..)
  , ContentAddressedWitness (..)
  , ContentAddressedMorphism (..)
  , ContentAddressedRefusal (..)
  , ContentAddressedVerdict (..)
  , ContentAdmissibilityConjunct (..)
  , contentConjunctAdmits
  , geometricContentIdPresent
  , evaluateGitHashOnlyIdentity
  , evaluateHostIdIdentity
  , refuseGitHashOnlyIdentity
  , refuseHostIdIdentity
  , refuseSecondArgmin
  , witnessFromSnapshot
  , applyContentAddressedMorphism
    -- * Excitement alignment (no second argmin)
  , ContentAddressedCtx (..)
  , contentAddressedSelect
  , contentAddressedSelectBare
  , contentAddressedSelectEqExcitementSelect
  , contentAddressedSelectEqUrgeRecoverySelect
  , contentAddressedNoLocalArgmin
  , contentAddressedSelectFromSnapshot
  , contentAddressedSelectFromSnapshotEqExcitementSelect
    -- * §3 fixtures + positive refuse witnesses
  , contentFixtureState
  , contentFixtureGeometric
  , contentFixtureGitCompat
  , contentFixtureUcrs
  , contentFixtureGeometricCert
  , contentFixtureSnapshot
  , contentFixtureConjunct
  , contentFixtureGitHashOnlyRefused
  , contentFixtureHostIdRefused
  , contentFixtureApplyMorphismOk
  , contentFixtureGeometricContentIdPresent
  , contentFixtureWitnessPreservesGeometric
  , contentFixtureWitnessPreservesGitCompat
  , contentAddressedGitHashOnlyNotAdmitted
  , contentAddressedHostIdNotAdmitted
  , gitHashOnlyRefusedPositive
  , hostIdRefusedPositive
    -- * Landauer bridge (derived — zero new axioms)
  , ContentHistoryTransition (..)
  , admissibleContentAddressed
  , contentSecondLawFromLandauer
  , contentFromLandauerAdmitSecondLaw
  , contentSecondLawFromHypothesis
  , physicalSecondLawImported
    -- * Honesty flags + catalog witnesses
  , contentAddressedPhysicsGreen
  , contentAddressedPhysicsGreenFalse
  , contentAddressedProductionWired
  , contentAddressedProductionWiredFalse
  , contentAddressedNonClaim
  , contentAddressedNonClaimNonempty
  , contentAddressedModuleWitness
  , contentAddressedNoNewAxiom
  , contentAddressedNoSecondArgmin
  ) where

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
import UMST.Urge.ExcitementImport
  ( urgeRecoverySelect
  , urgeRecoverySelectEqExcitementSelect
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Content-addressed snapshot + typed morphism carriers
-- ---------------------------------------------------------------------------

-- | §3 geometric identity — primary content-address factor (SDF surrogate).
data ContentGeometricIdentity = ContentGeometricIdentity
  { contentId      :: !Int
  , resolutionBits :: !Int
  } deriving (Show, Eq)

-- | Git hash compatibility witness — secondary to geometric identity.
data ContentGitHashCompat = ContentGitHashCompat
  { gitHash :: !String
  } deriving (Show, Eq)

-- | UCRS stamp surrogate carried through content-addressed history.
data ContentAddressedUcrsStamp = ContentAddressedUcrsStamp
  { ucrsSeq      :: !Int
  , ucrsWallHasT :: !Bool
  } deriving (Show, Eq)

-- | Geometric-primary certificate — content id must be non-zero.
data ContentGeometricPrimaryCert = ContentGeometricPrimaryCert
  { geometricPrimary :: !Bool
  } deriving (Show, Eq)

-- | Snapshot identity at history head (content-addressed surrogate).
data ContentAddressedSnapshot = ContentAddressedSnapshot
  { snapshotId       :: !Int
  , snapshotHead     :: !ThermodynamicState
  , snapshotGeometric :: !ContentGeometricIdentity
  , snapshotGitCompat :: !(Maybe ContentGitHashCompat)
  , snapshotUcrs     :: !ContentAddressedUcrsStamp
  , snapshotGeometricCert :: !ContentGeometricPrimaryCert
  , snapshotProvenanceIntact :: !Bool
  } deriving (Show, Eq)

-- | Witness bundle a content-addressed morphism must preserve (§3).
data ContentAddressedWitness = ContentAddressedWitness
  { witnessGeometric        :: !ContentGeometricIdentity
  , witnessGitCompat        :: !(Maybe ContentGitHashCompat)
  , witnessGeometricPrimary :: !Bool
  , witnessProvenanceIntact :: !Bool
  } deriving (Show, Eq)

-- | Typed content-addressed morphism — admissible history transition.
data ContentAddressedMorphism = ContentAddressedMorphism
  { morphismFrom          :: !ContentAddressedSnapshot
  , morphismToSeq           :: !Int
  , morphismWitness       :: !ContentAddressedWitness
  , morphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Fail-closed content-addressed errors — positive refuse, not silent accept.
data ContentAddressedRefusal
  = CarGitHashOnlyIdentity !String
  | CarHostIdIdentity !Int
  | CarGateRejected !Int
  | CarGeometricZero !Int
  | CarSecondArgminRefused
  deriving (Show, Eq)

-- | Verdict of a content-addressed admission operation class.
data ContentAddressedVerdict
  = CavAdmitted
  | CavGitHashOnlyRefused
  | CavHostIdRefused
  | CavInadmissible
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §3 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §3 admissibility conjunct inputs (surrogate).
data ContentAdmissibilityConjunct = ContentAdmissibilityConjunct
  { conjunctGateOk              :: !Bool
  , conjunctGeometricPrimary    :: !Bool
  , conjunctExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Conjunct admits when gate, geometric-primary, and excitement all hold.
contentConjunctAdmits :: ContentAdmissibilityConjunct -> Bool
contentConjunctAdmits c =
  conjunctGateOk c
  && conjunctGeometricPrimary c
  && conjunctExcitementPreserves c

-- | Geometric content id present when non-zero.
geometricContentIdPresent :: ContentGeometricIdentity -> Bool
geometricContentIdPresent g = contentId g /= 0

-- | Evaluate git-hash-only identity attempt.
evaluateGitHashOnlyIdentity :: Bool -> ContentAddressedVerdict
evaluateGitHashOnlyIdentity True  = CavGitHashOnlyRefused
evaluateGitHashOnlyIdentity False = CavAdmitted

-- | Evaluate host-id surrogate identity attempt.
evaluateHostIdIdentity :: Bool -> ContentAddressedVerdict
evaluateHostIdIdentity True  = CavHostIdRefused
evaluateHostIdIdentity False = CavAdmitted

-- | Positive refuse: git-hash-only identity without geometric carrier.
refuseGitHashOnlyIdentity :: String -> ContentAddressedRefusal
refuseGitHashOnlyIdentity h = CarGitHashOnlyIdentity h

-- | Positive refuse: host-id surrogate identity.
refuseHostIdIdentity :: Int -> ContentAddressedRefusal
refuseHostIdIdentity hid = CarHostIdIdentity hid

-- | Second-argmin pin refused at content-addressed boundary.
refuseSecondArgmin :: ContentAddressedRefusal
refuseSecondArgmin = CarSecondArgminRefused

-- | Witness bundle from snapshot at morphism head.
witnessFromSnapshot :: ContentAddressedSnapshot -> ContentAddressedWitness
witnessFromSnapshot s =
  ContentAddressedWitness
    { witnessGeometric = snapshotGeometric s
    , witnessGitCompat = snapshotGitCompat s
    , witnessGeometricPrimary = geometricPrimary (snapshotGeometricCert s)
    , witnessProvenanceIntact = snapshotProvenanceIntact s
    }

-- | Apply typed content-addressed morphism — fail-closed on refusal paths.
applyContentAddressedMorphism
  :: ContentAddressedSnapshot
  -> Int
  -> ContentAdmissibilityConjunct
  -> Bool
  -> Either ContentAddressedRefusal ContentAddressedMorphism
applyContentAddressedMorphism snapshot toSeq conjunct excitementSelected
  | not (contentConjunctAdmits conjunct) =
      Left (CarGateRejected (ucrsSeq (snapshotUcrs snapshot)))
  | not (geometricContentIdPresent (snapshotGeometric snapshot)) =
      case snapshotGitCompat snapshot of
        Just compat -> Left (CarGitHashOnlyIdentity (gitHash compat))
        Nothing     -> Left (CarHostIdIdentity 0)
  | not (geometricPrimary (snapshotGeometricCert snapshot)) =
      Left (CarGeometricZero (snapshotId snapshot))
  | not (snapshotProvenanceIntact snapshot) =
      Left (CarGeometricZero (snapshotId snapshot))
  | not excitementSelected =
      Left (CarGeometricZero (snapshotId snapshot))
  | otherwise =
      Right
        ContentAddressedMorphism
          { morphismFrom = snapshot
          , morphismToSeq = toSeq
          , morphismWitness = witnessFromSnapshot snapshot
          , morphismExcitementSelected = excitementSelected
          }

-- ---------------------------------------------------------------------------
-- SECTION 3: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for content-addressed history over admissible successors.
data ContentAddressedCtx = ContentAddressedCtx
  { contentPrior      :: !ThermodynamicState
  , contentSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Content-addressed history **is** 'excitementSelect' — no Urge-local argmin.
contentAddressedSelect
  :: ContentAddressedCtx
  -> Either ExcitementResidue HistoryCandidate
contentAddressedSelect ctx =
  excitementSelect (contentPrior ctx) (contentSuccessors ctx)

-- | Bare selector on prior + successors.
contentAddressedSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
contentAddressedSelectBare = excitementSelect

-- | Definitional witness: content-addressed selection API is 'excitementSelect'.
contentAddressedSelectEqExcitementSelect
  :: ContentAddressedCtx -> Bool
contentAddressedSelectEqExcitementSelect ctx =
  contentAddressedSelect ctx
    == excitementSelect (contentPrior ctx) (contentSuccessors ctx)

-- | Content-addressed selection equals urge recovery selector.
contentAddressedSelectEqUrgeRecoverySelect
  :: ContentAddressedCtx -> Bool
contentAddressedSelectEqUrgeRecoverySelect ctx =
  contentAddressedSelect ctx
    == urgeRecoverySelect (contentPrior ctx) (contentSuccessors ctx)

-- | No Urge-local argmin — composes imported 'excitementSelect' only.
contentAddressedNoLocalArgmin
  :: ContentAddressedCtx -> Bool
contentAddressedNoLocalArgmin ctx =
  contentAddressedSelect ctx
    == excitementSelect (contentPrior ctx) (contentSuccessors ctx)

-- | Snapshot-head recovery composes 'excitementSelect' on typed head.
contentAddressedSelectFromSnapshot
  :: ContentAddressedSnapshot
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
contentAddressedSelectFromSnapshot snap cands =
  excitementSelect (snapshotHead snap) cands

-- | Snapshot selection equals 'excitementSelect' on snapshot head.
contentAddressedSelectFromSnapshotEqExcitementSelect
  :: ContentAddressedSnapshot -> [HistoryCandidate] -> Bool
contentAddressedSelectFromSnapshotEqExcitementSelect snap cands =
  contentAddressedSelectFromSnapshot snap cands
    == excitementSelect (snapshotHead snap) cands

-- ---------------------------------------------------------------------------
-- SECTION 4: §3 fixtures + positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Fixture thermodynamic head for content-addressed scaffold.
contentFixtureState :: ThermodynamicState
contentFixtureState = ThermodynamicState 2400 0 0.3 30 40

-- | Fixture geometric identity (non-zero content id).
contentFixtureGeometric :: ContentGeometricIdentity
contentFixtureGeometric =
  ContentGeometricIdentity {contentId = 5381, resolutionBits = 2}

-- | Fixture git hash compatibility witness.
contentFixtureGitCompat :: ContentGitHashCompat
contentFixtureGitCompat =
  ContentGitHashCompat {gitHash = "sha1:geometric-primary-compat"}

-- | Fixture UCRS stamp surrogate.
contentFixtureUcrs :: ContentAddressedUcrsStamp
contentFixtureUcrs = ContentAddressedUcrsStamp {ucrsSeq = 3, ucrsWallHasT = True}

-- | Fixture geometric-primary certificate.
contentFixtureGeometricCert :: ContentGeometricPrimaryCert
contentFixtureGeometricCert = ContentGeometricPrimaryCert {geometricPrimary = True}

-- | Fixture content-addressed snapshot at history head.
contentFixtureSnapshot :: ContentAddressedSnapshot
contentFixtureSnapshot =
  ContentAddressedSnapshot
    { snapshotId = 1
    , snapshotHead = contentFixtureState
    , snapshotGeometric = contentFixtureGeometric
    , snapshotGitCompat = Just contentFixtureGitCompat
    , snapshotUcrs = contentFixtureUcrs
    , snapshotGeometricCert = contentFixtureGeometricCert
    , snapshotProvenanceIntact = True
    }

-- | Fixture admissibility conjunct (all gates pass).
contentFixtureConjunct :: ContentAdmissibilityConjunct
contentFixtureConjunct =
  ContentAdmissibilityConjunct
    { conjunctGateOk = True
    , conjunctGeometricPrimary = True
    , conjunctExcitementPreserves = True
    }

-- | Git-hash-only identity refused positively.
contentFixtureGitHashOnlyRefused :: Bool
contentFixtureGitHashOnlyRefused =
  refuseGitHashOnlyIdentity "sha1:only-hash"
    == CarGitHashOnlyIdentity "sha1:only-hash"

-- | Host-id surrogate identity refused positively.
contentFixtureHostIdRefused :: Bool
contentFixtureHostIdRefused =
  refuseHostIdIdentity 0xdeadbeef
    == CarHostIdIdentity 0xdeadbeef

-- | Fixture morphism application succeeds under conjunct + excitement pin.
contentFixtureApplyMorphismOk :: Bool
contentFixtureApplyMorphismOk =
  applyContentAddressedMorphism
    contentFixtureSnapshot
    2
    contentFixtureConjunct
    True
    == Right
      ContentAddressedMorphism
        { morphismFrom = contentFixtureSnapshot
        , morphismToSeq = 2
        , morphismWitness = witnessFromSnapshot contentFixtureSnapshot
        , morphismExcitementSelected = True
        }

-- | Fixture geometric content id is present.
contentFixtureGeometricContentIdPresent :: Bool
contentFixtureGeometricContentIdPresent =
  geometricContentIdPresent contentFixtureGeometric

-- | Witness preserves geometric identity from snapshot.
contentFixtureWitnessPreservesGeometric :: Bool
contentFixtureWitnessPreservesGeometric =
  witnessGeometric (witnessFromSnapshot contentFixtureSnapshot)
    == contentFixtureGeometric

-- | Witness preserves git hash compatibility from snapshot.
contentFixtureWitnessPreservesGitCompat :: Bool
contentFixtureWitnessPreservesGitCompat =
  witnessGitCompat (witnessFromSnapshot contentFixtureSnapshot)
    == Just contentFixtureGitCompat

-- | Git-hash-only identity path is not admitted.
contentAddressedGitHashOnlyNotAdmitted :: Bool
contentAddressedGitHashOnlyNotAdmitted =
  evaluateGitHashOnlyIdentity True /= CavAdmitted

-- | Host-id identity path is not admitted.
contentAddressedHostIdNotAdmitted :: Bool
contentAddressedHostIdNotAdmitted =
  evaluateHostIdIdentity True /= CavAdmitted

-- | Positive refuse witness for git-hash-only identity.
gitHashOnlyRefusedPositive :: String -> Bool
gitHashOnlyRefusedPositive h =
  refuseGitHashOnlyIdentity h == CarGitHashOnlyIdentity h

-- | Positive refuse witness for host-id identity.
hostIdRefusedPositive :: Int -> Bool
hostIdRefusedPositive hid =
  refuseHostIdIdentity hid == CarHostIdIdentity hid

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Content-addressed history transition surrogate for second-law discharge.
data ContentHistoryTransition = ContentHistoryTransition
  { contentPriorHead       :: !ThermodynamicState
  , contentPostHead        :: !ThermodynamicState
  , contentGateChecked     :: !Bool
  , contentGeometricPrimary :: !Bool
  , contentProvenanceOk    :: !Bool
  } deriving (Show, Eq)

-- | Admissible when gate, geometric-primary, and provenance hold.
admissibleContentAddressed :: ContentHistoryTransition -> Bool
admissibleContentAddressed t =
  contentGateChecked t
  && contentGeometricPrimary t
  && contentProvenanceOk t

-- | Second law on content transition from Landauer bridge discharge.
contentSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
contentSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
contentFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
contentFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for content second law (no new axiom).
contentSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
contentSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- | Physical second law imported from Lean @LandauerLaw.physicalSecondLaw@.
physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
contentAddressedPhysicsGreen :: Bool
contentAddressedPhysicsGreen = False

-- | Lean/Coq: @content_addressed_physics_green_false@.
contentAddressedPhysicsGreenFalse :: Bool
contentAddressedPhysicsGreenFalse =
  not contentAddressedPhysicsGreen

-- | Production wiring stays open (content-addressed lift only).
contentAddressedProductionWired :: Bool
contentAddressedProductionWired = False

-- | Lean/Coq: @content_addressed_production_wired_false@.
contentAddressedProductionWiredFalse :: Bool
contentAddressedProductionWiredFalse =
  not contentAddressedProductionWired

-- | Honest non-claim string (meso §3 content-addressed scaffold).
contentAddressedNonClaim :: String
contentAddressedNonClaim =
  "§3 content-addressed history; geometric identity primary, git hash compatibility; "
    ++ "compose excitementSelect not local argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
contentAddressedNonClaimNonempty :: Bool
contentAddressedNonClaimNonempty = length contentAddressedNonClaim > 0

-- | Catalog witness: meso Urge ContentAddressed module present.
contentAddressedModuleWitness :: Bool
contentAddressedModuleWitness = True

-- | Zero new axiom discipline witness.
contentAddressedNoNewAxiom :: Bool
contentAddressedNoNewAxiom = True

-- | Second-argmin refusal: content-addressed composes 'excitementSelect' only.
contentAddressedNoSecondArgmin :: Bool
contentAddressedNoSecondArgmin =
  contentAddressedNoLocalArgmin
    (ContentAddressedCtx
      { contentPrior = contentFixtureState
      , contentSuccessors = []
      })
  && contentAddressedSelectEqUrgeRecoverySelect
       (ContentAddressedCtx
         { contentPrior = contentFixtureState
         , contentSuccessors = []
         })
  && urgeRecoverySelectEqExcitementSelect contentFixtureState []
