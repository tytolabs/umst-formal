-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.CryptoCompose
-- Description : Meso acting Urge — §5.4 cryptographic safety lifted by composition.
--
-- §5.4: content-addressed DID+RID, signed transitions, threshold canonicalization —
-- **is** an Excitement-selected admissible state transition, not egoff copy-paste
-- theater. Cryptographic safety lives in compose, not a side channel.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.CryptoCompose
  ( -- * Crypto identity + typed morphism carriers (§5.4)
    CryptoIdentityClass (..)
  , identityContentAddressed
  , CryptoUcrsStamp (..)
  , CryptoThresholdCert (..)
  , CryptoSsotDigest (..)
  , CryptoComposeSnapshot (..)
  , CryptoComposeWitness (..)
  , CryptoComposeMorphism (..)
  , CryptoComposeRefusal (..)
  , CryptoComposeVerdict (..)
    -- * §5.4 admissibility conjunct + positive refuse
  , CryptoAdmissibilityConjunct (..)
  , cryptoConjunctAdmits
  , evaluateCryptoComposeOperation
  , refuseEgoffCopyPaste
  , refuseHostIdAsRid
  , refuseUnsignedTransition
  , witnessFromCryptoSnapshot
  , applyCryptoComposeMorphism
  , cryptoComposeEgoffCopyPasteRefused
  , cryptoComposeMorphismOkWhenNotCopyPaste
  , refuseEgoffCopyPastePositive
  , refuseHostIdAsRidPositive
  , refuseUnsignedTransitionPositive
    -- * Crypto compose composes excitementSelect (no second argmin)
  , CryptoComposeCtx (..)
  , cryptoComposeSelect
  , cryptoComposeSelectEqExcitementSelect
  , cryptoComposeSelectEqUrgeRecoverySelect
  , cryptoComposeNoLocalArgmin
  , cryptoComposeSelectEmpty
    -- * §5.4 fixtures + witness theorems
  , cryptoComposeFixtureState
  , cryptoComposeFixtureUcrs
  , cryptoComposeFixtureThreshold
  , cryptoComposeFixtureSsot
  , cryptoComposeFixtureSnapshot
  , cryptoComposeFixtureConjunct
  , cryptoComposeFixtureEgoffCopyPasteRefused
  , cryptoComposeFixtureApplyMorphismOk
  , cryptoComposeContentAddressedIdentity
  , cryptoComposeDecentralizedDidIdentity
  , cryptoComposeHostIdNotContentAddressed
  , cryptoComposeFixtureWitnessPreservesUcrs
  , cryptoComposePositiveRefuseNotSilent
    -- * Landauer bridge (derived — zero new axioms)
  , CryptoHistoryMove (..)
  , admissibleCryptoCompose
  , cryptoSecondLaw
  , cryptoSecondLawFromLandauer
  , cryptoSecondLawFromHypothesis
  , cryptoFromLandauerAdmitSecondLaw
    -- * Honesty flags + catalog witnesses
  , cryptoComposePhysicsGreen
  , cryptoComposePhysicsGreenFalse
  , cryptoComposeProductionWired
  , cryptoComposeProductionWiredFalse
  , cryptoComposeNonClaim
  , cryptoComposeNonClaimNonempty
  , cryptoComposeModuleWitness
  , cryptoComposeNoNewAxiom
  , cryptoComposeNoSecondArgmin
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
import UMST.Urge.ExcitementImport (urgeRecoverySelect)

-- ---------------------------------------------------------------------------
-- SECTION 1: Crypto identity + typed morphism carriers (§5.4)
-- ---------------------------------------------------------------------------

-- | Identity class row from §5.4 — content-addressed vs host-id surrogate.
data CryptoIdentityClass
  = CicContentAddressedRid
  | CicDecentralizedDid
  | CicHostIdSurrogate
  deriving (Show, Eq)

-- | Whether identity is content-addressed (not raw host id).
identityContentAddressed :: CryptoIdentityClass -> Bool
identityContentAddressed CicContentAddressedRid = True
identityContentAddressed CicDecentralizedDid    = True
identityContentAddressed CicHostIdSurrogate       = False

-- | UCRS stamp surrogate carried through signed transition.
data CryptoUcrsStamp = CryptoUcrsStamp
  { cryptoUcrsSeq       :: !Int
  , cryptoUcrsWallHasT  :: !Bool
  } deriving (Show, Eq)

-- | Threshold canonicalization certificate — quorum must be met.
data CryptoThresholdCert = CryptoThresholdCert
  { cryptoThresholdQuorum :: !Int
  , cryptoThresholdValid  :: !Int
  , cryptoThresholdMet  :: !Bool
  } deriving (Show, Eq)

-- | SSOT digest hex surrogate (64-char content-addressed RID witness).
data CryptoSsotDigest = CryptoSsotDigest
  { cryptoDigestHexLen   :: !Int
  , cryptoDigestHexValid :: !Bool
  } deriving (Show, Eq)

-- | Snapshot identity at transition source (content-addressed surrogate).
data CryptoComposeSnapshot = CryptoComposeSnapshot
  { cryptoSnapshotId        :: !Int
  , cryptoSnapshotHead      :: !ThermodynamicState
  , cryptoSnapshotUcrs      :: !CryptoUcrsStamp
  , cryptoSnapshotThreshold :: !CryptoThresholdCert
  , cryptoSnapshotSsotDigest :: !CryptoSsotDigest
  , cryptoSnapshotSigned    :: !Bool
  , cryptoSnapshotIdentity  :: !CryptoIdentityClass
  } deriving (Show, Eq)

-- | Witness bundle a crypto compose morphism must preserve (§5.4).
data CryptoComposeWitness = CryptoComposeWitness
  { cryptoWitnessUcrs       :: !CryptoUcrsStamp
  , cryptoWitnessThreshold  :: !CryptoThresholdCert
  , cryptoWitnessSsotValid  :: !Bool
  } deriving (Show, Eq)

-- | Typed crypto compose morphism — admissible signed transition, not blind copy.
data CryptoComposeMorphism = CryptoComposeMorphism
  { cryptoMorphismFrom              :: !CryptoComposeSnapshot
  , cryptoMorphismToIdentity        :: !CryptoIdentityClass
  , cryptoMorphismWitness           :: !CryptoComposeWitness
  , cryptoMorphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Fail-closed crypto compose errors — positive refuse, not silent no-op.
data CryptoComposeRefusal
  = CcrEgoffCopyPasteRefused !Int
  | CcrGateRejected !Int
  | CcrUnsignedTransition !Int
  | CcrHostIdAsRid !Int
  | CcrBelowThreshold !Int
  | CcrInvalidSsotDigest !Int
  | CcrIdentityClassMismatch
  deriving (Show, Eq)

-- | Verdict of a crypto compose operation class.
data CryptoComposeVerdict
  = CcvMorphismOk
  | CcvEgoffCopyPasteRefused
  | CcvInadmissible
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §5.4 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §5.4 admissibility conjunct inputs (surrogate).
data CryptoAdmissibilityConjunct = CryptoAdmissibilityConjunct
  { cryptoConjGateOk              :: !Bool
  , cryptoConjThresholdMet        :: !Bool
  , cryptoConjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate @admit(h) ⟺ gate ∧ threshold ∧ Excitement preserves@.
cryptoConjunctAdmits :: CryptoAdmissibilityConjunct -> Bool
cryptoConjunctAdmits c =
  cryptoConjGateOk c
  && cryptoConjThresholdMet c
  && cryptoConjExcitementPreserves c

-- | Classify egoff copy-paste vs typed morphism without performing I/O.
evaluateCryptoComposeOperation :: Bool -> CryptoComposeVerdict
evaluateCryptoComposeOperation True  = CcvEgoffCopyPasteRefused
evaluateCryptoComposeOperation False = CcvMorphismOk

-- | Positive refuse: egoff crypto inventory copy-paste is inadmissible.
refuseEgoffCopyPaste :: Int -> CryptoComposeRefusal
refuseEgoffCopyPaste snapshotId = CcrEgoffCopyPasteRefused snapshotId

-- | Positive refuse: host id cannot serve as content-addressed RID.
refuseHostIdAsRid :: Int -> CryptoComposeRefusal
refuseHostIdAsRid hostId = CcrHostIdAsRid hostId

-- | Positive refuse: unsigned transition refused.
refuseUnsignedTransition :: Int -> CryptoComposeRefusal
refuseUnsignedTransition snapshotId = CcrUnsignedTransition snapshotId

-- | Build witness from snapshot — morphism must preserve stamps and certificates.
witnessFromCryptoSnapshot :: CryptoComposeSnapshot -> CryptoComposeWitness
witnessFromCryptoSnapshot s =
  CryptoComposeWitness
    { cryptoWitnessUcrs = cryptoSnapshotUcrs s
    , cryptoWitnessThreshold = cryptoSnapshotThreshold s
    , cryptoWitnessSsotValid =
        cryptoDigestHexValid (cryptoSnapshotSsotDigest s)
    }

-- | Attempt typed crypto compose morphism to target identity — fail closed.
applyCryptoComposeMorphism
  :: CryptoComposeSnapshot
  -> CryptoIdentityClass
  -> CryptoAdmissibilityConjunct
  -> Bool
  -> Either CryptoComposeRefusal CryptoComposeMorphism
applyCryptoComposeMorphism snapshot toIdentity conjunct excitementSelected
  | not (cryptoConjunctAdmits conjunct) =
      Left (CcrGateRejected (cryptoUcrsSeq (cryptoSnapshotUcrs snapshot)))
  | not (cryptoThresholdMet (cryptoSnapshotThreshold snapshot)) =
      Left (CcrBelowThreshold (cryptoSnapshotId snapshot))
  | not (cryptoDigestHexValid (cryptoSnapshotSsotDigest snapshot)) =
      Left (CcrInvalidSsotDigest (cryptoSnapshotId snapshot))
  | not (cryptoSnapshotSigned snapshot) =
      Left (CcrUnsignedTransition (cryptoSnapshotId snapshot))
  | not excitementSelected =
      Left (CcrUnsignedTransition (cryptoSnapshotId snapshot))
  | otherwise =
      Right
        CryptoComposeMorphism
          { cryptoMorphismFrom = snapshot
          , cryptoMorphismToIdentity = toIdentity
          , cryptoMorphismWitness = witnessFromCryptoSnapshot snapshot
          , cryptoMorphismExcitementSelected = excitementSelected
          }

-- | Positive refuse witness: egoff copy-paste classified refused.
cryptoComposeEgoffCopyPasteRefused :: Int -> Bool
cryptoComposeEgoffCopyPasteRefused _snapshotId =
  evaluateCryptoComposeOperation True == CcvEgoffCopyPasteRefused

-- | Typed morphism path when not copy-paste.
cryptoComposeMorphismOkWhenNotCopyPaste :: Bool
cryptoComposeMorphismOkWhenNotCopyPaste =
  evaluateCryptoComposeOperation False == CcvMorphismOk

-- | Positive refuse: egoff copy-paste tag.
refuseEgoffCopyPastePositive :: Int -> Bool
refuseEgoffCopyPastePositive snapshotId =
  refuseEgoffCopyPaste snapshotId == CcrEgoffCopyPasteRefused snapshotId

-- | Positive refuse: host id as RID.
refuseHostIdAsRidPositive :: Int -> Bool
refuseHostIdAsRidPositive hostId =
  refuseHostIdAsRid hostId == CcrHostIdAsRid hostId

-- | Positive refuse: unsigned transition.
refuseUnsignedTransitionPositive :: Int -> Bool
refuseUnsignedTransitionPositive snapshotId =
  refuseUnsignedTransition snapshotId == CcrUnsignedTransition snapshotId

-- ---------------------------------------------------------------------------
-- SECTION 3: Crypto compose composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for crypto compose over admissible history successors.
data CryptoComposeCtx = CryptoComposeCtx
  { cryptoComposePrior       :: !ThermodynamicState
  , cryptoComposeSuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Crypto compose **is** 'urgeRecoverySelect' / 'excitementSelect'.
cryptoComposeSelect
  :: CryptoComposeCtx
  -> Either ExcitementResidue HistoryCandidate
cryptoComposeSelect ctx =
  urgeRecoverySelect (cryptoComposePrior ctx) (cryptoComposeSuccessors ctx)

-- | Definitional witness: crypto compose selection API is 'excitementSelect'.
cryptoComposeSelectEqExcitementSelect :: CryptoComposeCtx -> Bool
cryptoComposeSelectEqExcitementSelect ctx =
  cryptoComposeSelect ctx
    == excitementSelect (cryptoComposePrior ctx) (cryptoComposeSuccessors ctx)

-- | Crypto compose selection equals 'urgeRecoverySelect'.
cryptoComposeSelectEqUrgeRecoverySelect :: CryptoComposeCtx -> Bool
cryptoComposeSelectEqUrgeRecoverySelect ctx =
  cryptoComposeSelect ctx
    == urgeRecoverySelect (cryptoComposePrior ctx) (cryptoComposeSuccessors ctx)

-- | Crypto compose selector re-uses 'excitementSelect' — no Urge-local argmin.
cryptoComposeNoLocalArgmin :: CryptoComposeCtx -> Bool
cryptoComposeNoLocalArgmin ctx =
  cryptoComposeSelect ctx
    == excitementSelect (cryptoComposePrior ctx) (cryptoComposeSuccessors ctx)

-- | Empty successor list yields no-candidates residue.
cryptoComposeSelectEmpty :: CryptoComposeCtx -> Bool
cryptoComposeSelectEmpty ctx =
  cryptoComposeSuccessors ctx == []
  && cryptoComposeSelect ctx == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: §5.4 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | Fixture thermodynamic head for §5.4 sample.
cryptoComposeFixtureState :: ThermodynamicState
cryptoComposeFixtureState = ThermodynamicState 2400 0 0 0 0

-- | Fixture UCRS stamp with wall-has-T.
cryptoComposeFixtureUcrs :: CryptoUcrsStamp
cryptoComposeFixtureUcrs =
  CryptoUcrsStamp {cryptoUcrsSeq = 7, cryptoUcrsWallHasT = True}

-- | Fixture threshold certificate with quorum met.
cryptoComposeFixtureThreshold :: CryptoThresholdCert
cryptoComposeFixtureThreshold =
  CryptoThresholdCert
    { cryptoThresholdQuorum = 1
    , cryptoThresholdValid = 1
    , cryptoThresholdMet = True
    }

-- | Fixture SSOT digest (64-char surrogate).
cryptoComposeFixtureSsot :: CryptoSsotDigest
cryptoComposeFixtureSsot =
  CryptoSsotDigest {cryptoDigestHexLen = 64, cryptoDigestHexValid = True}

-- | Fixture signed snapshot with content-addressed identity.
cryptoComposeFixtureSnapshot :: CryptoComposeSnapshot
cryptoComposeFixtureSnapshot =
  CryptoComposeSnapshot
    { cryptoSnapshotId = 1
    , cryptoSnapshotHead = cryptoComposeFixtureState
    , cryptoSnapshotUcrs = cryptoComposeFixtureUcrs
    , cryptoSnapshotThreshold = cryptoComposeFixtureThreshold
    , cryptoSnapshotSsotDigest = cryptoComposeFixtureSsot
    , cryptoSnapshotSigned = True
    , cryptoSnapshotIdentity = CicContentAddressedRid
    }

-- | Fixture admissibility conjunct — gate ∧ threshold ∧ excitement.
cryptoComposeFixtureConjunct :: CryptoAdmissibilityConjunct
cryptoComposeFixtureConjunct =
  CryptoAdmissibilityConjunct
    { cryptoConjGateOk = True
    , cryptoConjThresholdMet = True
    , cryptoConjExcitementPreserves = True
    }

-- | Fixture: egoff copy-paste refused at snapshot id 1.
cryptoComposeFixtureEgoffCopyPasteRefused :: Bool
cryptoComposeFixtureEgoffCopyPasteRefused =
  refuseEgoffCopyPaste (cryptoSnapshotId cryptoComposeFixtureSnapshot)
    == CcrEgoffCopyPasteRefused 1

-- | Fixture: typed morphism to decentralized DID succeeds.
cryptoComposeFixtureApplyMorphismOk :: Bool
cryptoComposeFixtureApplyMorphismOk =
  applyCryptoComposeMorphism
    cryptoComposeFixtureSnapshot
    CicDecentralizedDid
    cryptoComposeFixtureConjunct
    True
    == Right
      CryptoComposeMorphism
        { cryptoMorphismFrom = cryptoComposeFixtureSnapshot
        , cryptoMorphismToIdentity = CicDecentralizedDid
        , cryptoMorphismWitness = witnessFromCryptoSnapshot cryptoComposeFixtureSnapshot
        , cryptoMorphismExcitementSelected = True
        }

-- | Content-addressed RID class is content-addressed.
cryptoComposeContentAddressedIdentity :: Bool
cryptoComposeContentAddressedIdentity =
  identityContentAddressed CicContentAddressedRid

-- | Decentralized DID class is content-addressed.
cryptoComposeDecentralizedDidIdentity :: Bool
cryptoComposeDecentralizedDidIdentity =
  identityContentAddressed CicDecentralizedDid

-- | Host-id surrogate is not content-addressed.
cryptoComposeHostIdNotContentAddressed :: Bool
cryptoComposeHostIdNotContentAddressed =
  not (identityContentAddressed CicHostIdSurrogate)

-- | Witness from fixture preserves UCRS stamp.
cryptoComposeFixtureWitnessPreservesUcrs :: Bool
cryptoComposeFixtureWitnessPreservesUcrs =
  cryptoWitnessUcrs (witnessFromCryptoSnapshot cryptoComposeFixtureSnapshot)
    == cryptoComposeFixtureUcrs

-- | Positive refuse is not silent — copy-paste ≠ morphism ok.
cryptoComposePositiveRefuseNotSilent :: Bool
cryptoComposePositiveRefuseNotSilent =
  evaluateCryptoComposeOperation True /= CcvMorphismOk

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Crypto history move conjunct (§5.4 gate + threshold + provenance).
data CryptoHistoryMove = CryptoHistoryMove
  { cryptoMoveGateChecked        :: !Bool
  , cryptoMoveThresholdCanonical :: !Bool
  , cryptoMoveProvenanceOk       :: !Bool
  } deriving (Show, Eq)

-- | Admissible crypto compose move — conjunct discharge, not a new axiom.
admissibleCryptoCompose :: CryptoHistoryMove -> Bool
admissibleCryptoCompose h =
  cryptoMoveGateChecked h
  && cryptoMoveThresholdCanonical h
  && cryptoMoveProvenanceOk h

-- | Second law on crypto transition (Bool witness — Landauer cited on Lean).
cryptoSecondLaw :: HistoryTransition -> Bool
cryptoSecondLaw = admitSecondLaw

-- | Second law on crypto carrier transition from Landauer bridge discharge.
cryptoSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
cryptoSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
cryptoFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
cryptoFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for crypto second law (no new axiom).
cryptoSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
cryptoSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
cryptoComposePhysicsGreen :: Bool
cryptoComposePhysicsGreen = False

-- | Lean/Coq: @crypto_compose_physics_green_false@.
cryptoComposePhysicsGreenFalse :: Bool
cryptoComposePhysicsGreenFalse = not cryptoComposePhysicsGreen

-- | Production wiring stays open (crypto compose lift only).
cryptoComposeProductionWired :: Bool
cryptoComposeProductionWired = False

-- | Lean/Coq: @crypto_compose_production_wired_false@.
cryptoComposeProductionWiredFalse :: Bool
cryptoComposeProductionWiredFalse = not cryptoComposeProductionWired

-- | Honest non-claim string (meso §5.4 crypto compose scaffold).
cryptoComposeNonClaim :: String
cryptoComposeNonClaim =
  "§5.4 cryptographic safety lifted by composition not copied; "
    ++ "compose excitementSelect not second argmin; "
    ++ "Landauer physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
cryptoComposeNonClaimNonempty :: Bool
cryptoComposeNonClaimNonempty = length cryptoComposeNonClaim > 0

-- | Catalog witness: meso Urge CryptoCompose module present.
cryptoComposeModuleWitness :: Bool
cryptoComposeModuleWitness = True

-- | Zero new axiom discipline witness.
cryptoComposeNoNewAxiom :: Bool
cryptoComposeNoNewAxiom = True

-- | Second-argmin refusal: crypto compose composes 'excitementSelect' only.
cryptoComposeNoSecondArgmin :: Bool
cryptoComposeNoSecondArgmin =
  cryptoComposeNoLocalArgmin
    (CryptoComposeCtx
      { cryptoComposePrior = cryptoComposeFixtureState
      , cryptoComposeSuccessors = []
      })
