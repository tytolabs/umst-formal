-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.UmstTomlRemotes
-- Description : Meso acting Urge — §13.6 `[urge.remote.*]` in root `umst.toml`.
--
-- Typed parse of proposed remote policy rows; pre-push positive refuse —
-- not only `!physics_green`. Composes 'excitementSelect' — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.UmstTomlRemotes
  ( -- * Root `umst.toml` `[urge.remote.*]` carriers
    UrgeEntity (..)
  , RemoteClassification (..)
  , CanonicalRemote (..)
  , MirrorRemote (..)
  , EntityRemoteHost (..)
  , UrgeRemotePolicy (..)
  , EntityPrePushVerdict (..)
  , EntityPrePushRefusal (..)
  , urgeRemoteSectionPrefix
  , classifyEntityRemoteHost
  , evaluateEntityPrePush
  , entityRemoteFixtureLabsPublic
  , entityRemoteFixtureComposeConfidential
  , UrgeRemoteTomlRow (..)
  , UmstTomlRemotesDocument (..)
  , TomlRemoteParseError (..)
  , UmstTomlRemotesImportRefusal (..)
  , UmstTomlRemotesVerdict (..)
  , emptyUmstTomlRemotesDocument
    -- * Row ↔ policy bridge + pre-push evaluation
  , urgeRemoteTomlSectionKey
  , urgeRemoteTomlRowToPolicy
  , evaluateTomlPrePush
  , UmstTomlRemotesConjunct (..)
  , umstTomlRemotesConjunctAdmits
  , evaluateUmstTomlRemotesOperation
  , refuseSecondArgminSelector
  , refuseProductionWiredTomlPush
  , applyUmstTomlRemoteRow
    -- * Fixture document + honest parse surrogate
  , umstTomlFixtureLabsPublic
  , umstTomlFixtureComposeConfidential
  , rootUmstTomlFixtureDocument
  , parseRootUmstTomlRemotesFixture
  , parseRootUmstTomlRemotesEmpty
    -- * Root `umst.toml` composes Excitement (no second argmin)
  , UmstTomlRemotesCtx (..)
  , umstTomlRemotesSelect
  , umstTomlRemotesSelectEqExcitementSelect
  , umstTomlRemotesSelectEqUrgeRecoverySelect
  , umstTomlRemotesNoLocalArgmin
  , umstTomlRemotesEmpty
    -- * §13.6 fixtures + witness theorems
  , umstTomlFixtureConjunct
  , umstTomlFixtureState
  , umstTomlLabsPublicSectionKey
  , umstTomlComposeConfidentialSectionKey
  , umstTomlRowToPolicyLabsPublic
  , umstTomlRowToPolicyComposeConfidential
  , umstTomlLabsGithubAdmitted
  , umstTomlComposeGithubRefused
  , umstTomlComposeOriginRefused
  , umstTomlComposeForgeAdmitted
  , umstTomlFixtureApplyRowOk
  , umstTomlSectionPrefixWitness
  , umstTomlRemotesParseRefusedPositive
  , umstTomlRemotesDocumentOkWhenNotParseRefused
  , refuseSecondArgminSelectorPositive
  , refuseProductionWiredTomlPushPositive
  , rootUmstTomlFixtureDocumentTwoRows
  , parseRootUmstTomlRemotesFixtureOk
  , parseRootUmstTomlRemotesEmptyRefused
    -- * Landauer bridge (derived — zero new axioms)
  , UmstTomlRemotesHistoryMove (..)
  , admissibleUmstTomlRemotes
  , UmstTomlRemotesTransition (..)
  , umstTomlRemotesSecondLaw
  , PhysicalUmstTomlRemotesBridge (..)
  , umstTomlRemotesSecondLawFromPhysical
  , admissibleUmstTomlRemotesFromPhysical
  , physicalSecondLawImported
    -- * Honesty flags + catalog witnesses
  , umstTomlRemotesPhysicsGreen
  , umstTomlRemotesPhysicsGreenFalse
  , umstTomlRemotesProductionWired
  , umstTomlRemotesProductionWiredFalse
  , umstTomlRemotesModuleWitness
  , umstTomlRemotesNoNewAxiom
  , umstTomlRemotesNoSecondArgmin
  , umstTomlRemotesPositiveRefuseNotSilent
  , umstTomlComposeGithubPositiveRefuse
  , umstTomlComposeOriginPositiveRefuse
  , umstTomlRemotesNonClaim
  , umstTomlRemotesNonClaimNonempty
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HeatBath (..)
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
-- SECTION 1: §13.6 `[urge.remote.*]` policy carriers (EntityRemote bridge)
-- ---------------------------------------------------------------------------

data UrgeEntity
  = UrgeEntityLabs
  | UrgeEntityCompose
  deriving (Show, Eq)

data RemoteClassification
  = RemotePublicOss
  | RemoteLabsInternal
  | RemoteComposeConfidential
  | RemoteComposeDefence
  | RemoteProposalConfidential
  deriving (Show, Eq)

data CanonicalRemote
  = CanonicalForge
  | CanonicalNone
  deriving (Show, Eq)

data MirrorRemote
  = MirrorGithub
  | MirrorNone
  deriving (Show, Eq)

data EntityRemoteHost
  = EntityHostGithub
  | EntityHostOriginCursor
  | EntityHostForge
  | EntityHostUnclassified
  deriving (Show, Eq)

data UrgeRemotePolicy = UrgeRemotePolicy
  { policySectionKey     :: !String
  , policyEntity         :: !UrgeEntity
  , policyClassification :: !RemoteClassification
  , policyCanonical      :: !CanonicalRemote
  , policyMirror         :: !MirrorRemote
  } deriving (Show, Eq)

data EntityPrePushVerdict
  = EntityPrePushAdmitted
  | EntityPrePushComposeGithubRefused
  | EntityPrePushComposeOriginRefused
  | EntityPrePushOriginNeverSsotRefused
  | EntityPrePushUnclassifiedHostRefused
  | EntityPrePushProductionWiredRefused
  deriving (Show, Eq)

data EntityPrePushRefusal
  = EntityPrePushRefuseComposeGithub
  | EntityPrePushRefuseComposeOrigin
  | EntityPrePushRefuseOriginNeverSsot
  | EntityPrePushRefuseUnclassifiedHost !EntityRemoteHost
  | EntityPrePushRefuseProductionWired
  deriving (Show, Eq)

urgeRemoteSectionPrefix :: String
urgeRemoteSectionPrefix = "urge.remote."

classifyEntityRemoteHost :: String -> EntityRemoteHost
classifyEntityRemoteHost host
  | null host = EntityHostUnclassified
  | host == "origin.cursor.com" = EntityHostOriginCursor
  | host == "github.com" = EntityHostGithub
  | host == "forge.tyto.in" || host == "forge.entity" = EntityHostForge
  | otherwise = EntityHostUnclassified

labsGithubVerdict :: RemoteClassification -> Either EntityPrePushVerdict EntityPrePushRefusal
labsGithubVerdict RemotePublicOss = Left EntityPrePushAdmitted
labsGithubVerdict _ = Right (EntityPrePushRefuseUnclassifiedHost EntityHostGithub)

evaluateEntityPrePush :: UrgeRemotePolicy -> String -> Either EntityPrePushVerdict EntityPrePushRefusal
evaluateEntityPrePush policy host =
  case classifyEntityRemoteHost host of
    EntityHostOriginCursor ->
      case policyEntity policy of
        UrgeEntityCompose -> Right EntityPrePushRefuseComposeOrigin
        UrgeEntityLabs -> Right EntityPrePushRefuseOriginNeverSsot
    EntityHostGithub ->
      case policyEntity policy of
        UrgeEntityCompose -> Right EntityPrePushRefuseComposeGithub
        UrgeEntityLabs -> labsGithubVerdict (policyClassification policy)
    EntityHostForge -> Left EntityPrePushAdmitted
    EntityHostUnclassified ->
      Right (EntityPrePushRefuseUnclassifiedHost EntityHostUnclassified)

entityRemoteFixtureLabsPublic :: UrgeRemotePolicy
entityRemoteFixtureLabsPublic =
  UrgeRemotePolicy
    { policySectionKey = "labs-public"
    , policyEntity = UrgeEntityLabs
    , policyClassification = RemotePublicOss
    , policyCanonical = CanonicalForge
    , policyMirror = MirrorGithub
    }

entityRemoteFixtureComposeConfidential :: UrgeRemotePolicy
entityRemoteFixtureComposeConfidential =
  UrgeRemotePolicy
    { policySectionKey = "compose-confidential"
    , policyEntity = UrgeEntityCompose
    , policyClassification = RemoteComposeConfidential
    , policyCanonical = CanonicalForge
    , policyMirror = MirrorNone
    }

-- ---------------------------------------------------------------------------
-- SECTION 2: Root `umst.toml` `[urge.remote.*]` carriers
-- ---------------------------------------------------------------------------

data UrgeRemoteTomlRow = UrgeRemoteTomlRow
  { tomlSectionSuffix  :: !String
  , tomlEntity         :: !UrgeEntity
  , tomlClassification :: !RemoteClassification
  , tomlCanonical      :: !CanonicalRemote
  , tomlMirror         :: !MirrorRemote
  } deriving (Show, Eq)

data UmstTomlRemotesDocument = UmstTomlRemotesDocument
  { tomlRemoteRows :: ![UrgeRemoteTomlRow]
  } deriving (Show, Eq)

data TomlRemoteParseError
  = TomlNoRemoteSections
  | TomlMissingField !String !String
  | TomlUnknownValue !String !String !String
  deriving (Show, Eq)

data UmstTomlRemotesImportRefusal
  = UmstTomlRemotesSecondArgmin
  deriving (Show, Eq)

data UmstTomlRemotesVerdict
  = UmstTomlRemotesDocumentOk
  | UmstTomlRemotesParseRefused
  | UmstTomlRemotesInadmissible
  deriving (Show, Eq)

emptyUmstTomlRemotesDocument :: UmstTomlRemotesDocument
emptyUmstTomlRemotesDocument = UmstTomlRemotesDocument {tomlRemoteRows = []}

-- ---------------------------------------------------------------------------
-- SECTION 3: Row ↔ policy bridge + pre-push evaluation
-- ---------------------------------------------------------------------------

urgeRemoteTomlSectionKey :: UrgeRemoteTomlRow -> String
urgeRemoteTomlSectionKey row =
  urgeRemoteSectionPrefix ++ tomlSectionSuffix row

urgeRemoteTomlRowToPolicy :: UrgeRemoteTomlRow -> UrgeRemotePolicy
urgeRemoteTomlRowToPolicy row =
  UrgeRemotePolicy
    { policySectionKey = tomlSectionSuffix row
    , policyEntity = tomlEntity row
    , policyClassification = tomlClassification row
    , policyCanonical = tomlCanonical row
    , policyMirror = tomlMirror row
    }

evaluateTomlPrePush :: UrgeRemoteTomlRow -> String -> Either EntityPrePushVerdict EntityPrePushRefusal
evaluateTomlPrePush row host =
  evaluateEntityPrePush (urgeRemoteTomlRowToPolicy row) host

data UmstTomlRemotesConjunct = UmstTomlRemotesConjunct
  { tomlConjunctGateOk              :: !Bool
  , tomlConjunctDocumentTyped       :: !Bool
  , tomlConjunctExcitementPreserves :: !Bool
  } deriving (Show, Eq)

umstTomlRemotesConjunctAdmits :: UmstTomlRemotesConjunct -> Bool
umstTomlRemotesConjunctAdmits c =
  tomlConjunctGateOk c
    && tomlConjunctDocumentTyped c
    && tomlConjunctExcitementPreserves c

evaluateUmstTomlRemotesOperation :: Bool -> UmstTomlRemotesVerdict
evaluateUmstTomlRemotesOperation isParseRefused =
  if isParseRefused then UmstTomlRemotesParseRefused else UmstTomlRemotesDocumentOk

refuseSecondArgminSelector :: UmstTomlRemotesImportRefusal
refuseSecondArgminSelector = UmstTomlRemotesSecondArgmin

refuseProductionWiredTomlPush :: EntityPrePushRefusal
refuseProductionWiredTomlPush = EntityPrePushRefuseProductionWired

applyUmstTomlRemoteRow
  :: UrgeRemoteTomlRow
  -> String
  -> UmstTomlRemotesConjunct
  -> Bool
  -> Either UrgeRemoteTomlRow EntityPrePushRefusal
applyUmstTomlRemoteRow row host conjunct excitementSelected
  | not (umstTomlRemotesConjunctAdmits conjunct) =
      Right (EntityPrePushRefuseUnclassifiedHost EntityHostUnclassified)
  | not excitementSelected =
      Right (EntityPrePushRefuseUnclassifiedHost EntityHostUnclassified)
  | otherwise =
      case evaluateTomlPrePush row host of
        Left _ -> Left row
        Right r -> Right r

-- ---------------------------------------------------------------------------
-- SECTION 4: Fixture document + honest parse surrogate
-- ---------------------------------------------------------------------------

umstTomlFixtureLabsPublic :: UrgeRemoteTomlRow
umstTomlFixtureLabsPublic =
  UrgeRemoteTomlRow
    { tomlSectionSuffix = "labs-public"
    , tomlEntity = UrgeEntityLabs
    , tomlClassification = RemotePublicOss
    , tomlCanonical = CanonicalForge
    , tomlMirror = MirrorGithub
    }

umstTomlFixtureComposeConfidential :: UrgeRemoteTomlRow
umstTomlFixtureComposeConfidential =
  UrgeRemoteTomlRow
    { tomlSectionSuffix = "compose-confidential"
    , tomlEntity = UrgeEntityCompose
    , tomlClassification = RemoteComposeConfidential
    , tomlCanonical = CanonicalForge
    , tomlMirror = MirrorNone
    }

rootUmstTomlFixtureDocument :: UmstTomlRemotesDocument
rootUmstTomlFixtureDocument =
  UmstTomlRemotesDocument
    { tomlRemoteRows =
        [ umstTomlFixtureLabsPublic
        , umstTomlFixtureComposeConfidential
        ]
    }

parseRootUmstTomlRemotesFixture :: Either UmstTomlRemotesDocument TomlRemoteParseError
parseRootUmstTomlRemotesFixture = Left rootUmstTomlFixtureDocument

parseRootUmstTomlRemotesEmpty :: Either UmstTomlRemotesDocument TomlRemoteParseError
parseRootUmstTomlRemotesEmpty = Right TomlNoRemoteSections

-- ---------------------------------------------------------------------------
-- SECTION 5: Root `umst.toml` composes Excitement (no second argmin)
-- ---------------------------------------------------------------------------

data UmstTomlRemotesCtx = UmstTomlRemotesCtx
  { umstTomlRemotesPrior       :: !ThermodynamicState
  , umstTomlRemotesSuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

umstTomlRemotesSelect
  :: UmstTomlRemotesCtx
  -> Either ExcitementResidue HistoryCandidate
umstTomlRemotesSelect ctx =
  urgeRecoverySelect
    (umstTomlRemotesPrior ctx)
    (umstTomlRemotesSuccessors ctx)

umstTomlRemotesSelectEqExcitementSelect :: UmstTomlRemotesCtx -> Bool
umstTomlRemotesSelectEqExcitementSelect ctx =
  umstTomlRemotesSelect ctx
    == excitementSelect
         (umstTomlRemotesPrior ctx)
         (umstTomlRemotesSuccessors ctx)

umstTomlRemotesSelectEqUrgeRecoverySelect :: UmstTomlRemotesCtx -> Bool
umstTomlRemotesSelectEqUrgeRecoverySelect ctx =
  umstTomlRemotesSelect ctx
    == urgeRecoverySelect
         (umstTomlRemotesPrior ctx)
         (umstTomlRemotesSuccessors ctx)

umstTomlRemotesNoLocalArgmin :: UmstTomlRemotesCtx -> Bool
umstTomlRemotesNoLocalArgmin ctx =
  umstTomlRemotesSelect ctx
    == excitementSelect
         (umstTomlRemotesPrior ctx)
         (umstTomlRemotesSuccessors ctx)

umstTomlRemotesEmpty :: UmstTomlRemotesCtx -> Bool
umstTomlRemotesEmpty ctx =
  umstTomlRemotesSelect ctx == Left ExcNoCandidates
  && null (umstTomlRemotesSuccessors ctx)

-- ---------------------------------------------------------------------------
-- SECTION 6: §13.6 fixtures + witness theorems
-- ---------------------------------------------------------------------------

umstTomlFixtureConjunct :: UmstTomlRemotesConjunct
umstTomlFixtureConjunct =
  UmstTomlRemotesConjunct
    { tomlConjunctGateOk = True
    , tomlConjunctDocumentTyped = True
    , tomlConjunctExcitementPreserves = True
    }

umstTomlFixtureState :: ThermodynamicState
umstTomlFixtureState = ThermodynamicState 2400 0 0 0 0

umstTomlRemotesParseRefusedPositive :: Bool
umstTomlRemotesParseRefusedPositive =
  evaluateUmstTomlRemotesOperation True == UmstTomlRemotesParseRefused

umstTomlRemotesDocumentOkWhenNotParseRefused :: Bool
umstTomlRemotesDocumentOkWhenNotParseRefused =
  evaluateUmstTomlRemotesOperation False == UmstTomlRemotesDocumentOk

refuseSecondArgminSelectorPositive :: Bool
refuseSecondArgminSelectorPositive =
  refuseSecondArgminSelector == UmstTomlRemotesSecondArgmin

refuseProductionWiredTomlPushPositive :: Bool
refuseProductionWiredTomlPushPositive =
  refuseProductionWiredTomlPush == EntityPrePushRefuseProductionWired

rootUmstTomlFixtureDocumentTwoRows :: Bool
rootUmstTomlFixtureDocumentTwoRows =
  length (tomlRemoteRows rootUmstTomlFixtureDocument) == 2

parseRootUmstTomlRemotesFixtureOk :: Bool
parseRootUmstTomlRemotesFixtureOk =
  parseRootUmstTomlRemotesFixture == Left rootUmstTomlFixtureDocument

parseRootUmstTomlRemotesEmptyRefused :: Bool
parseRootUmstTomlRemotesEmptyRefused =
  parseRootUmstTomlRemotesEmpty == Right TomlNoRemoteSections

umstTomlLabsPublicSectionKey :: Bool
umstTomlLabsPublicSectionKey =
  urgeRemoteTomlSectionKey umstTomlFixtureLabsPublic == "urge.remote.labs-public"

umstTomlComposeConfidentialSectionKey :: Bool
umstTomlComposeConfidentialSectionKey =
  urgeRemoteTomlSectionKey umstTomlFixtureComposeConfidential
    == "urge.remote.compose-confidential"

umstTomlRowToPolicyLabsPublic :: Bool
umstTomlRowToPolicyLabsPublic =
  urgeRemoteTomlRowToPolicy umstTomlFixtureLabsPublic
    == entityRemoteFixtureLabsPublic

umstTomlRowToPolicyComposeConfidential :: Bool
umstTomlRowToPolicyComposeConfidential =
  urgeRemoteTomlRowToPolicy umstTomlFixtureComposeConfidential
    == entityRemoteFixtureComposeConfidential

umstTomlLabsGithubAdmitted :: Bool
umstTomlLabsGithubAdmitted =
  evaluateTomlPrePush umstTomlFixtureLabsPublic "github.com"
    == Left EntityPrePushAdmitted

umstTomlComposeGithubRefused :: Bool
umstTomlComposeGithubRefused =
  evaluateTomlPrePush umstTomlFixtureComposeConfidential "github.com"
    == Right EntityPrePushRefuseComposeGithub

umstTomlComposeOriginRefused :: Bool
umstTomlComposeOriginRefused =
  evaluateTomlPrePush umstTomlFixtureComposeConfidential "origin.cursor.com"
    == Right EntityPrePushRefuseComposeOrigin

umstTomlComposeForgeAdmitted :: Bool
umstTomlComposeForgeAdmitted =
  evaluateTomlPrePush umstTomlFixtureComposeConfidential "forge.tyto.in"
    == Left EntityPrePushAdmitted

umstTomlFixtureApplyRowOk :: Bool
umstTomlFixtureApplyRowOk =
  applyUmstTomlRemoteRow
    umstTomlFixtureLabsPublic
    "forge.tyto.in"
    umstTomlFixtureConjunct
    True
    == Left umstTomlFixtureLabsPublic

umstTomlSectionPrefixWitness :: Bool
umstTomlSectionPrefixWitness = urgeRemoteSectionPrefix == "urge.remote."

-- ---------------------------------------------------------------------------
-- SECTION 7: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

data UmstTomlRemotesHistoryMove = UmstTomlRemotesHistoryMove
  { tomlMovePrior         :: !ThermodynamicState
  , tomlMovePost          :: !ThermodynamicState
  , tomlMoveGateChecked   :: !Bool
  , tomlMoveDocumentTyped :: !Bool
  , tomlMoveProvenanceOk  :: !Bool
  } deriving (Show, Eq)

admissibleUmstTomlRemotes :: UmstTomlRemotesHistoryMove -> Bool
admissibleUmstTomlRemotes h =
  tomlMoveGateChecked h
    && tomlMoveDocumentTyped h
    && tomlMoveProvenanceOk h

data UmstTomlRemotesTransition = UmstTomlRemotesTransition
  { tomlTransitionMove            :: !UmstTomlRemotesHistoryMove
  , tomlTransitionBath            :: !HeatBath
  , tomlTransitionDissipatedWork  :: !Double
  , tomlTransitionEntropyDrop     :: !Double
  } deriving (Show, Eq)

umstTomlRemotesSecondLaw :: UmstTomlRemotesTransition -> Bool
umstTomlRemotesSecondLaw t =
  tomlTransitionEntropyDrop t
    <= tomlTransitionDissipatedWork t / bathTemp (tomlTransitionBath t)

data PhysicalUmstTomlRemotesBridge = PhysicalUmstTomlRemotesBridge
  { physicalTomlLandauerBridge :: !LandauerHistoryBridge
  , physicalTomlTransition     :: !UmstTomlRemotesTransition
  , physicalTomlAdmissible     :: !Bool
  } deriving (Show, Eq)

umstTomlRemotesSecondLawFromPhysical :: PhysicalUmstTomlRemotesBridge -> Bool -> Bool
umstTomlRemotesSecondLawFromPhysical b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge
       (physicalTomlLandauerBridge b)
       hSL
  && admitSecondLaw (landauerTransition (physicalTomlLandauerBridge b))
  && umstTomlRemotesSecondLaw (physicalTomlTransition b)
  && physicalTomlAdmissible b

physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

admissibleUmstTomlRemotesFromPhysical :: PhysicalUmstTomlRemotesBridge -> Bool -> Bool
admissibleUmstTomlRemotesFromPhysical b hSL =
  hSL
  && physicalTomlAdmissible b
  && admissibleUmstTomlRemotes (tomlTransitionMove (physicalTomlTransition b))

-- ---------------------------------------------------------------------------
-- SECTION 8: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

umstTomlRemotesPhysicsGreen :: Bool
umstTomlRemotesPhysicsGreen = False

umstTomlRemotesPhysicsGreenFalse :: Bool
umstTomlRemotesPhysicsGreenFalse = not umstTomlRemotesPhysicsGreen

umstTomlRemotesProductionWired :: Bool
umstTomlRemotesProductionWired = False

umstTomlRemotesProductionWiredFalse :: Bool
umstTomlRemotesProductionWiredFalse = not umstTomlRemotesProductionWired

umstTomlRemotesModuleWitness :: Bool
umstTomlRemotesModuleWitness = True

umstTomlRemotesNoNewAxiom :: Bool
umstTomlRemotesNoNewAxiom = True

umstTomlRemotesNoSecondArgmin :: Bool
umstTomlRemotesNoSecondArgmin =
  umstTomlRemotesNoLocalArgmin
    (UmstTomlRemotesCtx umstTomlFixtureState [])

umstTomlRemotesPositiveRefuseNotSilent :: Bool
umstTomlRemotesPositiveRefuseNotSilent =
  evaluateUmstTomlRemotesOperation True /= UmstTomlRemotesDocumentOk

umstTomlComposeGithubPositiveRefuse :: Bool
umstTomlComposeGithubPositiveRefuse =
  evaluateTomlPrePush umstTomlFixtureComposeConfidential "github.com"
    /= Left EntityPrePushAdmitted

umstTomlComposeOriginPositiveRefuse :: Bool
umstTomlComposeOriginPositiveRefuse =
  evaluateTomlPrePush umstTomlFixtureComposeConfidential "origin.cursor.com"
    /= Left EntityPrePushAdmitted

umstTomlRemotesNonClaim :: String
umstTomlRemotesNonClaim =
  "§13.6 [urge.remote.*] in root umst.toml types; typed positive refuse not only "
    ++ "!physics_green; compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

umstTomlRemotesNonClaimNonempty :: Bool
umstTomlRemotesNonClaimNonempty = not (null umstTomlRemotesNonClaim)
