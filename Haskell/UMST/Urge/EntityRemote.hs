-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.EntityRemote
-- Description : Meso acting Urge — §13.6 entity remotes classification.
--
-- `[urge.remote.*]` policy types; pre-push refuse github /
-- origin.cursor.com when entity = compose. Classified remotes — not origin SSOT.
--
-- Entity remote recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.EntityRemote
  ( -- * §13.6 `[urge.remote.*]` policy carriers
    urgeRemoteSectionPrefix
  , UrgeEntity (..)
  , RemoteClassification (..)
  , CanonicalRemote (..)
  , MirrorRemote (..)
  , EntityRemoteHost (..)
  , UrgeRemotePolicy (..)
  , EntityPrePushVerdict (..)
  , EntityPrePushRefusal (..)
  , EntityRemoteVerdict (..)
    -- * Admissibility conjunct + positive refuse
  , EntityRemoteConjunct (..)
  , entityRemoteConjunctAdmits
  , classificationEntity
  , parseUrgeEntity
  , classifyEntityRemoteHost
  , evaluateEntityPrePush
  , refuseProductionWiredEntityPush
  , evaluateEntityRemoteOperation
  , applyEntityRemotePolicy
  , entityRemoteUpstreamRefusedPositive
  , entityRemotePolicyOkWhenNotUpstream
  , refuseProductionWiredEntityPushPositive
    -- * Excitement alignment (no second argmin)
  , EntityRemoteCtx (..)
  , entityRemoteSelect
  , entityRemoteSelectEqExcitementSelect
  , entityRemoteSelectEqUrgeRecoverySelect
  , entityRemoteNoLocalArgmin
  , entityRemoteEmpty
    -- * §13.6 fixtures + witness theorems
  , entityRemoteFixtureLabsPublic
  , entityRemoteFixtureComposeConfidential
  , entityRemoteFixtureConjunct
  , entityRemoteFixtureState
  , entityRemoteLabsGithubAdmitted
  , entityRemoteComposeGithubRefused
  , entityRemoteComposeOriginRefused
  , entityRemoteOriginNeverSsotRefused
  , entityRemoteComposeForgeAdmitted
  , entityRemoteSectionPrefixWitness
  , entityRemoteLabsPublicSectionKey
  , entityRemoteParseLabs
  , entityRemoteParseCompose
  , entityRemoteClassificationEntityLabs
  , entityRemoteClassificationEntityCompose
  , entityRemoteFixtureApplyPolicyOk
  , entityRemotePositiveRefuseNotSilent
  , entityRemoteComposeGithubPositiveRefuse
    -- * Landauer bridge (derived — zero new axioms)
  , EntityRemoteHistoryMove (..)
  , admissibleEntityRemote
  , EntityRemoteTransition (..)
  , entityRemoteSecondLaw
  , PhysicalEntityRemoteBridge (..)
  , entityRemoteSecondLawFromPhysical
  , entityRemoteSecondLawFromLandauer
  , physicalSecondLawImported
  , admissibleEntityRemoteFromPhysical
    -- * Honesty flags + catalog witnesses
  , entityRemotePhysicsGreen
  , entityRemotePhysicsGreenFalse
  , entityRemoteProductionWired
  , entityRemoteProductionWiredFalse
  , entityRemoteModuleWitness
  , entityRemoteNoNewAxiom
  , entityRemoteNoSecondArgmin
  , entityRemoteNonClaim
  , entityRemoteNonClaimNonempty
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
  , bathTemp
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.ExcitementImport (urgeRecoverySelect)

-- ---------------------------------------------------------------------------
-- SECTION 1: §13.6 `[urge.remote.*]` policy carriers
-- ---------------------------------------------------------------------------

-- | `umst.toml` section prefix for remote policy rows.
urgeRemoteSectionPrefix :: String
urgeRemoteSectionPrefix = "urge.remote."

-- | Entity label in `[urge.remote.*]` — Labs vs Compose.
data UrgeEntity
  = UrgeLabs
  | UrgeCompose
  deriving (Show, Eq)

-- | Share-security classification label (§13.6 table).
data RemoteClassification
  = RcPublicOss
  | RcLabsInternal
  | RcComposeConfidential
  | RcComposeDefence
  | RcProposalConfidential
  deriving (Show, Eq)

-- | Canonical remote role — India-resident Forgejo is SSOT after restore test.
data CanonicalRemote
  = CrForge
  | CrNone
  deriving (Show, Eq)

-- | Mirror remote role — GitHub interim / public discovery only.
data MirrorRemote
  = MrGithub
  | MrNone
  deriving (Show, Eq)

-- | Push target host for pre-push policy evaluation (§16.8).
data EntityRemoteHost
  = ErhGithub
  | ErhOriginCursor
  | ErhForge
  | ErhUnclassified
  deriving (Show, Eq)

-- | One `[urge.remote.*]` policy row from `umst.toml` (proposed §13.6).
data UrgeRemotePolicy = UrgeRemotePolicy
  { erpSection         :: !String
  , erpEntity          :: !UrgeEntity
  , erpClassification  :: !RemoteClassification
  , erpCanonical       :: !CanonicalRemote
  , erpMirror          :: !MirrorRemote
  } deriving (Show, Eq)

-- | Pre-push verdict for entity remote policy.
data EntityPrePushVerdict
  = EppvAdmitted
  | EppvComposeGithubRefused
  | EppvComposeOriginRefused
  | EppvOriginNeverSsotRefused
  | EppvUnclassifiedHostRefused
  | EppvProductionWiredRefused
  deriving (Show, Eq)

-- | Fail-closed pre-push errors — positive refuse, not silent no-op.
data EntityPrePushRefusal
  = EpprComposeGithubRefused
  | EpprComposeOriginRefused
  | EpprOriginNeverSsotRefused
  | EpprUnclassifiedHostRefused !EntityRemoteHost
  | EpprProductionWiredRefused
  deriving (Show, Eq)

-- | Verdict of entity remote classification operation class.
data EntityRemoteVerdict
  = ErvPolicyOk
  | ErvUpstreamRefused
  | ErvInadmissible
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §13.6 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §13.6 admissibility conjunct inputs (surrogate).
data EntityRemoteConjunct = EntityRemoteConjunct
  { ercGateOk              :: !Bool
  , ercPolicyTyped         :: !Bool
  , ercExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate `admit(h) ⟺ gate ∧ policy typed ∧ Excitement preserves`.
entityRemoteConjunctAdmits :: EntityRemoteConjunct -> Bool
entityRemoteConjunctAdmits c =
  ercGateOk c && ercPolicyTyped c && ercExcitementPreserves c

-- | Owning entity for a share-security classification.
classificationEntity :: RemoteClassification -> UrgeEntity
classificationEntity c =
  case c of
    RcPublicOss -> UrgeLabs
    RcLabsInternal -> UrgeLabs
    RcProposalConfidential -> UrgeLabs
    RcComposeConfidential -> UrgeCompose
    RcComposeDefence -> UrgeCompose

-- | Parse entity label from `umst.toml` value (fail closed on unknown).
parseUrgeEntity :: String -> Maybe UrgeEntity
parseUrgeEntity tag =
  if tag == "labs" || tag == "LABS" then Just UrgeLabs
  else if tag == "compose" || tag == "COMPOSE" then Just UrgeCompose
  else Nothing

-- | Classify push target from host string (typed surrogate).
classifyEntityRemoteHost :: String -> EntityRemoteHost
classifyEntityRemoteHost host =
  if null host then ErhUnclassified
  else if host == "origin.cursor.com" then ErhOriginCursor
  else if host == "github.com" then ErhGithub
  else if host == "forge.tyto.in" || host == "forge.entity" then ErhForge
  else ErhUnclassified

labsGithubVerdict :: RemoteClassification -> Either EntityPrePushVerdict EntityPrePushRefusal
labsGithubVerdict c =
  if c == RcPublicOss then Left EppvAdmitted
  else Right (EpprUnclassifiedHostRefused ErhGithub)

-- | Evaluate pre-push under §13.6 entity remote policy and §16.8 host table.
evaluateEntityPrePush
  :: UrgeRemotePolicy -> String -> Either EntityPrePushVerdict EntityPrePushRefusal
evaluateEntityPrePush policy host =
  case classifyEntityRemoteHost host of
    ErhOriginCursor ->
      case erpEntity policy of
        UrgeCompose -> Right EpprComposeOriginRefused
        UrgeLabs -> Right EpprOriginNeverSsotRefused
    ErhGithub ->
      case erpEntity policy of
        UrgeCompose -> Right EpprComposeGithubRefused
        UrgeLabs -> labsGithubVerdict (erpClassification policy)
    ErhForge -> Left EppvAdmitted
    ErhUnclassified -> Right (EpprUnclassifiedHostRefused ErhUnclassified)

-- | Positive refuse: production wired push without entity remote policy.
refuseProductionWiredEntityPush :: EntityPrePushRefusal
refuseProductionWiredEntityPush = EpprProductionWiredRefused

-- | Classify blind upstream vs typed policy without performing I/O.
evaluateEntityRemoteOperation :: Bool -> EntityRemoteVerdict
evaluateEntityRemoteOperation isUpstreamRefused =
  if isUpstreamRefused then ErvUpstreamRefused else ErvPolicyOk

-- | Apply typed entity remote policy check — fail closed on inadmissibility.
applyEntityRemotePolicy
  :: UrgeRemotePolicy
  -> String
  -> EntityRemoteConjunct
  -> Bool
  -> Either UrgeRemotePolicy EntityPrePushRefusal
applyEntityRemotePolicy policy host conjunct excitementSelected =
  if not (entityRemoteConjunctAdmits conjunct) then
    Right (EpprUnclassifiedHostRefused ErhUnclassified)
  else if not excitementSelected then
    Right (EpprUnclassifiedHostRefused ErhUnclassified)
  else
    case evaluateEntityPrePush policy host of
      Left _ -> Left policy
      Right r -> Right r

-- | Upstream refused classifies as upstream-refused.
entityRemoteUpstreamRefusedPositive :: Bool
entityRemoteUpstreamRefusedPositive =
  evaluateEntityRemoteOperation True == ErvUpstreamRefused

-- | Non-upstream classifies as policy-ok.
entityRemotePolicyOkWhenNotUpstream :: Bool
entityRemotePolicyOkWhenNotUpstream =
  evaluateEntityRemoteOperation False == ErvPolicyOk

-- | Production-wired refuse witness is the canonical refusal constructor.
refuseProductionWiredEntityPushPositive :: Bool
refuseProductionWiredEntityPushPositive =
  refuseProductionWiredEntityPush == EpprProductionWiredRefused

-- ---------------------------------------------------------------------------
-- SECTION 3: Entity remote composes Excitement (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for entity remote over admissible history successors.
data EntityRemoteCtx = EntityRemoteCtx
  { entityRemoteSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Entity remote selection **is** 'urgeRecoverySelect' / 'excitementSelect'.
entityRemoteSelect
  :: ThermodynamicState
  -> EntityRemoteCtx
  -> Either ExcitementResidue HistoryCandidate
entityRemoteSelect src ctx =
  urgeRecoverySelect src (entityRemoteSuccessors ctx)

-- | Definitional witness: entity remote selection API is 'excitementSelect'.
entityRemoteSelectEqExcitementSelect
  :: ThermodynamicState -> EntityRemoteCtx -> Bool
entityRemoteSelectEqExcitementSelect src ctx =
  entityRemoteSelect src ctx
    == excitementSelect src (entityRemoteSuccessors ctx)

-- | Definitional witness: entity remote selection API is 'urgeRecoverySelect'.
entityRemoteSelectEqUrgeRecoverySelect
  :: ThermodynamicState -> EntityRemoteCtx -> Bool
entityRemoteSelectEqUrgeRecoverySelect src ctx =
  entityRemoteSelect src ctx
    == urgeRecoverySelect src (entityRemoteSuccessors ctx)

-- | Entity remote selector re-uses 'excitementSelect' — no Urge-local argmin.
entityRemoteNoLocalArgmin :: ThermodynamicState -> EntityRemoteCtx -> Bool
entityRemoteNoLocalArgmin src ctx =
  entityRemoteSelect src ctx
    == excitementSelect src (entityRemoteSuccessors ctx)

-- | Empty successor list yields no-candidates residue.
entityRemoteEmpty :: ThermodynamicState -> Bool
entityRemoteEmpty src =
  entityRemoteSelect src (EntityRemoteCtx []) == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: §13.6 fixtures + witness theorems
-- ---------------------------------------------------------------------------

entityRemoteFixtureLabsPublic :: UrgeRemotePolicy
entityRemoteFixtureLabsPublic =
  UrgeRemotePolicy
    { erpSection = "labs-public"
    , erpEntity = UrgeLabs
    , erpClassification = RcPublicOss
    , erpCanonical = CrForge
    , erpMirror = MrGithub
    }

entityRemoteFixtureComposeConfidential :: UrgeRemotePolicy
entityRemoteFixtureComposeConfidential =
  UrgeRemotePolicy
    { erpSection = "compose-confidential"
    , erpEntity = UrgeCompose
    , erpClassification = RcComposeConfidential
    , erpCanonical = CrForge
    , erpMirror = MrNone
    }

entityRemoteFixtureConjunct :: EntityRemoteConjunct
entityRemoteFixtureConjunct =
  EntityRemoteConjunct
    { ercGateOk = True
    , ercPolicyTyped = True
    , ercExcitementPreserves = True
    }

entityRemoteFixtureState :: ThermodynamicState
entityRemoteFixtureState = ThermodynamicState 2400 0 0 0 0

entityRemoteLabsGithubAdmitted :: Bool
entityRemoteLabsGithubAdmitted =
  evaluateEntityPrePush entityRemoteFixtureLabsPublic "github.com"
    == Left EppvAdmitted

entityRemoteComposeGithubRefused :: Bool
entityRemoteComposeGithubRefused =
  evaluateEntityPrePush entityRemoteFixtureComposeConfidential "github.com"
    == Right EpprComposeGithubRefused

entityRemoteComposeOriginRefused :: Bool
entityRemoteComposeOriginRefused =
  evaluateEntityPrePush entityRemoteFixtureComposeConfidential "origin.cursor.com"
    == Right EpprComposeOriginRefused

entityRemoteOriginNeverSsotRefused :: Bool
entityRemoteOriginNeverSsotRefused =
  evaluateEntityPrePush entityRemoteFixtureLabsPublic "origin.cursor.com"
    == Right EpprOriginNeverSsotRefused

entityRemoteComposeForgeAdmitted :: Bool
entityRemoteComposeForgeAdmitted =
  evaluateEntityPrePush entityRemoteFixtureComposeConfidential "forge.tyto.in"
    == Left EppvAdmitted

entityRemoteSectionPrefixWitness :: Bool
entityRemoteSectionPrefixWitness =
  urgeRemoteSectionPrefix == "urge.remote."

entityRemoteLabsPublicSectionKey :: Bool
entityRemoteLabsPublicSectionKey =
  urgeRemoteSectionPrefix ++ erpSection entityRemoteFixtureLabsPublic
    == "urge.remote.labs-public"

entityRemoteParseLabs :: Bool
entityRemoteParseLabs = parseUrgeEntity "labs" == Just UrgeLabs

entityRemoteParseCompose :: Bool
entityRemoteParseCompose = parseUrgeEntity "compose" == Just UrgeCompose

entityRemoteClassificationEntityLabs :: Bool
entityRemoteClassificationEntityLabs =
  classificationEntity RcPublicOss == UrgeLabs

entityRemoteClassificationEntityCompose :: Bool
entityRemoteClassificationEntityCompose =
  classificationEntity RcComposeConfidential == UrgeCompose

entityRemoteFixtureApplyPolicyOk :: Bool
entityRemoteFixtureApplyPolicyOk =
  applyEntityRemotePolicy
    entityRemoteFixtureLabsPublic
    "forge.tyto.in"
    entityRemoteFixtureConjunct
    True
    == Left entityRemoteFixtureLabsPublic

entityRemotePositiveRefuseNotSilent :: Bool
entityRemotePositiveRefuseNotSilent =
  evaluateEntityRemoteOperation True /= ErvPolicyOk

entityRemoteComposeGithubPositiveRefuse :: Bool
entityRemoteComposeGithubPositiveRefuse =
  evaluateEntityPrePush entityRemoteFixtureComposeConfidential "github.com"
    /= Left EppvAdmitted

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | History move accounting for entity remote policy (acting meso layer).
data EntityRemoteHistoryMove = EntityRemoteHistoryMove
  { ermPrior         :: !ThermodynamicState
  , ermPost          :: !ThermodynamicState
  , ermGateChecked   :: !Bool
  , ermPolicyTyped   :: !Bool
  , ermProvenanceOk  :: !Bool
  } deriving (Show, Eq)

-- | Admissible entity remote move: gate + typed policy + provenance intact.
admissibleEntityRemote :: EntityRemoteHistoryMove -> Bool
admissibleEntityRemote h =
  ermGateChecked h && ermPolicyTyped h && ermProvenanceOk h

-- | Thermodynamic accounting on an entity remote transition.
data EntityRemoteTransition = EntityRemoteTransition
  { ertMove            :: !EntityRemoteHistoryMove
  , ertBath            :: !HeatBath
  , ertDissipatedWork  :: !Double
  , ertEntropyDrop     :: !Double
  } deriving (Show, Eq)

-- | Named second-law invariant on entity remote transition (Bool witness).
entityRemoteSecondLaw :: EntityRemoteTransition -> Bool
entityRemoteSecondLaw t =
  ertEntropyDrop t <= ertDissipatedWork t / bathTemp (ertBath t)

-- | Physical bridge tying Landauer process to entity remote transition.
data PhysicalEntityRemoteBridge = PhysicalEntityRemoteBridge
  { perLandauerBridge :: !LandauerHistoryBridge
  , perTransition     :: !EntityRemoteTransition
  , perAdmissible     :: !Bool
  } deriving (Show, Eq)

-- | Second law on entity remote transition from Landauer bridge discharge.
entityRemoteSecondLawFromPhysical :: PhysicalEntityRemoteBridge -> Bool -> Bool
entityRemoteSecondLawFromPhysical b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge
       (perLandauerBridge b)
       hSL
  && admitSecondLaw (landauerTransition (perLandauerBridge b))
  && entityRemoteSecondLaw (perTransition b)

-- | Second law on entity remote carrier transition from Landauer bridge.
entityRemoteSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
entityRemoteSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical second law imported from Lean @LandauerLaw.physicalSecondLaw@.
physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

-- | Admissible entity remote move under physical bridge (no new axiom).
admissibleEntityRemoteFromPhysical :: PhysicalEntityRemoteBridge -> Bool -> Bool
admissibleEntityRemoteFromPhysical b hSL =
  hSL && perAdmissible b
  && admissibleEntityRemote (ertMove (perTransition b))

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
entityRemotePhysicsGreen :: Bool
entityRemotePhysicsGreen = False

-- | Lean/Coq: @entity_remote_physics_green_false@.
entityRemotePhysicsGreenFalse :: Bool
entityRemotePhysicsGreenFalse = not entityRemotePhysicsGreen

-- | Production wiring stays open (meso lift only).
entityRemoteProductionWired :: Bool
entityRemoteProductionWired = False

-- | Lean/Coq: @entity_remote_production_wired_false@.
entityRemoteProductionWiredFalse :: Bool
entityRemoteProductionWiredFalse = not entityRemoteProductionWired

-- | Catalog witness: meso Urge EntityRemote module present.
entityRemoteModuleWitness :: Bool
entityRemoteModuleWitness = True

-- | Zero new axiom discipline witness.
entityRemoteNoNewAxiom :: Bool
entityRemoteNoNewAxiom = True

-- | Second-argmin refusal: entity remote composes 'excitementSelect' only.
entityRemoteNoSecondArgmin :: Bool
entityRemoteNoSecondArgmin =
  entityRemoteNoLocalArgmin entityRemoteFixtureState (EntityRemoteCtx [])

-- | Honest non-claim string (meso §13.6 entity remote scaffold).
entityRemoteNonClaim :: String
entityRemoteNonClaim =
  "§13.6 entity remotes [urge.remote.*] policy types; classified remotes not origin; "
    ++ "pre-push refuse github/origin when compose; compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
entityRemoteNonClaimNonempty :: Bool
entityRemoteNonClaimNonempty = length entityRemoteNonClaim > 0
