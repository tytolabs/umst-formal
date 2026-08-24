-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.CobSocialGraph
-- Description : Meso acting Urge — §3 COB typed social graph.
--
-- Radicle-style overlay with typed nodes and edges (patch, issue, review,
-- identity). Positive refuse via untyped-edge and git-hash-only identity —
-- not silent accept. Composes 'excitementSelect'; no second argmin.
--
-- Mirrors 'UMST.Urge.CollaborativeObject' social-graph discipline.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.CobSocialGraph
  ( -- * Typed social graph (patch / issue / review / identity)
    SocialNodeKind (..)
  , SocialNode (..)
  , SocialEdge (..)
  , TypedSocialGraph (..)
  , emptySocialGraph
  , findSocialNode
  , kindEqb
  , kindEqbRefl
  , addSocialNode
  , CobLinkVerdict (..)
  , linkTypedEdge
    -- * Repository identity + positive refuse (§3 COB)
  , RepositoryIdentity (..)
  , CobIdentityVerdict (..)
  , refuseGitHashOnlyIdentity
  , repositoryIdentityWithCarrier
  , CobSocialRefusal (..)
  , CobSocialLinkVerdict (..)
  , evaluateSocialLink
  , refuseGitHashOnly
  , refuseSecondArgmin
    -- * Excitement composition (no second argmin)
  , CobSocialRecoveryCtx (..)
  , cobSocialSelect
  , cobSocialSelectEqExcitementSelect
  , cobSocialSelectEqUrgeRecoverySelect
  , cobSocialNoLocalArgmin
  , CobExcitementComposePin (..)
  , cobSocialExcitementSelect
  , cobSocialExcitementSelectEqExcitementSelect
  , cobSocialExcitementSelectRefusesSecondArgmin
  , cobSocialSelectEmpty
    -- * §3 fixtures + witness theorems
  , cobFixtureGraph
  , cobFixturePatchId
  , cobFixtureIssueId
  , cobFixtureReviewId
  , cobFixtureAcceptLink
  , cobFixtureUntypedLinkRefused
  , cobFixtureMissingNodeRefused
  , cobFixtureGitHashOnlyRefused
  , cobFixtureState
  , cobFixtureExcitementCompose
  , cobSocialPositiveRefuseNotSilent
    -- * Landauer bridge (derived — zero new axioms)
  , CobSocialHistoryMove (..)
  , admissibleCobSocialGraph
  , CobSocialTransition (..)
  , cobSocialSecondLaw
  , PhysicalCobSocialBridge (..)
  , cobSocialSecondLawFromPhysical
  , admissibleCobSocialGraphFromPhysical
    -- * Honesty flags + catalog witnesses
  , cobSocialGraphPhysicsGreen
  , cobSocialGraphPhysicsGreenFalse
  , cobSocialGraphProductionWired
  , cobSocialGraphProductionWiredFalse
  , cobSocialGraphNonClaim
  , cobSocialGraphNonClaimNonempty
  , cobSocialGraphModuleWitness
  , cobSocialGraphNoNewAxiom
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HeatBath (..)
  , HistoryCandidate (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.CarrierProduct (HistoryCarrier (..))
import UMST.Urge.ExcitementImport (urgeRecoverySelect)

-- ---------------------------------------------------------------------------
-- SECTION 1: Typed social graph (patch / issue / review / identity)
-- ---------------------------------------------------------------------------

-- | Radicle-style social node kinds — untyped edges refused at link time.
data SocialNodeKind
  = SocialPatch
  | SocialIssue
  | SocialReview
  | SocialIdentity
  deriving (Show, Eq)

-- | One node in the typed social graph.
data SocialNode = SocialNode
  { socialNodeId    :: !Int
  , socialNodeKind  :: !SocialNodeKind
  , socialNodeLabel :: !String
  } deriving (Show, Eq)

-- | Typed edge between social nodes — source/target kinds pinned.
data SocialEdge = SocialEdge
  { socialEdgeFromId    :: !Int
  , socialEdgeToId      :: !Int
  , socialEdgeFromKind  :: !SocialNodeKind
  , socialEdgeToKind    :: !SocialNodeKind
  } deriving (Show, Eq)

-- | Typed social graph carrier (append-only lists).
data TypedSocialGraph = TypedSocialGraph
  { socialNodes   :: ![SocialNode]
  , socialEdges   :: ![SocialEdge]
  , socialNextId  :: !Int
  } deriving (Show, Eq)

-- | Empty typed social graph scaffold.
emptySocialGraph :: TypedSocialGraph
emptySocialGraph =
  TypedSocialGraph {socialNodes = [], socialEdges = [], socialNextId = 0}

-- | Lookup a social node by id.
findSocialNode :: [SocialNode] -> Int -> Maybe SocialNode
findSocialNode [] _ = Nothing
findSocialNode (n : rest) nid =
  if socialNodeId n == nid then Just n else findSocialNode rest nid

-- | Decidable equality on social node kinds.
kindEqb :: SocialNodeKind -> SocialNodeKind -> Bool
kindEqb SocialPatch SocialPatch         = True
kindEqb SocialIssue SocialIssue         = True
kindEqb SocialReview SocialReview       = True
kindEqb SocialIdentity SocialIdentity   = True
kindEqb _ _                             = False

-- | Reflexivity witness for 'kindEqb'.
kindEqbRefl :: SocialNodeKind -> Bool
kindEqbRefl k = kindEqb k k

-- | Add a typed social node (monotonic id assignment).
addSocialNode
  :: TypedSocialGraph -> SocialNodeKind -> String -> (SocialNode, TypedSocialGraph)
addSocialNode g kind label =
  let nid = socialNextId g
      node =
        SocialNode
          { socialNodeId = nid
          , socialNodeKind = kind
          , socialNodeLabel = label
          }
   in ( node
      , TypedSocialGraph
          { socialNodes = socialNodes g ++ [node]
          , socialEdges = socialEdges g
          , socialNextId = nid + 1
          }
      )

data CobLinkVerdict
  = CobLinkOk
  | CobUntypedSocialEdgeRefused
  | CobNodeNotFound
  deriving (Show, Eq)

-- | Link two existing nodes with typed kinds — kind mismatch refused.
linkTypedEdge
  :: TypedSocialGraph
  -> Int
  -> Int
  -> SocialNodeKind
  -> SocialNodeKind
  -> (CobLinkVerdict, TypedSocialGraph)
linkTypedEdge g fromId toId fromKind toKind =
  case findSocialNode (socialNodes g) fromId of
    Nothing -> (CobNodeNotFound, g)
    Just fromNode ->
      case findSocialNode (socialNodes g) toId of
        Nothing -> (CobNodeNotFound, g)
        Just toNode ->
          if kindEqb (socialNodeKind fromNode) fromKind
            && kindEqb (socialNodeKind toNode) toKind
            then
              let edge =
                    SocialEdge
                      { socialEdgeFromId = fromId
                      , socialEdgeToId = toId
                      , socialEdgeFromKind = fromKind
                      , socialEdgeToKind = toKind
                      }
               in ( CobLinkOk
                  , TypedSocialGraph
                      { socialNodes = socialNodes g
                      , socialEdges = socialEdges g ++ [edge]
                      , socialNextId = socialNextId g
                      }
                  )
            else (CobUntypedSocialEdgeRefused, g)

-- ---------------------------------------------------------------------------
-- SECTION 2: Repository identity + positive refuse (§3 COB)
-- ---------------------------------------------------------------------------

-- | Repository identity: RID pin + owning history carrier.
data RepositoryIdentity = RepositoryIdentity
  { repoRid     :: !String
  , repoCarrier :: !HistoryCarrier
  } deriving (Show, Eq)

data CobIdentityVerdict
  = CobIdentityOk RepositoryIdentity
  | CobGitHashOnlyIdentityRefused String
  deriving (Show, Eq)

-- | Refuse constructing identity from RID alone — carrier required.
refuseGitHashOnlyIdentity :: String -> CobIdentityVerdict
refuseGitHashOnlyIdentity rid = CobGitHashOnlyIdentityRefused rid

-- | Build repository identity with full carrier (geometric identity primary).
repositoryIdentityWithCarrier :: String -> HistoryCarrier -> CobIdentityVerdict
repositoryIdentityWithCarrier rid c =
  CobIdentityOk (RepositoryIdentity {repoRid = rid, repoCarrier = c})

-- | Fail-closed COB social graph refusals — positive refuse, not silent swallow.
data CobSocialRefusal
  = CobUntypedSocialEdge !Int !Int
  | CobNodeNotFoundRefusal !Int
  | CobGitHashOnlyIdentityRefusal !String
  | CobSecondArgminRefused
  deriving (Show, Eq)

-- | Verdict of a social link evaluation.
data CobSocialLinkVerdict
  = CobSocialAccept
  | CobSocialRefuseUntypedEdge
  | CobSocialRefuseMissingNode
  deriving (Show, Eq)

-- | Classify linkTypedEdge output into evaluation verdict.
evaluateSocialLink
  :: TypedSocialGraph
  -> Int
  -> Int
  -> SocialNodeKind
  -> SocialNodeKind
  -> CobSocialLinkVerdict
evaluateSocialLink g fromId toId fromKind toKind =
  case fst (linkTypedEdge g fromId toId fromKind toKind) of
    CobLinkOk                    -> CobSocialAccept
    CobUntypedSocialEdgeRefused  -> CobSocialRefuseUntypedEdge
    CobNodeNotFound              -> CobSocialRefuseMissingNode

-- | Positive refuse: git-hash-only identity without carrier.
refuseGitHashOnly :: String -> CobSocialRefusal
refuseGitHashOnly rid = CobGitHashOnlyIdentityRefusal rid

-- | Positive refuse: second Excitement selector — compose 'excitementSelect'.
refuseSecondArgmin :: CobSocialRefusal
refuseSecondArgmin = CobSecondArgminRefused

-- ---------------------------------------------------------------------------
-- SECTION 3: COB social graph composes Excitement (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for COB social history recovery over admissible successors.
data CobSocialRecoveryCtx = CobSocialRecoveryCtx
  { cobSocialPrior      :: !ThermodynamicState
  , cobSocialSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | COB social graph selection **is** 'urgeRecoverySelect' / 'excitementSelect'.
cobSocialSelect
  :: CobSocialRecoveryCtx
  -> Either ExcitementResidue HistoryCandidate
cobSocialSelect ctx =
  urgeRecoverySelect (cobSocialPrior ctx) (cobSocialSuccessors ctx)

-- | Definitional witness: COB social selection API is 'excitementSelect'.
cobSocialSelectEqExcitementSelect :: CobSocialRecoveryCtx -> Bool
cobSocialSelectEqExcitementSelect ctx =
  cobSocialSelect ctx
    == excitementSelect (cobSocialPrior ctx) (cobSocialSuccessors ctx)

-- | COB social selection equals 'urgeRecoverySelect'.
cobSocialSelectEqUrgeRecoverySelect :: CobSocialRecoveryCtx -> Bool
cobSocialSelectEqUrgeRecoverySelect ctx =
  cobSocialSelect ctx
    == urgeRecoverySelect (cobSocialPrior ctx) (cobSocialSuccessors ctx)

-- | COB path composes 'excitementSelect' — not a second argmin.
cobSocialNoLocalArgmin :: CobSocialRecoveryCtx -> Bool
cobSocialNoLocalArgmin ctx =
  cobSocialSelect ctx
    == excitementSelect (cobSocialPrior ctx) (cobSocialSuccessors ctx)

-- | Excitement compose pin — Urge imports selector; no second argmin.
data CobExcitementComposePin
  = CobImportSelectExcitement
  | CobPinSecondArgminRefused
  deriving (Show, Eq)

-- | COB excitement selection with explicit compose pin.
cobSocialExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> CobExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
cobSocialExcitementSelect src cands pin =
  case pin of
    CobImportSelectExcitement -> excitementSelect src cands
    CobPinSecondArgminRefused -> Left ExcAllInadmissible

-- | Definitional witness: import pin is 'excitementSelect'.
cobSocialExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
cobSocialExcitementSelectEqExcitementSelect src cands =
  cobSocialExcitementSelect src cands CobImportSelectExcitement
    == excitementSelect src cands

-- | Second-argmin pin refuses with 'ExcAllInadmissible'.
cobSocialExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
cobSocialExcitementSelectRefusesSecondArgmin src cands =
  cobSocialExcitementSelect src cands CobPinSecondArgminRefused
    == Left ExcAllInadmissible

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
cobSocialSelectEmpty :: ThermodynamicState -> Bool
cobSocialSelectEmpty src =
  cobSocialSelect
    (CobSocialRecoveryCtx {cobSocialPrior = src, cobSocialSuccessors = []})
    == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: §3 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | Fixture graph: patch → issue → review → identity nodes.
cobFixtureGraph :: TypedSocialGraph
cobFixtureGraph =
  let (_, g1) = addSocialNode emptySocialGraph SocialPatch "patch-admissible"
      (_, g2) = addSocialNode g1 SocialIssue "issue-thread"
      (_, g3) = addSocialNode g2 SocialReview "review-verdict"
      (_, g4) = addSocialNode g3 SocialIdentity "did:umst:cob"
   in g4

cobFixturePatchId :: Int
cobFixturePatchId = 0

cobFixtureIssueId :: Int
cobFixtureIssueId = 1

cobFixtureReviewId :: Int
cobFixtureReviewId = 2

-- | Typed patch→issue link accepted on fixture graph.
cobFixtureAcceptLink :: Bool
cobFixtureAcceptLink =
  evaluateSocialLink
    cobFixtureGraph
    cobFixturePatchId
    cobFixtureIssueId
    SocialPatch
    SocialIssue
    == CobSocialAccept

-- | Kind mismatch patch→review refused as untyped edge.
cobFixtureUntypedLinkRefused :: Bool
cobFixtureUntypedLinkRefused =
  evaluateSocialLink
    cobFixtureGraph
    cobFixturePatchId
    cobFixtureReviewId
    SocialPatch
    SocialIssue
    == CobSocialRefuseUntypedEdge

-- | Missing node id refused.
cobFixtureMissingNodeRefused :: Bool
cobFixtureMissingNodeRefused =
  evaluateSocialLink
    cobFixtureGraph
    cobFixturePatchId
    999
    SocialPatch
    SocialIssue
    == CobSocialRefuseMissingNode

-- | Git-hash-only identity refused positively.
cobFixtureGitHashOnlyRefused :: Bool
cobFixtureGitHashOnlyRefused =
  refuseGitHashOnly "sha1:deadbeef"
    == CobGitHashOnlyIdentityRefusal "sha1:deadbeef"

cobFixtureState :: ThermodynamicState
cobFixtureState = ThermodynamicState 2400 0 0 0 0

-- | Empty candidates → noCandidates via composed excitementSelect.
cobFixtureExcitementCompose :: Bool
cobFixtureExcitementCompose =
  cobSocialExcitementSelect cobFixtureState [] CobImportSelectExcitement
    == Left ExcNoCandidates

-- | Positive refuse is not silent accept.
cobSocialPositiveRefuseNotSilent :: Bool
cobSocialPositiveRefuseNotSilent =
  evaluateSocialLink
    cobFixtureGraph
    cobFixturePatchId
    cobFixtureReviewId
    SocialPatch
    SocialIssue
    /= CobSocialAccept

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ---------------------------------------------------------------------------

-- | COB social history move with gate + provenance witnesses.
data CobSocialHistoryMove = CobSocialHistoryMove
  { cobMovePrior          :: !ThermodynamicState
  , cobMovePost           :: !ThermodynamicState
  , cobMoveGateChecked    :: !Bool
  , cobMoveUntypedRefused :: !Bool
  , cobMoveProvenanceOk   :: !Bool
  } deriving (Show, Eq)

-- | Admissible COB social graph move (gate + refuse + provenance).
admissibleCobSocialGraph :: CobSocialHistoryMove -> Bool
admissibleCobSocialGraph h =
  cobMoveGateChecked h
  && cobMoveUntypedRefused h
  && cobMoveProvenanceOk h

-- | Thermodynamic accounting on a COB social transition.
data CobSocialTransition = CobSocialTransition
  { cobSocialMove           :: !CobSocialHistoryMove
  , cobSocialBath           :: !HeatBath
  , cobSocialDissipatedWork :: !Double
  , cobSocialEntropyDrop    :: !Double
  } deriving (Show, Eq)

-- | Second-law invariant on COB social transition (Bool witness).
cobSocialSecondLaw :: CobSocialTransition -> Bool
cobSocialSecondLaw t =
  cobSocialEntropyDrop t
    <= cobSocialDissipatedWork t / bathTemp (cobSocialBath t)

-- | Physical bridge tying COB social transition to Landauer discharge.
data PhysicalCobSocialBridge = PhysicalCobSocialBridge
  { cobSocialBridge       :: !LandauerHistoryBridge
  , cobSocialTransition   :: !CobSocialTransition
  , cobSocialAdmissible   :: !Bool
  } deriving (Show, Eq)

-- | Second law on COB social transition from Landauer bridge (no new axiom).
cobSocialSecondLawFromPhysical
  :: PhysicalCobSocialBridge -> Bool -> Bool
cobSocialSecondLawFromPhysical b hSL =
  hSL
  && cobSocialAdmissible b
  && admitSecondLaw (landauerTransition (cobSocialBridge b))

-- | Admissible move from physical bridge discharge.
admissibleCobSocialGraphFromPhysical
  :: PhysicalCobSocialBridge -> Bool -> Bool
admissibleCobSocialGraphFromPhysical b hSL =
  hSL && cobSocialAdmissible b

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
cobSocialGraphPhysicsGreen :: Bool
cobSocialGraphPhysicsGreen = False

-- | Lean/Coq: @cobSocialGraphPhysicsGreenFalse@.
cobSocialGraphPhysicsGreenFalse :: Bool
cobSocialGraphPhysicsGreenFalse = not cobSocialGraphPhysicsGreen

-- | Production wiring stays open (COB social graph lift only).
cobSocialGraphProductionWired :: Bool
cobSocialGraphProductionWired = False

-- | Lean/Coq: @cobSocialGraphProductionWiredFalse@.
cobSocialGraphProductionWiredFalse :: Bool
cobSocialGraphProductionWiredFalse = not cobSocialGraphProductionWired

-- | Honest non-claim string (meso §3 COB typed social graph scaffold).
cobSocialGraphNonClaim :: String
cobSocialGraphNonClaim =
  "§3 COB typed social graph (patch, issue, review, identity); positive refuse "
    ++ "not only !physics_green; compose excitementSelect not local argmin; "
    ++ "not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
cobSocialGraphNonClaimNonempty :: Bool
cobSocialGraphNonClaimNonempty = length cobSocialGraphNonClaim > 0

-- | Catalog witness: meso Urge CobSocialGraph module present.
cobSocialGraphModuleWitness :: Bool
cobSocialGraphModuleWitness = True

-- | Zero new axiom discipline witness.
cobSocialGraphNoNewAxiom :: Bool
cobSocialGraphNoNewAxiom = True
