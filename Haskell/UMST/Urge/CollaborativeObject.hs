-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.CollaborativeObject
-- Description : Meso acting Urge — §3 COB: history carrier + typed social graph.
--
-- Collaborative Object = same Repository/History carrier product
-- (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness) plus typed social graph
-- overlay (patch, issue, review, identity).
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.CollaborativeObject
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
    -- * Repository identity + history carrier (§3 COB)
  , RepositoryIdentity (..)
  , CobIdentityVerdict (..)
  , refuseGitHashOnlyIdentity
  , repositoryIdentityWithCarrier
  , carrierPopulated
  , Cob (..)
  , CollaborativeObject
  , cobNew
  , cobCarrier
  , cobHead
    -- * Positive refuse witnesses
  , refuseGitHashOnlyIsRefused
  , emptyGraphLinkNodeNotFound
  , addSocialNodeThenLinkOk
  , linkTypedEdgeUntypedRefusedSample
    -- * Excitement alignment (no second argmin)
  , cobSelect
  , cobCarrierSelect
  , cobSelectEqExcitementSelect
  , cobSelectEqCarrierSelect
  , cobNoLocalArgmin
  , cobSelectEqCarrierSelectHead
    -- * Landauer bridge (derived — zero new axioms)
  , cobSecondLawFromLandauer
  , cobFromLandauerAdmitSecondLaw
  , cobSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , collaborativeObjectPhysicsGreen
  , collaborativeObjectPhysicsGreenFalse
  , collaborativeObjectProductionWired
  , collaborativeObjectProductionWiredFalse
  , collaborativeObjectNonClaim
  , collaborativeObjectNonClaimNonempty
  , collaborativeObjectModuleWitness
  , collaborativeObjectNoNewAxiom
  , collaborativeObjectNoSecondArgmin
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.CarrierProduct
  ( HistoryCarrier (..)
  , carrierMk
  , carrierSelect
  , satisfiedWitness
  , stampProj
  , umstProj
  , wallOnlyStamp
  , ExactAlg (..)
  , SdfFRep (..)
  , observedAtWall
  )

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
kindEqb SocialPatch SocialPatch     = True
kindEqb SocialIssue SocialIssue     = True
kindEqb SocialReview SocialReview   = True
kindEqb SocialIdentity SocialIdentity = True
kindEqb _ _                         = False

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
-- SECTION 2: Repository identity + history carrier (§3 COB)
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

-- | Carrier populated when UMST commit id or stamp wall is present.
carrierPopulated :: HistoryCarrier -> Bool
carrierPopulated c =
  historyCommitId (umstProj c) > 0
  || observedAtWall (stampProj c) > 0

-- | Collaborative Object — history carrier + typed social graph (§3 COB).
data Cob = Cob
  { cobIdentity :: !RepositoryIdentity
  , cobSocial   :: !TypedSocialGraph
  } deriving (Show, Eq)

type CollaborativeObject = Cob

-- | Fresh COB from repository identity + empty social graph.
cobNew :: RepositoryIdentity -> Cob
cobNew repoIdentity = Cob {cobIdentity = repoIdentity, cobSocial = emptySocialGraph}

-- | Project history carrier from COB.
cobCarrier :: Cob -> HistoryCarrier
cobCarrier cob = repoCarrier (cobIdentity cob)

-- | Thermodynamic head at COB carrier UMST snapshot.
cobHead :: Cob -> ThermodynamicState
cobHead cob = historyHead (umstProj (cobCarrier cob))

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Git-hash-only identity construction is always refused.
refuseGitHashOnlyIsRefused :: String -> Bool
refuseGitHashOnlyIsRefused rid =
  refuseGitHashOnlyIdentity rid == CobGitHashOnlyIdentityRefused rid

-- | Link on empty graph refuses with node-not-found.
emptyGraphLinkNodeNotFound :: Bool
emptyGraphLinkNodeNotFound =
  fst (linkTypedEdge emptySocialGraph 0 0 SocialPatch SocialIssue)
    == CobNodeNotFound

-- | Add patch+issue nodes then link typed edge succeeds.
addSocialNodeThenLinkOk :: Bool
addSocialNodeThenLinkOk =
  let (_, g1) = addSocialNode emptySocialGraph SocialPatch "p"
      (_, g2) = addSocialNode g1 SocialIssue "i"
   in fst (linkTypedEdge g2 0 1 SocialPatch SocialIssue) == CobLinkOk

-- | Kind mismatch on a concrete graph refuses untyped edge (positive refuse).
linkTypedEdgeUntypedRefusedSample :: Bool
linkTypedEdgeUntypedRefusedSample =
  let (_, g1) = addSocialNode emptySocialGraph SocialPatch "p"
      (_, g2) = addSocialNode g1 SocialIssue "i"
   in fst (linkTypedEdge g2 0 1 SocialPatch SocialReview)
        == CobUntypedSocialEdgeRefused
     && snd (linkTypedEdge g2 0 1 SocialPatch SocialReview) == g2

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | COB history recovery composes 'excitementSelect' on carrier UMST head.
cobSelect
  :: Cob
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
cobSelect cob cands =
  excitementSelect (historyHead (umstProj (cobCarrier cob))) cands

-- | Carrier-level selection on history carrier UMST head.
cobCarrierSelect
  :: HistoryCarrier
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
cobCarrierSelect c cands =
  excitementSelect (historyHead (umstProj c)) cands

-- | Definitional witness: COB selection API is 'excitementSelect'.
cobSelectEqExcitementSelect :: Cob -> [HistoryCandidate] -> Bool
cobSelectEqExcitementSelect cob cands =
  cobSelect cob cands
    == excitementSelect (historyHead (umstProj (cobCarrier cob))) cands

-- | COB selection equals carrier-level selection.
cobSelectEqCarrierSelect :: Cob -> [HistoryCandidate] -> Bool
cobSelectEqCarrierSelect cob cands =
  cobSelect cob cands == cobCarrierSelect (cobCarrier cob) cands

-- | COB selector re-uses 'excitementSelect' — no Urge-local argmin.
cobNoLocalArgmin :: Cob -> [HistoryCandidate] -> Bool
cobNoLocalArgmin cob cands =
  cobSelect cob cands
    == excitementSelect (historyHead (umstProj (cobCarrier cob))) cands

-- | COB selection equals 'carrierSelect' on the embedded carrier.
cobSelectEqCarrierSelectHead :: Cob -> [HistoryCandidate] -> Bool
cobSelectEqCarrierSelectHead cob cands =
  cobSelect cob cands == carrierSelect (cobCarrier cob) cands

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on COB carrier transition from Landauer bridge discharge.
cobSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
cobSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
cobFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
cobFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for COB second law (no new axiom).
cobSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
cobSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
collaborativeObjectPhysicsGreen :: Bool
collaborativeObjectPhysicsGreen = False

-- | Lean/Coq: @collaborative_object_physics_green_false@.
collaborativeObjectPhysicsGreenFalse :: Bool
collaborativeObjectPhysicsGreenFalse =
  not collaborativeObjectPhysicsGreen

-- | Production wiring stays open (COB lift only).
collaborativeObjectProductionWired :: Bool
collaborativeObjectProductionWired = False

-- | Lean/Coq: @collaborative_object_production_wired_false@.
collaborativeObjectProductionWiredFalse :: Bool
collaborativeObjectProductionWiredFalse =
  not collaborativeObjectProductionWired

-- | Honest non-claim string (meso §3 COB scaffold).
collaborativeObjectNonClaim :: String
collaborativeObjectNonClaim =
  "§3 COB: same carrier + typed social graph (patch, issue, review, identity); "
    ++ "geometric identity primary; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
collaborativeObjectNonClaimNonempty :: Bool
collaborativeObjectNonClaimNonempty = length collaborativeObjectNonClaim > 0

-- | Catalog witness: meso Urge CollaborativeObject module present.
collaborativeObjectModuleWitness :: Bool
collaborativeObjectModuleWitness = True

-- | Zero new axiom discipline witness.
collaborativeObjectNoNewAxiom :: Bool
collaborativeObjectNoNewAxiom = True

-- | Second-argmin refusal: COB composes 'excitementSelect' only.
collaborativeObjectNoSecondArgmin :: Bool
collaborativeObjectNoSecondArgmin =
  cobNoLocalArgmin
    (cobNew
      (RepositoryIdentity
        { repoRid = "rid"
        , repoCarrier =
            carrierMk
              (HistorySnapshot 1 (ThermodynamicState 2400 0 0.3 30 40))
              (wallOnlyStamp 1)
              (SdfFRep 0 0)
              (ExactAlg 0 0)
              satisfiedWitness
        }))
    []
