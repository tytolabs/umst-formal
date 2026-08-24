-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.OriginRefuse
-- Description : Meso acting Urge — §16.8 origin.cursor.com / GitHub-as-origin refuse.
--
-- India-resident Forgejo is canonical SSOT. Typed positive refuse for Compose entity
-- when origin is 'origin.cursor.com' or GitHub-as-origin — not silent accept.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.OriginRefuse
  ( -- * Entity labels + origin host classification (§16.8)
    OriginEntityLabel (..)
  , OriginHostClass (..)
  , originHostTag
  , originHostTagOriginCursorNeGithub
  , originHostIsCursor
  , originHostIsGithub
  , originCursorHostPin
  , githubOriginHostPin
  , forgejoCanonicalHostPin
  , classifyOriginHost
    -- * Remote descriptor + policy carriers
  , OriginRemoteDescriptor (..)
  , OriginUcrsStamp (..)
  , OriginPolicyWitness (..)
  , OriginRefuseMorphism (..)
    -- * §16.8 policy verdict + positive refuse
  , OriginRefusal (..)
  , OriginPolicyVerdict (..)
  , composeUpstreamRefused
  , OriginAdmissibilityConjunct (..)
  , originConjunctAdmits
  , evaluateOriginPolicy
  , admitOriginRemote
  , refuseOriginCursorForCompose
  , refuseGithubAsOriginForCompose
  , refuseDualPushCompose
  , witnessFromRemote
  , applyOriginRefuseMorphism
  , refuseOriginCursorForComposePositive
  , refuseGithubAsOriginForComposePositive
  , refuseDualPushComposePositive
    -- * Excitement alignment (no second argmin)
  , OriginExcitementComposePin (..)
  , OriginRefuseCtx (..)
  , composeExcitementSelect
  , originRefuseSelect
  , originRefuseSelectBare
  , composeExcitementSelectEqExcitementSelect
  , originRefuseSelectEqExcitementSelect
  , originRefuseSelectBareEqExcitementSelect
  , originRefuseSelectEqOriginRefuseSelectBare
  , originRefuseNoLocalArgmin
  , composeExcitementSelectRefusesSecondArgmin
  , originRefuseEmpty
    -- * Landauer bridge (derived — zero new axioms)
  , OriginHistoryMove (..)
  , admissibleOriginRefuse
  , OriginTransition (..)
  , originSecondLaw
  , PhysicalOriginBridge (..)
  , originSecondLawFromPhysical
  , admissibleOriginRefuseFromPhysical
  , physicalSecondLawImported
    -- * §16.8 fixtures + witness theorems
  , originFixtureUcrs
  , originFixtureConjunct
  , composeOriginCursorFixture
  , composeGithubOriginFixture
  , composeForgejoCanonicalFixture
  , originFixtureCursorComposeRefused
  , originFixtureGithubComposeRefused
  , originFixtureForgejoComposeAdmitted
  , originFixtureComposeUpstreamRefusedGithub
  , originFixtureComposeUpstreamRefusedCursor
  , originFixtureApplyMorphismForgejoOk
  , originFixtureClassifyCursor
  , originFixtureClassifyGithub
  , originFixtureClassifyForgejo
  , originFixtureConjunctAdmits
    -- * Honesty flags + catalog witnesses
  , originRefusePhysicsGreen
  , originRefusePhysicsGreenFalse
  , originRefuseProductionWired
  , originRefuseProductionWiredFalse
  , originRefuseModuleWitness
  , originRefuseNoNewAxiom
  , originRefusePositiveRefuseNotSilent
  , originRefuseNoSecondArgmin
  , originRefuseNonClaim
  , originRefuseNonClaimNonempty
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

-- ---------------------------------------------------------------------------
-- SECTION 1: Entity labels + origin host classification (§16.8)
-- ---------------------------------------------------------------------------

-- | Urge entity label for §16.8 origin policy row.
data OriginEntityLabel
  = OriginCompose
  | OriginLabsPublicOss
  deriving (Show, Eq)

-- | Classified origin host for policy evaluation.
data OriginHostClass
  = OriginCursor
  | OriginGithub
  | OriginForgejoCanonical
  | OriginUnclassified
  deriving (Show, Eq)

-- | Stable host-class tag string (not XOR — distinct tags).
originHostTag :: OriginHostClass -> String
originHostTag OriginCursor          = "origin-cursor"
originHostTag OriginGithub          = "github"
originHostTag OriginForgejoCanonical = "forgejo-canonical"
originHostTag OriginUnclassified    = "unclassified"

-- | Host tags are distinct — origin-cursor ≠ github.
originHostTagOriginCursorNeGithub :: Bool
originHostTagOriginCursorNeGithub =
  originHostTag OriginCursor /= originHostTag OriginGithub

-- | Whether host class is 'origin.cursor.com'.
originHostIsCursor :: OriginHostClass -> Bool
originHostIsCursor OriginCursor = True
originHostIsCursor _            = False

-- | Whether host class is GitHub-as-origin.
originHostIsGithub :: OriginHostClass -> Bool
originHostIsGithub OriginGithub = True
originHostIsGithub _              = False

-- | Canonical host pins from §16.8.
originCursorHostPin :: String
originCursorHostPin = "origin.cursor.com"

githubOriginHostPin :: String
githubOriginHostPin = "github.com"

forgejoCanonicalHostPin :: String
forgejoCanonicalHostPin = "forgejo.tailnet"

-- | Classify origin host string into policy row host.
classifyOriginHost :: String -> OriginHostClass
classifyOriginHost host
  | host == originCursorHostPin     = OriginCursor
  | host == githubOriginHostPin     = OriginGithub
  | host == forgejoCanonicalHostPin = OriginForgejoCanonical
  | otherwise                       = OriginUnclassified

-- | Remote origin descriptor — entity label + host string.
data OriginRemoteDescriptor = OriginRemoteDescriptor
  { originRemoteEntity :: !OriginEntityLabel
  , originRemoteHost   :: !String
  } deriving (Show, Eq)

-- | UCRS stamp surrogate carried through origin policy checks.
data OriginUcrsStamp = OriginUcrsStamp
  { originUcrsSeq      :: !Int
  , originUcrsWallHasT :: !Bool
  } deriving (Show, Eq)

-- | Witness bundle origin admission must preserve (§16.8).
data OriginPolicyWitness = OriginPolicyWitness
  { originWitnessUcrs              :: !OriginUcrsStamp
  , originWitnessForgejoCanonical  :: !Bool
  } deriving (Show, Eq)

-- | Typed origin policy morphism — admissible admission, not silent accept.
data OriginRefuseMorphism = OriginRefuseMorphism
  { originMorphismRemote              :: !OriginRemoteDescriptor
  , originMorphismWitness               :: !OriginPolicyWitness
  , originMorphismExcitementSelected    :: !Bool
  } deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §16.8 policy verdict + positive refuse
-- ---------------------------------------------------------------------------

-- | Typed refusal when origin policy rejects entity × host.
data OriginRefusal
  = OriginCursorComposeRefused
  | GithubAsOriginComposeRefused
  | OriginCursorLabsRefused
  | UnclassifiedHost
  | DualPushComposeRefused
  | GateRejected !Int
  deriving (Show, Eq)

-- | Origin policy verdict for entity × host.
data OriginPolicyVerdict
  = OriginAdmitted
  | OriginRefused !OriginRefusal
  deriving (Show, Eq)

-- | Whether remote host is refused upstream for Compose (§16.8 / §13.6).
composeUpstreamRefused :: String -> Bool
composeUpstreamRefused host =
  host == githubOriginHostPin || host == originCursorHostPin

-- | §16.8 admissibility conjunct inputs (surrogate).
data OriginAdmissibilityConjunct = OriginAdmissibilityConjunct
  { originConjGateOk              :: !Bool
  , originConjForgejoCanonical    :: !Bool
  , originConjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate @admit(h) ⟺ gate ∧ Forgejo canonical ∧ Excitement preserves@.
originConjunctAdmits :: OriginAdmissibilityConjunct -> Bool
originConjunctAdmits c =
  originConjGateOk c
  && originConjForgejoCanonical c
  && originConjExcitementPreserves c

-- | Evaluate §16.8 origin policy for entity × classified host.
evaluateOriginPolicy
  :: OriginEntityLabel -> OriginHostClass -> OriginPolicyVerdict
evaluateOriginPolicy OriginCompose OriginCursor =
  OriginRefused OriginCursorComposeRefused
evaluateOriginPolicy OriginCompose OriginGithub =
  OriginRefused GithubAsOriginComposeRefused
evaluateOriginPolicy OriginLabsPublicOss OriginCursor =
  OriginRefused OriginCursorLabsRefused
evaluateOriginPolicy OriginLabsPublicOss OriginGithub = OriginAdmitted
evaluateOriginPolicy _ OriginForgejoCanonical = OriginAdmitted
evaluateOriginPolicy _ OriginUnclassified = OriginRefused UnclassifiedHost

-- | Admit origin remote — 'OriginRefused' when §16.8 policy refuses entity × host.
admitOriginRemote :: OriginRemoteDescriptor -> OriginPolicyVerdict
admitOriginRemote remote =
  evaluateOriginPolicy
    (originRemoteEntity remote)
    (classifyOriginHost (originRemoteHost remote))

-- | Positive refuse: 'origin.cursor.com' for Compose entity.
refuseOriginCursorForCompose :: OriginRefusal
refuseOriginCursorForCompose = OriginCursorComposeRefused

-- | Positive refuse: 'github.com' as origin for Compose entity.
refuseGithubAsOriginForCompose :: OriginRefusal
refuseGithubAsOriginForCompose = GithubAsOriginComposeRefused

-- | Positive refuse: dual-push / @origin repo create@ on Compose trees.
refuseDualPushCompose :: OriginRefusal
refuseDualPushCompose = DualPushComposeRefused

-- | Build witness from remote descriptor.
witnessFromRemote
  :: OriginRemoteDescriptor -> OriginUcrsStamp -> OriginPolicyWitness
witnessFromRemote remote stamp =
  OriginPolicyWitness
    { originWitnessUcrs = stamp
    , originWitnessForgejoCanonical =
        case classifyOriginHost (originRemoteHost remote) of
          OriginForgejoCanonical -> True
          _                      -> False
    }

-- | Attempt typed origin morphism — fail closed on inadmissibility.
applyOriginRefuseMorphism
  :: OriginRemoteDescriptor
  -> OriginAdmissibilityConjunct
  -> OriginUcrsStamp
  -> Bool
  -> (Maybe OriginRefuseMorphism, Maybe OriginRefusal)
applyOriginRefuseMorphism remote conjunct stamp excitementSelected
  | not (originConjunctAdmits conjunct) =
      (Nothing, Just (GateRejected (originUcrsSeq stamp)))
  | otherwise =
      case admitOriginRemote remote of
        OriginAdmitted ->
          if not excitementSelected
            then (Nothing, Just UnclassifiedHost)
            else
              ( Just
                  OriginRefuseMorphism
                    { originMorphismRemote = remote
                    , originMorphismWitness = witnessFromRemote remote stamp
                    , originMorphismExcitementSelected = excitementSelected
                    }
              , Nothing
              )
        OriginRefused r -> (Nothing, Just r)

-- | Positive refuse witness: origin-cursor for Compose.
refuseOriginCursorForComposePositive :: Bool
refuseOriginCursorForComposePositive =
  refuseOriginCursorForCompose == OriginCursorComposeRefused

-- | Positive refuse witness: GitHub-as-origin for Compose.
refuseGithubAsOriginForComposePositive :: Bool
refuseGithubAsOriginForComposePositive =
  refuseGithubAsOriginForCompose == GithubAsOriginComposeRefused

-- | Positive refuse witness: dual-push Compose refused.
refuseDualPushComposePositive :: Bool
refuseDualPushComposePositive =
  refuseDualPushCompose == DualPushComposeRefused

-- ---------------------------------------------------------------------------
-- SECTION 3: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement compose pin — Urge imports selector; no second argmin.
data OriginExcitementComposePin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

-- | Context for origin refuse over admissible history successors.
data OriginRefuseCtx = OriginRefuseCtx
  { originRefusePrior      :: !ThermodynamicState
  , originRefuseSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Origin path composes 'excitementSelect' — not a second argmin.
composeExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> OriginExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
composeExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
composeExcitementSelect _ _ SecondArgminRefused =
  Left ExcAllInadmissible

-- | Origin refuse selection composes imported excitement — no local argmin.
originRefuseSelect
  :: OriginRefuseCtx -> Either ExcitementResidue HistoryCandidate
originRefuseSelect ctx =
  excitementSelect (originRefusePrior ctx) (originRefuseSuccessors ctx)

-- | Bare origin refuse selection on @(prior, successors)@.
originRefuseSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
originRefuseSelectBare = excitementSelect

-- | Definitional witness: import pin is 'excitementSelect'.
composeExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
composeExcitementSelectEqExcitementSelect src cands =
  composeExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | Definitional witness: origin refuse selection API is 'excitementSelect'.
originRefuseSelectEqExcitementSelect :: OriginRefuseCtx -> Bool
originRefuseSelectEqExcitementSelect ctx =
  originRefuseSelect ctx
    == excitementSelect (originRefusePrior ctx) (originRefuseSuccessors ctx)

-- | Definitional witness: bare selection API is 'excitementSelect'.
originRefuseSelectBareEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
originRefuseSelectBareEqExcitementSelect prior successors =
  originRefuseSelectBare prior successors == excitementSelect prior successors

-- | Context and bare selectors agree.
originRefuseSelectEqOriginRefuseSelectBare :: OriginRefuseCtx -> Bool
originRefuseSelectEqOriginRefuseSelectBare ctx =
  originRefuseSelect ctx
    == originRefuseSelectBare (originRefusePrior ctx) (originRefuseSuccessors ctx)

-- | Origin selector re-uses 'excitementSelect' — no Urge-local argmin.
originRefuseNoLocalArgmin :: OriginRefuseCtx -> Bool
originRefuseNoLocalArgmin ctx =
  originRefuseSelect ctx
    == excitementSelect (originRefusePrior ctx) (originRefuseSuccessors ctx)

-- | Second-argmin pin refuses with all-inadmissible residue.
composeExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
composeExcitementSelectRefusesSecondArgmin src cands =
  composeExcitementSelect src cands SecondArgminRefused
    == Left ExcAllInadmissible

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
originRefuseEmpty :: ThermodynamicState -> Bool
originRefuseEmpty prior =
  originRefuseSelectBare prior [] == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Origin history move admissibility conjunct (gate + Forgejo + provenance).
data OriginHistoryMove = OriginHistoryMove
  { originMoveGateChecked      :: !Bool
  , originMoveForgejoCanonical :: !Bool
  , originMoveProvenanceOk     :: !Bool
  } deriving (Show, Eq)

-- | Admissible origin refuse when gate, Forgejo canonical, and provenance hold.
admissibleOriginRefuse :: OriginHistoryMove -> Bool
admissibleOriginRefuse h =
  originMoveGateChecked h
  && originMoveForgejoCanonical h
  && originMoveProvenanceOk h

-- | Thermodynamic accounting on an origin transition (acting meso layer).
data OriginTransition = OriginTransition
  { originTransitionMove           :: !OriginHistoryMove
  , originTransitionBath           :: !HeatBath
  , originTransitionDissipatedWork :: !Double
  , originTransitionEntropyDrop    :: !Double
  } deriving (Show, Eq)

-- | Named second-law invariant on origin transition (Bool witness).
originSecondLaw :: OriginTransition -> Bool
originSecondLaw t =
  originTransitionEntropyDrop t
    <= originTransitionDissipatedWork t / bathTemp (originTransitionBath t)

-- | Physical bridge tying Landauer process to origin refuse admissibility.
data PhysicalOriginBridge = PhysicalOriginBridge
  { physicalOriginLandauerBridge :: !LandauerHistoryBridge
  , physicalOriginTransition     :: !OriginTransition
  , physicalOriginAdmissible     :: !Bool
  } deriving (Show, Eq)

-- | Second law on origin transition from Landauer bridge discharge.
originSecondLawFromPhysical :: PhysicalOriginBridge -> Bool -> Bool
originSecondLawFromPhysical b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge
       (physicalOriginLandauerBridge b)
       hSL
  && admitSecondLaw (landauerTransition (physicalOriginLandauerBridge b))
  && originSecondLaw (physicalOriginTransition b)

-- | Admissible origin refuse from physical bridge (no new axiom).
admissibleOriginRefuseFromPhysical :: PhysicalOriginBridge -> Bool -> Bool
admissibleOriginRefuseFromPhysical b hSL =
  hSL
  && physicalOriginAdmissible b
  && admissibleOriginRefuse (originTransitionMove (physicalOriginTransition b))

-- | Physical second law imported from Lean @LandauerLaw.physicalSecondLaw@.
physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 5: §16.8 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | §16.8 fixture UCRS stamp.
originFixtureUcrs :: OriginUcrsStamp
originFixtureUcrs = OriginUcrsStamp {originUcrsSeq = 8, originUcrsWallHasT = True}

-- | §16.8 fixture admissibility conjunct (all gates pass).
originFixtureConjunct :: OriginAdmissibilityConjunct
originFixtureConjunct =
  OriginAdmissibilityConjunct
    { originConjGateOk = True
    , originConjForgejoCanonical = True
    , originConjExcitementPreserves = True
    }

-- | Compose entity + origin.cursor.com fixture (refused).
composeOriginCursorFixture :: OriginRemoteDescriptor
composeOriginCursorFixture =
  OriginRemoteDescriptor
    { originRemoteEntity = OriginCompose
    , originRemoteHost = originCursorHostPin
    }

-- | Compose entity + github.com-as-origin fixture (refused).
composeGithubOriginFixture :: OriginRemoteDescriptor
composeGithubOriginFixture =
  OriginRemoteDescriptor
    { originRemoteEntity = OriginCompose
    , originRemoteHost = githubOriginHostPin
    }

-- | Compose entity + Forgejo canonical fixture (admitted).
composeForgejoCanonicalFixture :: OriginRemoteDescriptor
composeForgejoCanonicalFixture =
  OriginRemoteDescriptor
    { originRemoteEntity = OriginCompose
    , originRemoteHost = forgejoCanonicalHostPin
    }

-- | origin.cursor.com for Compose is positively refused.
originFixtureCursorComposeRefused :: Bool
originFixtureCursorComposeRefused =
  admitOriginRemote composeOriginCursorFixture
    == OriginRefused OriginCursorComposeRefused

-- | github.com-as-origin for Compose is positively refused.
originFixtureGithubComposeRefused :: Bool
originFixtureGithubComposeRefused =
  admitOriginRemote composeGithubOriginFixture
    == OriginRefused GithubAsOriginComposeRefused

-- | Forgejo canonical for Compose is admitted.
originFixtureForgejoComposeAdmitted :: Bool
originFixtureForgejoComposeAdmitted =
  admitOriginRemote composeForgejoCanonicalFixture == OriginAdmitted

-- | Compose upstream refused for github.com.
originFixtureComposeUpstreamRefusedGithub :: Bool
originFixtureComposeUpstreamRefusedGithub =
  composeUpstreamRefused githubOriginHostPin

-- | Compose upstream refused for origin.cursor.com.
originFixtureComposeUpstreamRefusedCursor :: Bool
originFixtureComposeUpstreamRefusedCursor =
  composeUpstreamRefused originCursorHostPin

-- | Forgejo morphism applies successfully under fixture conjunct.
originFixtureApplyMorphismForgejoOk :: Bool
originFixtureApplyMorphismForgejoOk =
  applyOriginRefuseMorphism
    composeForgejoCanonicalFixture
    originFixtureConjunct
    originFixtureUcrs
    True
    == ( Just
           OriginRefuseMorphism
             { originMorphismRemote = composeForgejoCanonicalFixture
             , originMorphismWitness =
                 witnessFromRemote composeForgejoCanonicalFixture originFixtureUcrs
             , originMorphismExcitementSelected = True
             }
       , Nothing
       )

-- | Classify origin.cursor.com host pin.
originFixtureClassifyCursor :: Bool
originFixtureClassifyCursor =
  classifyOriginHost originCursorHostPin == OriginCursor

-- | Classify github.com host pin.
originFixtureClassifyGithub :: Bool
originFixtureClassifyGithub =
  classifyOriginHost githubOriginHostPin == OriginGithub

-- | Classify forgejo.tailnet host pin.
originFixtureClassifyForgejo :: Bool
originFixtureClassifyForgejo =
  classifyOriginHost forgejoCanonicalHostPin == OriginForgejoCanonical

-- | Fixture conjunct admits.
originFixtureConjunctAdmits :: Bool
originFixtureConjunctAdmits = originConjunctAdmits originFixtureConjunct

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
originRefusePhysicsGreen :: Bool
originRefusePhysicsGreen = False

-- | Lean/Coq: @origin_refuse_physics_green_false@.
originRefusePhysicsGreenFalse :: Bool
originRefusePhysicsGreenFalse = not originRefusePhysicsGreen

-- | Production wiring stays open (meso lift only).
originRefuseProductionWired :: Bool
originRefuseProductionWired = False

-- | Lean/Coq: @origin_refuse_production_wired_false@.
originRefuseProductionWiredFalse :: Bool
originRefuseProductionWiredFalse = not originRefuseProductionWired

-- | Catalog witness: meso Urge OriginRefuse module present.
originRefuseModuleWitness :: Bool
originRefuseModuleWitness = True

-- | Zero new axiom discipline witness.
originRefuseNoNewAxiom :: Bool
originRefuseNoNewAxiom = True

-- | Positive refuse is not silent accept on Compose origin fixtures.
originRefusePositiveRefuseNotSilent :: Bool
originRefusePositiveRefuseNotSilent =
  admitOriginRemote composeOriginCursorFixture /= OriginAdmitted
  && admitOriginRemote composeGithubOriginFixture /= OriginAdmitted

-- | Second-argmin refusal: origin composes 'excitementSelect' only.
originRefuseNoSecondArgmin :: Bool
originRefuseNoSecondArgmin =
  originRefuseNoLocalArgmin
    OriginRefuseCtx
      { originRefusePrior = ThermodynamicState 300 0 0.3 30 40
      , originRefuseSuccessors = []
      }

-- | Honest non-claim string (meso §16.8 origin refuse scaffold).
originRefuseNonClaim :: String
originRefuseNonClaim =
  "§16.8 origin.cursor.com / GitHub-as-origin refuse for Compose; "
    ++ "Forgejo canonical SSOT; compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
originRefuseNonClaimNonempty :: Bool
originRefuseNonClaimNonempty = length originRefuseNonClaim > 0
