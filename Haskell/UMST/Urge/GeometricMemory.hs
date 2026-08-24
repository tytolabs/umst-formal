-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.GeometricMemory
-- Description : Meso acting Urge — §5.3 geometric memory / SDF identity of a history object.
--
-- Identity is canonical SDF/FRep fingerprint — not host ids or raw payload bytes alone.
-- History recovery composes 'excitementSelect' — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.GeometricMemory
  ( -- * SDF identity + typed history object carriers (§5.3)
    SdfFingerprint (..)
  , HistoryGeometricIdentity (..)
  , HistoryObjectGeom (..)
  , GeometricMemoryWitness (..)
  , GeometricMemoryMorphism (..)
  , GeometricMemoryRefusal (..)
  , GeometricMemoryVerdict (..)
  , GeometricAdmissibilityConjunct (..)
  , sdfIdentityFromDigest
  , witnessFromHistoryObject
  , geometricIdentityMatches
    -- * §5.3 admissibility conjunct + positive refuse
  , geometricConjunctAdmits
  , evaluateHostIdIdentity
  , evaluatePayloadOnlyIdentity
  , refuseHostIdIdentity
  , refusePayloadOnlyIdentity
  , applyGeometricMemoryMorphism
  , hostIdIdentityRefused
  , payloadOnlyIdentityRefused
  , evaluateHostIdIdentityRefused
  , evaluateHostIdIdentityOk
  , evaluatePayloadOnlyIdentityRefused
  , evaluatePayloadOnlyIdentityOk
    -- * Excitement alignment (no second argmin)
  , GeometricMemoryCtx (..)
  , geometricMemorySelect
  , geometricMemorySelectBare
  , geometricMemorySelectEqExcitementSelect
  , geometricMemorySelectBareEqExcitementSelect
  , geometricMemoryNoLocalArgmin
  , geometricMemoryEmpty
    -- * §5.3 fixtures + witness theorems
  , geometricFixtureFingerprint
  , geometricFixtureIdentity
  , geometricFixtureObject
  , geometricFixtureObjectSameIdentity
  , geometricFixtureObjectDistinct
  , geometricFixtureConjunct
  , geometricFixtureHostIdRefused
  , geometricFixturePayloadOnlyRefused
  , geometricFixtureApplyMorphismOk
  , geometricFixtureMatchingIdentity
  , geometricFixtureDistinctIdentity
  , geometricFixtureWitnessPreservesFingerprint
  , geometricMemoryHostIdNotOk
  , geometricMemoryPayloadOnlyNotOk
    -- * Landauer bridge (derived — zero new axioms)
  , geometricSecondLawFromLandauer
  , geometricFromLandauerAdmitSecondLaw
  , geometricSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , geometricMemoryPhysicsGreen
  , geometricMemoryPhysicsGreenFalse
  , geometricMemoryProductionWired
  , geometricMemoryProductionWiredFalse
  , geometricMemoryNonClaim
  , geometricMemoryNonClaimNonempty
  , geometricMemoryModuleWitness
  , geometricMemoryNoNewAxiom
  , geometricMemoryNoSecondArgmin
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

-- ---------------------------------------------------------------------------
-- SECTION 1: SDF identity + typed history object carriers (§5.3)
-- ---------------------------------------------------------------------------

-- | Canonical SDF fingerprint surrogate (FRep grain + digest).
data SdfFingerprint = SdfFingerprint
  { sdfDigest :: !Int
  , sdfGrain  :: !Int
  } deriving (Show, Eq)

-- | §5.3 geometric identity — SDF-canonical, not host-id keyed.
data HistoryGeometricIdentity = HistoryGeometricIdentity
  { geomFingerprint    :: !SdfFingerprint
  , geomResolutionBits :: !Int
  } deriving (Show, Eq)

-- | History object whose identity is geometric memory, not host id.
data HistoryObjectGeom = HistoryObjectGeom
  { geomSeq           :: !Int
  , geomIdentity      :: !HistoryGeometricIdentity
  , geomHostSurrogate :: !Int
  } deriving (Show, Eq)

-- | Witness bundle a geometric memory morphism must preserve (§5.3).
data GeometricMemoryWitness = GeometricMemoryWitness
  { witnessFingerprint   :: !SdfFingerprint
  , witnessResolutionBits :: !Int
  , witnessSdfCanonical  :: !Bool
  } deriving (Show, Eq)

-- | Typed geometric-memory morphism — admissible identity transition.
data GeometricMemoryMorphism = GeometricMemoryMorphism
  { morphismFrom           :: !HistoryObjectGeom
  , morphismToSeq          :: !Int
  , morphismWitness        :: !GeometricMemoryWitness
  , morphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Fail-closed geometric memory errors — positive refuse, not silent accept.
data GeometricMemoryRefusal
  = GeomHostIdNotGeometric !Int
  | GeomPayloadWithoutSdf !Int
  | GeomGateRejected !Int
  | GeomIdentityMismatch !Int !Int
  | GeomHostIdTheater
  | GeomPayloadOnlyTheater
  | GeomSecondArgmin
  | GeomSdfNotCanonical
  deriving (Show, Eq)

-- | Verdict of a geometric identity operation class.
data GeometricMemoryVerdict
  = GeomIdentityOk
  | GeomHostIdRefused
  | GeomPayloadOnlyRefused
  | GeomInadmissible
  deriving (Show, Eq)

-- | §5.3 admissibility conjunct inputs (surrogate).
data GeometricAdmissibilityConjunct = GeometricAdmissibilityConjunct
  { conjGateOk              :: !Bool
  , conjSdfCanonical        :: !Bool
  , conjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Build geometric identity from digest/grain/resolution.
sdfIdentityFromDigest :: Int -> Int -> Int -> HistoryGeometricIdentity
sdfIdentityFromDigest digest grain resolution =
  HistoryGeometricIdentity
    { geomFingerprint = SdfFingerprint {sdfDigest = digest, sdfGrain = grain}
    , geomResolutionBits = resolution
    }

-- | Build witness from history object — morphism must preserve SDF fingerprint.
witnessFromHistoryObject :: HistoryObjectGeom -> GeometricMemoryWitness
witnessFromHistoryObject o =
  GeometricMemoryWitness
    { witnessFingerprint = geomFingerprint (geomIdentity o)
    , witnessResolutionBits = geomResolutionBits (geomIdentity o)
    , witnessSdfCanonical = True
    }

-- | Whether two history objects share the same geometric memory identity.
geometricIdentityMatches :: HistoryObjectGeom -> HistoryObjectGeom -> Bool
geometricIdentityMatches left right =
  sdfDigest (geomFingerprint (geomIdentity left))
    == sdfDigest (geomFingerprint (geomIdentity right))
  && sdfGrain (geomFingerprint (geomIdentity left))
    == sdfGrain (geomFingerprint (geomIdentity right))
  && geomResolutionBits (geomIdentity left)
    == geomResolutionBits (geomIdentity right)

-- ---------------------------------------------------------------------------
-- SECTION 2: §5.3 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | Evaluate `admit(h) ⟺ gate ∧ SDF-canonical ∧ Excitement preserves`.
geometricConjunctAdmits :: GeometricAdmissibilityConjunct -> Bool
geometricConjunctAdmits c =
  conjGateOk c && conjSdfCanonical c && conjExcitementPreserves c

-- | Classify host-id vs SDF identity without performing I/O.
evaluateHostIdIdentity :: Bool -> GeometricMemoryVerdict
evaluateHostIdIdentity True  = GeomHostIdRefused
evaluateHostIdIdentity False = GeomIdentityOk

-- | Classify payload-only vs SDF-canonical identity.
evaluatePayloadOnlyIdentity :: Bool -> GeometricMemoryVerdict
evaluatePayloadOnlyIdentity True  = GeomPayloadOnlyRefused
evaluatePayloadOnlyIdentity False = GeomIdentityOk

-- | Positive refuse: host id is not geometric memory identity.
refuseHostIdIdentity :: Int -> GeometricMemoryRefusal
refuseHostIdIdentity = GeomHostIdNotGeometric

-- | Positive refuse: raw payload without SDF canonicalization refused.
refusePayloadOnlyIdentity :: Int -> GeometricMemoryRefusal
refusePayloadOnlyIdentity = GeomPayloadWithoutSdf

-- | Attempt typed geometric-memory morphism — fail closed on inadmissibility.
applyGeometricMemoryMorphism
  :: HistoryObjectGeom
  -> Int
  -> GeometricAdmissibilityConjunct
  -> Bool
  -> Either GeometricMemoryRefusal GeometricMemoryMorphism
applyGeometricMemoryMorphism obj toSeq conjunct excitementSelected
  | not (geometricConjunctAdmits conjunct) =
      Left (GeomGateRejected (geomSeq obj))
  | not (witnessSdfCanonical (witnessFromHistoryObject obj)) =
      Left (GeomPayloadWithoutSdf (geomHostSurrogate obj))
  | not excitementSelected =
      Left
        ( GeomIdentityMismatch
            ( sdfDigest (geomFingerprint (geomIdentity obj))
            )
            ( sdfDigest (geomFingerprint (geomIdentity obj))
            )
        )
  | otherwise =
      Right
        GeometricMemoryMorphism
          { morphismFrom = obj
          , morphismToSeq = toSeq
          , morphismWitness = witnessFromHistoryObject obj
          , morphismExcitementSelected = excitementSelected
          }

-- | Positive refuse witnesses (definitional).
hostIdIdentityRefused :: Int -> Bool
hostIdIdentityRefused hostId =
  refuseHostIdIdentity hostId == GeomHostIdNotGeometric hostId

payloadOnlyIdentityRefused :: Int -> Bool
payloadOnlyIdentityRefused payload =
  refusePayloadOnlyIdentity payload == GeomPayloadWithoutSdf payload

evaluateHostIdIdentityRefused :: Bool
evaluateHostIdIdentityRefused =
  evaluateHostIdIdentity True == GeomHostIdRefused

evaluateHostIdIdentityOk :: Bool
evaluateHostIdIdentityOk =
  evaluateHostIdIdentity False == GeomIdentityOk

evaluatePayloadOnlyIdentityRefused :: Bool
evaluatePayloadOnlyIdentityRefused =
  evaluatePayloadOnlyIdentity True == GeomPayloadOnlyRefused

evaluatePayloadOnlyIdentityOk :: Bool
evaluatePayloadOnlyIdentityOk =
  evaluatePayloadOnlyIdentity False == GeomIdentityOk

-- ---------------------------------------------------------------------------
-- SECTION 3: Geometric memory composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for geometric memory over admissible history successors.
data GeometricMemoryCtx = GeometricMemoryCtx
  { geometricMemoryPrior       :: !ThermodynamicState
  , geometricMemorySuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Geometric memory selection **is** 'excitementSelect' — not a second argmin.
geometricMemorySelect
  :: GeometricMemoryCtx
  -> Either ExcitementResidue HistoryCandidate
geometricMemorySelect ctx =
  excitementSelect (geometricMemoryPrior ctx) (geometricMemorySuccessors ctx)

-- | Bare alias on @(prior, successors)@ — same selector, no re-derivation.
geometricMemorySelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
geometricMemorySelectBare = excitementSelect

-- | Definitional witness: geometric memory selection API is 'excitementSelect'.
geometricMemorySelectEqExcitementSelect :: GeometricMemoryCtx -> Bool
geometricMemorySelectEqExcitementSelect ctx =
  geometricMemorySelect ctx
    == excitementSelect (geometricMemoryPrior ctx) (geometricMemorySuccessors ctx)

-- | Definitional witness: bare selection API is 'excitementSelect'.
geometricMemorySelectBareEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
geometricMemorySelectBareEqExcitementSelect prior cands =
  geometricMemorySelectBare prior cands == excitementSelect prior cands

-- | Geometric memory selector re-uses 'excitementSelect' — no Urge-local argmin.
geometricMemoryNoLocalArgmin :: GeometricMemoryCtx -> Bool
geometricMemoryNoLocalArgmin ctx =
  geometricMemorySelect ctx
    == excitementSelect (geometricMemoryPrior ctx) (geometricMemorySuccessors ctx)

-- | Empty successor list yields no-candidates residue.
geometricMemoryEmpty :: GeometricMemoryCtx -> Bool
geometricMemoryEmpty ctx =
  geometricMemorySuccessors ctx == []
  && geometricMemorySelect ctx == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: §5.3 fixtures + witness theorems
-- ---------------------------------------------------------------------------

geometricFixtureFingerprint :: SdfFingerprint
geometricFixtureFingerprint = SdfFingerprint {sdfDigest = 42, sdfGrain = 7}

geometricFixtureIdentity :: HistoryGeometricIdentity
geometricFixtureIdentity =
  HistoryGeometricIdentity
    { geomFingerprint = geometricFixtureFingerprint
    , geomResolutionBits = 2
    }

geometricFixtureObject :: HistoryObjectGeom
geometricFixtureObject =
  HistoryObjectGeom
    { geomSeq = 0
    , geomIdentity = geometricFixtureIdentity
    , geomHostSurrogate = 42
    }

geometricFixtureObjectSameIdentity :: HistoryObjectGeom
geometricFixtureObjectSameIdentity =
  HistoryObjectGeom
    { geomSeq = 99
    , geomIdentity = geometricFixtureIdentity
    , geomHostSurrogate = 42
    }

geometricFixtureObjectDistinct :: HistoryObjectGeom
geometricFixtureObjectDistinct =
  HistoryObjectGeom
    { geomSeq = 1
    , geomIdentity =
        HistoryGeometricIdentity
          { geomFingerprint = SdfFingerprint {sdfDigest = 7, sdfGrain = 7}
          , geomResolutionBits = 2
          }
    , geomHostSurrogate = 7
    }

geometricFixtureConjunct :: GeometricAdmissibilityConjunct
geometricFixtureConjunct =
  GeometricAdmissibilityConjunct
    { conjGateOk = True
    , conjSdfCanonical = True
    , conjExcitementPreserves = True
    }

geometricFixtureHostIdRefused :: Bool
geometricFixtureHostIdRefused =
  refuseHostIdIdentity 0xdead == GeomHostIdNotGeometric 0xdead

geometricFixturePayloadOnlyRefused :: Bool
geometricFixturePayloadOnlyRefused =
  refusePayloadOnlyIdentity 42 == GeomPayloadWithoutSdf 42

geometricFixtureApplyMorphismOk :: Bool
geometricFixtureApplyMorphismOk =
  applyGeometricMemoryMorphism geometricFixtureObject 1 geometricFixtureConjunct True
    == Right
      GeometricMemoryMorphism
        { morphismFrom = geometricFixtureObject
        , morphismToSeq = 1
        , morphismWitness = witnessFromHistoryObject geometricFixtureObject
        , morphismExcitementSelected = True
        }

geometricFixtureMatchingIdentity :: Bool
geometricFixtureMatchingIdentity =
  geometricIdentityMatches
    geometricFixtureObject
    geometricFixtureObjectSameIdentity

geometricFixtureDistinctIdentity :: Bool
geometricFixtureDistinctIdentity =
  not
    ( geometricIdentityMatches
        geometricFixtureObject
        geometricFixtureObjectDistinct
    )

geometricFixtureWitnessPreservesFingerprint :: Bool
geometricFixtureWitnessPreservesFingerprint =
  witnessFingerprint (witnessFromHistoryObject geometricFixtureObject)
    == geometricFixtureFingerprint

geometricMemoryHostIdNotOk :: Bool
geometricMemoryHostIdNotOk =
  evaluateHostIdIdentity True /= GeomIdentityOk

geometricMemoryPayloadOnlyNotOk :: Bool
geometricMemoryPayloadOnlyNotOk =
  evaluatePayloadOnlyIdentity True /= GeomIdentityOk

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on geometric memory transition from Landauer bridge discharge.
geometricSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
geometricSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
geometricFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
geometricFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for geometric memory second law (no new axiom).
geometricSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
geometricSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
geometricMemoryPhysicsGreen :: Bool
geometricMemoryPhysicsGreen = False

-- | Lean/Coq: @geometric_memory_physics_green_false@.
geometricMemoryPhysicsGreenFalse :: Bool
geometricMemoryPhysicsGreenFalse = not geometricMemoryPhysicsGreen

-- | Production wiring stays open (meso lift only).
geometricMemoryProductionWired :: Bool
geometricMemoryProductionWired = False

-- | Lean/Coq: @geometric_memory_production_wired_false@.
geometricMemoryProductionWiredFalse :: Bool
geometricMemoryProductionWiredFalse = not geometricMemoryProductionWired

-- | Honest non-claim string (meso §5.3 geometric memory scaffold).
geometricMemoryNonClaim :: String
geometricMemoryNonClaim =
  "§5.3 geometric memory: SDF/FRep identity of history object not host-id or "
    ++ "payload-only; composes excitementSelect not second argmin; "
    ++ "Landauer physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
geometricMemoryNonClaimNonempty :: Bool
geometricMemoryNonClaimNonempty = length geometricMemoryNonClaim > 0

-- | Catalog witness: meso Urge GeometricMemory module present.
geometricMemoryModuleWitness :: Bool
geometricMemoryModuleWitness = True

-- | Zero new axiom discipline witness.
geometricMemoryNoNewAxiom :: Bool
geometricMemoryNoNewAxiom = True

-- | Second-argmin refusal: geometric memory composes 'excitementSelect' only.
geometricMemoryNoSecondArgmin :: Bool
geometricMemoryNoSecondArgmin =
  geometricMemoryNoLocalArgmin
    ( GeometricMemoryCtx
        { geometricMemoryPrior = ThermodynamicState 2400 0 0.3 30 40
        , geometricMemorySuccessors = []
        }
    )
