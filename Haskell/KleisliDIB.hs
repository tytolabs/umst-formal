-- |
-- Module      : KleisliDIB
-- Description : Categorical semantics for the Discover–Invent–Build cycle
-- License     : MIT
--
-- = Why a Kleisli Monad?
--
-- The Discover–Invent–Build (DIB) cycle is the epistemological engine
-- of material-design practice.  Each phase has three properties that
-- make a plain function @a -> b@ inadequate:
--
--   1. __Partiality__: discovery can fail (a sample may be inconclusive),
--      invention can fail (no admissible gate specification may exist),
--      and building can fail (the gate may reject the transition).
--
--   2. __Side effects__: each phase performs I/O — reading sensors,
--      writing logs, invoking the Rust FFI for gate evaluation.
--
--   3. __State accumulation__: the thermodynamic state evolves across
--      the cycle; each phase reads and updates it.
--
-- A Kleisli arrow @a -> m b@ over the monad @m = StateT UMSTState IO@
-- captures all three concerns in a single compositional abstraction.
-- Kleisli composition @(>=>)@ is exactly sequential pipeline:
--
-- @
--   dibCycle = discover >=> invent >=> build
-- @
--
-- = Monoidal Structure and Mass Conservation
--
-- The category of material states carries a monoidal structure under
-- /mixture/.  When two material batches are combined, their masses add
-- (tensor product), and the gate enforces that total mass is conserved
-- (unit coherence).  In code, this appears as the @massConserved@ field
-- of 'AdmissibilityResult': a monoidal constraint on state composition.
--
-- = Connection to Linear Logic
--
-- The gate has a linear character: a kilogram of cement, once consumed
-- by hydration, cannot be "un-hydrated" and reused.  Resources are
-- consumed, not duplicated.  In linear-logic terms, the gate enforces
-- that the transition arrow is /linear/ — it maps each unit of
-- reactant to exactly one unit of product.  The hydration-irreversibility
-- invariant (\(\alpha_{new} \geq \alpha_{old}\)) is the categorical
-- shadow of this linear constraint.
--
-- = Empirical Basis
--
-- Each DIB phase has a concrete referent:
--
--   * __Discover__: systematic field measurement of material behaviour
--     (carbonation depth, workability at successive intervals, moisture
--     content profiles).  Outputs are @Observation@ values — structured
--     records of what was measured and when.
--
--   * __Invent__: inductive generalisation from observations to invariant
--     candidates.  The four gate conditions (mass conservation,
--     Clausius-Duhem, hydration irreversibility, strength monotonicity)
--     were each identified by observing that specific failure modes
--     violated them and that no undamaged specimen ever did.
--
--   * __Build__: implementation of the formalised gate in the Rust kernel
--     (umst-prototype-2a) and validation against new batches.

module KleisliDIB
  ( -- * State and monad type
    UMSTState (..)
  , LogEntry (..)
  , Phase (..)
  , DIB
    -- * DIB data types
  , Observation (..)
  , Insight (..)
  , Design (..)
  , Artifact (..)
    -- * DIB phases (Kleisli arrows)
  , discover
  , invent
  , build
    -- * Full cycle (Kleisli composition)
  , dibCycle
  ) where

import Control.Monad.State  (StateT, get, modify', runStateT)

import UMST

------------------------------------------------------------------------
-- State
------------------------------------------------------------------------

-- | The mutable context threaded through the DIB cycle.
--
-- [@currentState@] The material's current thermodynamic snapshot.
-- [@stateLog@]     An append-only audit trail.  Every gate evaluation —
--                  pass or fail — is recorded here so that the full
--                  material history is reconstructable for certification.
data UMSTState = UMSTState
  { currentState :: !ThermodynamicState
  , stateLog     :: ![LogEntry]
  } deriving (Show)

-- | A single entry in the audit trail.
--
-- Records the phase that produced it, the time, and a human-readable
-- message.  In production this would be a structured event; here we
-- keep it simple for clarity.
data LogEntry = LogEntry
  { logPhase   :: !Phase
  , logMessage :: !String
  } deriving (Show)

-- | The three phases of the DIB cycle, used for log tagging.
data Phase
  = Discover
  | Invent
  | Build
  deriving (Show, Eq, Ord, Enum, Bounded)

------------------------------------------------------------------------
-- DIB Monad
------------------------------------------------------------------------

-- | The DIB monad: a Kleisli category over @StateT UMSTState IO@.
--
-- Every arrow @a -> DIB b@ is a Kleisli arrow that can:
--
--   * Read and update the current 'ThermodynamicState'.
--   * Append to the audit log.
--   * Perform I/O (sensor reads, FFI calls, file writes).
--   * Fail via 'IO' exceptions when a phase is irrecoverable.
type DIB a = StateT UMSTState IO a

------------------------------------------------------------------------
-- Phase Data Types
------------------------------------------------------------------------

-- | Raw field observation: measured properties of a material sample.
--
-- In practice this comes from a lab test (slump, air content,
-- temperature) or a field measurement (core density, rebound number).
data Observation = Observation
  { obsMaterialType :: !MaterialType
    -- ^ What kind of material was observed
  , obsDensity      :: !Double
    -- ^ Measured bulk density (kg/m³)
  , obsHydration    :: !Double
    -- ^ Measured or estimated degree of hydration
  , obsStrength     :: !Double
    -- ^ Measured compressive strength (MPa), 0 if not tested
  , obsTemperature  :: !Double
    -- ^ Ambient or sample temperature (°C)
  , obsNotes        :: !String
    -- ^ Free-text field notes (the tacit-knowledge capture point)
  } deriving (Show, Eq)

-- | An insight distilled from observation: which invariants must hold
-- and what parameter ranges are physically plausible.
--
-- This is where tacit knowledge becomes explicit.  A practitioner who
-- has watched hundreds of cubes fail knows that a lime–pozzolan mix at
-- w/c > 0.7 will never reach 15 MPa — that knowledge is encoded here
-- as bounds on the gate parameters.
data Insight = Insight
  { insightState       :: !ThermodynamicState
    -- ^ Reconstructed thermodynamic state from the observation
  , insightMaxDensity  :: !Double
    -- ^ Upper bound on plausible density for this material
  , insightMinStrength :: !Double
    -- ^ Lower bound on expected strength at this hydration degree
  , insightRationale   :: !String
    -- ^ Human-readable explanation of why these bounds were chosen
  } deriving (Show, Eq)

-- | A design specification: the gate parameters and proposed next state
-- that the Build phase will attempt to commit.
--
-- The transition from 'Insight' to 'Design' is the formalisation step:
-- fuzzy practitioner intuition ("this mix feels too wet") becomes a
-- precise gate specification ("density must not drop below 2100 kg/m³").
data Design = Design
  { designProposedState :: !ThermodynamicState
    -- ^ The state we want to transition to
  , designTimeStep      :: !Double
    -- ^ Δt for the gate evaluation (seconds)
  , designSpecification :: !String
    -- ^ Formal specification summary
  } deriving (Show, Eq)

-- | A verified artefact: the result of applying the gate to a proposed
-- transition and committing the new state if admissible.
--
-- If the gate rejects the transition, the artefact records the failure
-- diagnostics so the cycle can iterate.
data Artifact = Artifact
  { artifactResult   :: !AdmissibilityResult
    -- ^ Full gate-check diagnostics
  , artifactNewState :: !ThermodynamicState
    -- ^ The state after the transition (unchanged if rejected)
  , artifactVerified :: !Bool
    -- ^ True iff the transition was accepted and committed
  } deriving (Show, Eq)

------------------------------------------------------------------------
-- Kleisli Arrows
------------------------------------------------------------------------

-- | __Phase 1: Discover__ — observe a material and reconstruct its
-- thermodynamic state.
--
-- This arrow consumes a raw 'Observation' and produces an 'Insight'
-- by mapping measured properties to the Powers–Clausius-Duhem model.
-- The practitioner's tacit knowledge enters through @obsNotes@ and
-- influences the plausibility bounds.
--
-- In category-theoretic terms: a morphism from the observation
-- presheaf to the insight presheaf, natural in the material type.
discover :: Observation -> DIB Insight
discover obs = do
  let st = fromMix
             (obsDensity obs / 1500.0)
             (obsHydration obs)
             (obsTemperature obs)
  appendLog Discover $
    "Observed " ++ show (obsMaterialType obs)
    ++ " at ρ=" ++ show (obsDensity obs)
    ++ ", α=" ++ show (obsHydration obs)
  pure Insight
    { insightState       = st
    , insightMaxDensity  = obsDensity obs * 1.05
    , insightMinStrength = obsStrength obs * 0.9
    , insightRationale   = obsNotes obs
    }

-- | __Phase 2: Invent__ — formalise an insight into a gate-ready design.
--
-- Given the invariant bounds from 'Insight', this arrow constructs
-- a proposed next state and a time step.  The design encodes the
-- practitioner's intent: "advance hydration by Δα while keeping
-- density within the conservation envelope."
--
-- The output 'Design' is a /specification/, not yet verified.  It is
-- the Invent phase's job to produce specifications that are /likely/
-- admissible, but the gate has the final say.
invent :: Insight -> DIB Design
invent insight = do
  st <- currentState <$> get
  let proposed = insightState insight
      dt       = 3600.0
  appendLog Invent $
    "Proposed transition: α "
    ++ show (hydration st)
    ++ " → " ++ show (hydration proposed)
    ++ ", Δt=" ++ show dt ++ "s"
  pure Design
    { designProposedState = proposed
    , designTimeStep      = dt
    , designSpecification = insightRationale insight
    }

-- | __Phase 3: Build__ — apply the gate and commit or reject.
--
-- This is the moment of truth.  The arrow evaluates the pure gate
-- check (and, in production, the Rust FFI gate for cross-validation)
-- on the proposed transition.  If all four invariants hold, the new
-- state is committed and becomes the current state for the next cycle.
--
-- If the gate rejects, the state is /not/ updated — the system
-- remains in its previous safe configuration.  This is the linear-logic
-- guarantee: resources are only consumed when the transition is proven
-- admissible.
build :: Design -> DIB Artifact
build design = do
  st <- currentState <$> get
  let proposed = designProposedState design
      dt       = designTimeStep design
      result   = gateCheck st proposed dt
      verified = accepted result
  if verified
    then do
      modify' $ \s -> s { currentState = proposed }
      appendLog Build $
        "ACCEPTED: D_int=" ++ show (dissipation result)
        ++ ", state committed"
    else
      appendLog Build $
        "REJECTED: mass=" ++ show (massConserved result)
        ++ ", energy=" ++ show (energyPositive result)
  pure Artifact
    { artifactResult   = result
    , artifactNewState = if verified then proposed else st
    , artifactVerified = verified
    }

------------------------------------------------------------------------
-- Kleisli Composition
------------------------------------------------------------------------

-- | The full DIB cycle as a single Kleisli arrow.
--
-- @
--   dibCycle = discover >=> invent >=> build
-- @
--
-- This is /sequential/ composition in the Kleisli category:
-- each phase feeds its output into the next, threading the
-- 'UMSTState' through all three and accumulating the log.
dibCycle :: Observation -> DIB Artifact
dibCycle obs = discover obs >>= invent >>= build

------------------------------------------------------------------------
-- Runner
------------------------------------------------------------------------

-- | Execute a 'DIB' computation from an initial state, returning
-- both the final value and the final state (including the full log).
runDIB :: UMSTState -> DIB a -> IO (a, UMSTState)
runDIB = flip runStateT

-- | Construct an initial 'UMSTState' from mix-design parameters.
initialState :: Double -> Double -> Double -> UMSTState
initialState wc alpha temp = UMSTState
  { currentState = fromMix wc alpha temp
  , stateLog     = []
  }

------------------------------------------------------------------------
-- Internal Helpers
------------------------------------------------------------------------

-- | Append a timestamped entry to the audit log.
appendLog :: Phase -> String -> DIB ()
appendLog phase msg =
  modify' $ \s ->
    s { stateLog = stateLog s ++ [LogEntry phase msg] }
