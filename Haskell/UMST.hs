-- |
-- Module      : UMST
-- Description : Core types and pure reference implementation for the UMST thermodynamic gate
-- License     : MIT
--
-- This module defines the Haskell-side mirror of the Rust kernel's
-- thermodynamic types and gate logic.  Every type here has a 1:1
-- correspondence with a Rust struct or enum in @umst-core@, and the
-- pure gate-check function reproduces the Rust logic exactly so that
-- QuickCheck property tests can validate the FFI bridge.
--
-- The four invariants enforced by the gate are:
--
--   1. __Mass conservation__: \(|\rho_{new} - \rho_{old}| < \delta\)
--   2. __Clausius–Duhem__:   \(D_{int} = -\rho\,\dot\psi \geq 0\)
--   3. __Hydration irreversibility__: \(\alpha_{new} \geq \alpha_{old}\)
--   4. __Strength monotonicity__:     \(f_{c,new} \geq f_{c,old}\)
--
-- Each invariant was identified inductively from field observation
-- of failure modes in variable earth, lime, masonry, and recycled-
-- aggregate concrete (RAC) systems.  See Docs/Architecture-Invariants.md
-- for the derivation of each constraint.
--
-- Categorical role: 'ThermodynamicState' is an object in the category
-- of material states; the gate is a morphism predicate that selects
-- the admissible subcategory.  See "KleisliDIB" for the monad that
-- threads state through the Discover–Invent–Build cycle.

module UMST
  ( -- * Types
    ThermodynamicState (..)
  , AdmissibilityResult (..)
  , MaterialType (..)
    -- * Constants
  , qHydration
  , tolerance
  , massTolerance
  , intrinsicStrength
    -- * Gate
  , gateCheck
    -- * Constructors
  , fromMix
  ) where

------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------

-- | Latent heat of full cement hydration (J/kg).
--
-- Standard Portland cement releases approximately 450 kJ/kg when
-- fully hydrated.  This value enters the Helmholtz free-energy model
-- as \(\psi(\alpha) = -Q_{hyd} \cdot \alpha\), ensuring that the
-- Clausius–Duhem inequality is satisfied whenever hydration advances.
qHydration :: Double
qHydration = 450.0

-- | Floating-point tolerance for invariant checks.
--
-- Mirrors the Rust kernel's @TOLERANCE@ constant (1 × 10⁻⁶).
-- All inequality checks use this epsilon to absorb IEEE 754
-- rounding artefacts without weakening the physical guarantees.
tolerance :: Double
tolerance = 1e-6

-- | Maximum allowable density change per time step (kg/m³).
--
-- A generous bound (100 kg/m³) that catches gross density jumps —
-- e.g. a sign error that doubles mass — while permitting the modest
-- density shifts (~20 kg/m³) that occur during normal hydration as
-- free water is consumed and bound into C-S-H gel.
massTolerance :: Double
massTolerance = 100.0

-- | Intrinsic strength coefficient for the Powers model (MPa).
--
-- Represents the compressive strength of a fully-dense, zero-porosity
-- paste.  Typical values for Portland cement fall in the range
-- 200–280 MPa; we use 230 MPa following Powers & Brownyard (1946).
intrinsicStrength :: Double
intrinsicStrength = 230.0

------------------------------------------------------------------------
-- ThermodynamicState
------------------------------------------------------------------------

-- | A snapshot of a material's thermodynamic condition at a single
-- point in time.
--
-- Each field maps to a measurable physical quantity:
--
-- [@density@]     Bulk density \(\rho\) in kg/m³.  For normal-weight
--                 concrete this ranges from ~2200 to ~2500 kg/m³.
--
-- [@freeEnergy@]  Helmholtz free energy per unit mass \(\psi\) in J/kg.
--                 Computed as \(\psi = -Q_{hyd} \cdot \alpha\).  This
--                 is always non-positive for hydrating systems and
--                 must decrease (become more negative) over time by
--                 the Clausius–Duhem inequality.
--
-- [@hydration@]   Degree of hydration \(\alpha \in [0, 1]\).
--                 The fraction of cement that has reacted with water.
--                 Measured by loss-on-ignition, isothermal calorimetry,
--                 or bound-water content.
--
-- [@strength@]    Compressive strength \(f_c\) in MPa, computed via the
--                 Powers gel-space ratio model.
--
-- [@maxStrength@] Theoretical maximum strength at full hydration
--                 (\(\alpha = 1\)) for the current mix proportions.
--                 Acts as an upper bound: \(f_c \leq f_{c,max}\).
data ThermodynamicState = ThermodynamicState
  { density     :: !Double
  , freeEnergy  :: !Double
  , hydration   :: !Double
  , strength    :: !Double
  , maxStrength :: !Double
  } deriving (Show, Eq)

------------------------------------------------------------------------
-- AdmissibilityResult
------------------------------------------------------------------------

-- | The outcome of a gate check, reporting both the overall verdict
-- and the status of each individual invariant.
--
-- This mirrors the Rust @AdmissibilityResult@ struct.  By exposing
-- each sub-check separately, callers can diagnose /why/ a transition
-- was rejected — invaluable during mix-design iteration where a
-- formulator needs to know whether the failure is thermodynamic
-- (energy), chemical (hydration), or mechanical (strength).
data AdmissibilityResult = AdmissibilityResult
  { accepted       :: !Bool    -- ^ Overall verdict: all four invariants hold
  , dissipation    :: !Double  -- ^ Computed dissipation \(D_{int}\) (J/kg·s)
  , massConserved  :: !Bool    -- ^ Invariant 1: density change within tolerance
  , energyPositive :: !Bool    -- ^ Invariant 2: Clausius-Duhem satisfied (\(D_{int} \geq 0\))
  , hydrationOk    :: !Bool    -- ^ Invariant 3: hydration irreversibility
  , strengthOk     :: !Bool    -- ^ Invariant 4: strength monotonicity
  } deriving (Show, Eq)

------------------------------------------------------------------------
-- MaterialType
------------------------------------------------------------------------

-- | Enumeration of the 17 material constituents recognised by UMST.
--
-- Each variant corresponds to a distinct role in concrete mix design.
-- The classification follows ACI 211 and EN 206 conventions, extended
-- with modern constituents (nanomaterials, polymers, SCMs) that have
-- become routine in contemporary practice.
--
-- In categorical terms, 'MaterialType' is a finite coproduct whose
-- inhabitants index into the product of material-property functions.
data MaterialType
  = Cement          -- ^ Ordinary Portland cement (OPC) or blended cements
  | Aggregate       -- ^ Coarse and fine aggregate (natural or recycled)
  | Water           -- ^ Mixing water, including absorbed moisture
  | Admixture       -- ^ Chemical admixtures (superplasticisers, etc.)
  | Air             -- ^ Entrained or entrapped air voids
  | SCM             -- ^ Supplementary cementitious materials (fly ash, slag, silica fume)
  | Fiber           -- ^ Structural or non-structural fibres (steel, glass, polymer)
  | Nanomaterial    -- ^ Nano-silica, nano-clay, carbon nanotubes
  | Activator       -- ^ Alkaline activators for geopolymer systems
  | Lightweight     -- ^ Lightweight aggregates (expanded clay, pumice)
  | Heavyweight     -- ^ Heavyweight aggregates (barite, magnetite) for radiation shielding
  | Accelerator     -- ^ Set or hardening accelerators (calcium chloride, etc.)
  | Retarder        -- ^ Set retarders (sugar, tartaric acid, etc.)
  | AirEntrainer    -- ^ Air-entraining agents for freeze-thaw durability
  | Polymer         -- ^ Polymer modifiers (latex, epoxy, acrylic)
  | Pigment         -- ^ Inorganic pigments (iron oxide, chromium oxide)
  | Filler          -- ^ Inert fillers (limestone powder, quartz flour)
  deriving (Show, Eq, Ord, Enum, Bounded)

------------------------------------------------------------------------
-- Pure Gate Check
------------------------------------------------------------------------

-- | Pure reference implementation of the thermodynamic gate.
--
-- Given an old state, a proposed new state, and a time step \(\Delta t\),
-- this function evaluates all four invariants and returns a full
-- diagnostic result.
--
-- __Correspondence to formal layers:__
--
--   * Agda (@Gate.agda@): the @Admissible@ record type and @gate@
--     decision procedure.
--   * Rust (@thermodynamic_filter.rs@): @ThermodynamicFilter::check_transition@.
--   * This function: a pure, property-testable mirror of both.
--
-- The implementation uses the same arithmetic as the Rust kernel:
--
-- @
--   ψ̇ = (ψ_new − ψ_old) / Δt
--   D_int = −ρ_avg · ψ̇
-- @
--
-- where \(\rho_{avg}\) is the mean of old and new density.  The sign
-- of \(D_{int}\) determines Clausius–Duhem compliance.
gateCheck
  :: ThermodynamicState  -- ^ Previous (old) state
  -> ThermodynamicState  -- ^ Proposed (new) state
  -> Double              -- ^ Time step Δt (seconds, must be > 0)
  -> AdmissibilityResult
gateCheck old new dt =
  let
    -- Invariant 1: Mass conservation
    massDelta = abs (density new - density old)
    massOk    = massDelta < massTolerance + tolerance

    -- Invariant 2: Clausius-Duhem dissipation inequality
    -- Guard dt against zero to match Rust kernel (dt + 1e-10)
    psiDot = (freeEnergy new - freeEnergy old) / (dt + 1e-10)
    rhoAvg = (density old + density new) / 2.0
    diss   = negate (rhoAvg * psiDot)
    dissOk = diss >= negate tolerance

    -- Invariant 3: Hydration irreversibility
    hydOk = hydration new >= hydration old - tolerance

    -- Invariant 4: Strength monotonicity
    strOk = strength new >= strength old - tolerance

    allOk = massOk && dissOk && hydOk && strOk
  in AdmissibilityResult
    { accepted       = allOk
    , dissipation    = diss
    , massConserved  = massOk
    , energyPositive = dissOk
    , hydrationOk    = hydOk
    , strengthOk     = strOk
    }

------------------------------------------------------------------------
-- Pure fromMix
------------------------------------------------------------------------

-- | Construct a 'ThermodynamicState' from mix-design parameters.
--
-- This is the Haskell mirror of @ThermodynamicState::from_mix@ in the
-- Rust kernel.  It implements the classical Powers–Brownyard model:
--
--   * __Density__: A simplified linear model relating bulk density to
--     the water-cement ratio.  At w/c = 0.0 (dry cement), density
--     approaches 1500 kg/m³; at w/c = 0.5, about 1250 kg/m³.
--     Temperature contributes a small correction for thermal expansion.
--
--   * __Free energy__: \(\psi = -Q_{hyd} \cdot \alpha\), the Helmholtz
--     model where hydration releases latent heat proportional to the
--     degree of reaction.
--
--   * __Gel-space ratio__: \(x = \frac{0.68\,\alpha}{0.32\,\alpha + w/c}\),
--     the fraction of the available capillary space filled by C-S-H gel.
--     This is the core of Powers' insight: strength is controlled by
--     /how much/ of the pore space the gel occupies, not by total porosity.
--
--   * __Strength__: \(f_c = A \cdot x^3\), with \(A = 230\) MPa.
fromMix
  :: Double  -- ^ Water-cement ratio (w/c), typically 0.3–0.6
  -> Double  -- ^ Degree of hydration α ∈ [0, 1]
  -> Double  -- ^ Temperature (°C)
  -> ThermodynamicState
fromMix wc alpha temp =
  let
    rho    = 1000.0 + 500.0 * (1.0 - wc) - 0.5 * (temp - 20.0)
    psi    = negate (qHydration * alpha)
    gel    = powersGelSpaceRatio wc alpha
    fc     = intrinsicStrength * gel ** 3
    gelMax = powersGelSpaceRatio wc 1.0
    fcMax  = intrinsicStrength * gelMax ** 3
  in ThermodynamicState
    { density     = rho
    , freeEnergy  = psi
    , hydration   = alpha
    , strength    = fc
    , maxStrength = fcMax
    }

-- | Powers gel-space ratio: the fraction of capillary space occupied
-- by C-S-H gel.
--
-- \[
--   x = \frac{0.68\,\alpha}{0.32\,\alpha + w/c}
-- \]
--
-- When \(x \to 1\), all capillary pores are filled and the paste
-- reaches its theoretical maximum density and strength.
powersGelSpaceRatio :: Double -> Double -> Double
powersGelSpaceRatio wc alpha
  | denom < tolerance = 0.0
  | otherwise         = (0.68 * alpha) / denom
  where
    denom = 0.32 * alpha + wc
