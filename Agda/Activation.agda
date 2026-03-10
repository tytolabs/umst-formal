------------------------------------------------------------------------
-- UMST-Formal: Activation.agda
--
-- Material activations as dependent types.
--
-- Core idea:  Each material class activates a specific subset of
-- physics engines.  This module encodes that relationship as a
-- *dependent type*: ActivatedUMST is a type-level function
--
--     ActivatedUMST : MaterialClass → Set
--
-- that returns a record of engine flags indexed by the material.
-- The dependent typing ensures at compile time that every material
-- has the correct engines enabled — you cannot run OPC without
-- hydration, and you cannot accidentally enable alkali-activation
-- for lime.
--
-- Physical basis:
--   The activation profiles are determined by the dominant transport and
--   reaction mechanisms of each material class.  For example:
--     - RAC requires an extra transport engine because recycled
--       aggregates have 2-3× the porosity of virgin aggregates,
--       causing moisture and chloride transport to dominate durability.
--     - Lime requires a carbonation engine (not hydration) because
--       air lime hardens by reacting with atmospheric CO₂, not water.
--     - Earth requires a moisture-sorption engine because unbaked
--       earth is hygroscopic — its strength depends on ambient RH.
--   These are not theoretical choices; they come from running real
--   material tests and seeing which physics actually matters.
--
-- Sheaf-theory perspective:
--   The activation map can be understood as a *section of a sheaf*
--   over the material classification space.  The base space is
--   MaterialClass (a discrete topological space).  The sheaf assigns
--   to each open set (singleton {M}) the set of valid engine
--   configurations for M.  A global section — an activation for
--   every material — is exactly what ActivatedUMST provides.
--
--   The sheaf perspective becomes non-trivial at finer scales:
--   if we refine MaterialClass into sub-classes (e.g., OPC-CEM-I,
--   OPC-CEM-II/A-LL, OPC-CEM-III/B), the restriction maps of the
--   sheaf must be compatible.  A CEM-III/B activation (with extra
--   slag hydration) must restrict consistently to the generic OPC
--   activation.  This compatibility is the sheaf's gluing condition
--   and corresponds physically to the requirement that specialised
--   models are consistent refinements of generic ones.
--
--   At the multi-scale level (micro → meso → macro), we get a
--   sheaf over a two-dimensional base: (material class) × (length
--   scale).  The sections at different scales must be compatible
--   through restriction (coarse-graining) maps.  This is the
--   formal version of "the macro model is a homogenised version
--   of the micro model".
--
-- Correspondence to Rust:
--   ActivatedUMST ↔ activated_engines field in UMSTInstance
--   EngineSet     ↔ PhysicsEngine enum + HashSet<PhysicsEngine>
--   totality      ↔ match on MaterialType with no missing arms
------------------------------------------------------------------------

module Activation where

------------------------------------------------------------------------
-- Imports
------------------------------------------------------------------------

-- We import Gate for ThermodynamicState and the gate, so we can
-- connect activated engines back to the gate's domain.
open import Gate using (ThermodynamicState; Admissible; gate)

-- We import MaterialClass from Naturality to reuse the same type.
open import Naturality using (MaterialClass; OPC; RAC; Geopolymer; Lime; Earth)

-- Standard library imports.
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

------------------------------------------------------------------------
-- 1. Physics Engine Enumeration
------------------------------------------------------------------------

-- Each physics engine models one physical process.  The Rust kernel
-- has a trait PhysicsEngine with implementations for each process.
-- Here we enumerate them as a simple data type.
--
-- Physical meaning:
--   Hydration        — OPC/RAC cement hydration (C₃S + water → C-S-H + CH)
--   AlkaliActivation — geopolymer reaction (source + activator → N-A-S-H gel)
--   Carbonation      — lime carbonation (Ca(OH)₂ + CO₂ → CaCO₃ + H₂O)
--   MoistureSorption — earth hygroscopic equilibrium (clay ↔ water vapour)
--   Strength         — compressive/tensile strength evolution (Powers model)
--   Rheology         — workability / flow behaviour (Bingham model)
--   Thermal          — heat of reaction / thermal transport (Fourier + source)
--   Transport        — moisture and ion transport (Fick/Richards equation)

data Engine : Set where
  Hydration        : Engine
  AlkaliActivation : Engine
  Carbonation      : Engine
  MoistureSorption : Engine
  Strength         : Engine
  Rheology         : Engine
  Thermal          : Engine
  Transport        : Engine

------------------------------------------------------------------------
-- 2. EngineSet — a Boolean-valued characteristic function
------------------------------------------------------------------------

-- An EngineSet is a predicate on Engine: for each engine, it says
-- whether that engine is active (true) or inactive (false).
--
-- Mathematically:  EngineSet = Engine → Bool
-- This is the characteristic function of a subset of Engine.
-- In the Rust kernel this is a HashSet<PhysicsEngine>.

EngineSet : Set
EngineSet = Engine → Bool
  -- A function from Engine to Bool.
  -- If (es e ≡ true), engine e is active.
  -- If (es e ≡ false), engine e is inactive.

------------------------------------------------------------------------
-- 3. Engine membership predicate
------------------------------------------------------------------------

-- We lift Bool into Prop via T (the "truth" of a boolean).
-- T true = ⊤ (trivially true), T false = ⊥ (impossible).
-- This lets us write propositions about engine membership.

_∈ₑ_ : Engine → EngineSet → Set
e ∈ₑ es = T (es e)
  -- "Engine e is a member of engine set es"
  -- i.e., es maps e to true.

------------------------------------------------------------------------
-- 4. Activation Profiles — Which Engines Each Material Needs
------------------------------------------------------------------------

-- For each material class, we define the specific set of engines
-- that must be activated.  These profiles encode the dominant physical
-- mechanisms for each material, as determined by materials science
-- literature and field observation.

-- Helper: construct an EngineSet from explicit per-engine booleans.
-- This avoids repetitive pattern-matching in each profile definition.
-- Arguments are in the order: Hyd, Alkali, Carb, Moist, Str, Rheo, Therm, Trans.
mkEngineSet : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → EngineSet
mkEngineSet hyd alk carb moist str rheo therm trans = go
  where
  go : Engine → Bool
  go Hydration        = hyd
  go AlkaliActivation = alk
  go Carbonation      = carb
  go MoistureSorption = moist
  go Strength         = str
  go Rheology         = rheo
  go Thermal          = therm
  go Transport        = trans

-- OPC activation profile:
--   Hydration + Strength + Rheology + Thermal
--   (standard Portland cement: hydration drives everything)
opcEngines : EngineSet
opcEngines = mkEngineSet true false false false true true true false
  -- Hydration:  C₃S/C₂S react with water → C-S-H gel
  -- Strength:   Powers model fc = S·x³ driven by hydration degree α
  -- Rheology:   workability window (slump loss) as hydration progresses
  -- Thermal:    exothermic reaction; important for mass concrete

-- RAC activation profile:
--   Hydration + Strength + Rheology + Thermal + Transport
--   (everything OPC has, plus transport for the porous recycled aggregates)
racEngines : EngineSet
racEngines = mkEngineSet true false false false true true true true
  -- All OPC engines plus:
  -- Transport:  recycled aggregates have 2-3× porosity of virgin stone;
  --             moisture and chloride transport dominate durability.
  --             RAC durability predictions are systematically under-
  --             estimated without an explicit transport model.

-- Geopolymer activation profile:
--   AlkaliActivation + Strength + Rheology
--   (no Portland hydration; alkali-activated instead)
geopolymerEngines : EngineSet
geopolymerEngines = mkEngineSet false true false false true true false false
  -- AlkaliActivation:  fly ash/slag + NaOH/Na₂SiO₃ → N-A-S-H / C-A-S-H gel
  -- Strength:  strength evolution follows a different kinetic model
  -- Rheology:  highly sensitive to activator dosage and temperature
  -- No Thermal:  geopolymer reactions are mildly exothermic but thermal
  --              transport is less critical than for OPC mass pours

-- Lime activation profile:
--   Carbonation + Strength + Rheology
--   (lime hardens by atmospheric CO₂ absorption, not hydration)
limeEngines : EngineSet
limeEngines = mkEngineSet false false true false true true false false
  -- Carbonation:  Ca(OH)₂ + CO₂ → CaCO₃; this IS the hardening mechanism
  -- Strength:  develops slowly (months to years) as carbonation front advances
  -- Rheology:  lime putty workability is exceptional but time-dependent
  -- No Hydration:  air lime does not hydrate (hydraulic lime is a hybrid;
  --                we model it as OPC + Lime in the Rust kernel)

-- Earth activation profile:
--   MoistureSorption + Strength + Rheology
--   (unbaked earth depends on ambient relative humidity)
earthEngines : EngineSet
earthEngines = mkEngineSet false false false true true true false false
  -- MoistureSorption:  clay minerals adsorb/desorb water vapour; strength
  --                    is a function of moisture content, not chemical reaction
  -- Strength:  depends on compaction, clay content, and current moisture state
  -- Rheology:  earth mixes are plastic and exhibit thixotropy
  -- No Hydration/Carbonation:  raw earth has no cementitious reaction
  --                            (stabilised earth with cement → use OPC + Earth)

------------------------------------------------------------------------
-- 5. ActivatedUMST — Dependent Type Indexed by Material
------------------------------------------------------------------------

-- The activation function maps each material class to its engine set.
-- This is a type-level function and the core of the dependent typing.
--
-- In the Rust kernel, this is a match on MaterialType that returns
-- the appropriate set of physics engine instances.

activation : MaterialClass → EngineSet
activation OPC        = opcEngines
activation RAC        = racEngines
activation Geopolymer = geopolymerEngines
activation Lime       = limeEngines
activation Earth      = earthEngines

-- ActivatedUMST M is a proof that material M has been assigned a
-- specific engine set.  It bundles the engine set together with a
-- proof that it equals the canonical activation for M.
--
-- This is the "dependent type indexed by material class": the *type*
-- of the record depends on *which material* you pass in.

record ActivatedUMST (M : MaterialClass) : Set where
  constructor mkActivated
  field
    engines   : EngineSet
    -- The actual engine set assigned to this material instance.

    activated : engines ≡ activation M
    -- Proof that the assigned engines match the canonical profile.
    -- This prevents misconfigurations: you can't claim OPC activation
    -- while actually using lime's engine set.

open ActivatedUMST

------------------------------------------------------------------------
-- 6. Smart Constructors — Build ActivatedUMST for Each Material
------------------------------------------------------------------------

-- For each material class, we provide a constructor that produces
-- the canonical ActivatedUMST.  These serve as both convenience
-- functions and as proofs that each material *can* be activated.

activate-OPC : ActivatedUMST OPC
activate-OPC = mkActivated opcEngines refl
  -- OPC gets (Hydration, Strength, Rheology, Thermal) — proved by refl.

activate-RAC : ActivatedUMST RAC
activate-RAC = mkActivated racEngines refl
  -- RAC gets (Hydration, Strength, Rheology, Thermal, Transport).

activate-Geopolymer : ActivatedUMST Geopolymer
activate-Geopolymer = mkActivated geopolymerEngines refl
  -- Geopolymer gets (AlkaliActivation, Strength, Rheology).

activate-Lime : ActivatedUMST Lime
activate-Lime = mkActivated limeEngines refl
  -- Lime gets (Carbonation, Strength, Rheology).

activate-Earth : ActivatedUMST Earth
activate-Earth = mkActivated earthEngines refl
  -- Earth gets (MoistureSorption, Strength, Rheology).

------------------------------------------------------------------------
-- 7. Totality: Every Material Has at Least One Engine
------------------------------------------------------------------------

-- Theorem (Activation Totality):
-- Every material class has at least one active engine.
-- This guarantees that the simulation never runs with an empty engine
-- set, which would be physically meaningless and would produce a
-- state transition that is trivially admissible but carries no
-- physical information.
--
-- Formally: for every M, there exists an Engine e such that
-- e ∈ₑ (activation M).  We prove this by exhibiting a witness
-- for each material.

-- HasActiveEngine: there exists at least one engine in the set.
HasActiveEngine : EngineSet → Set
HasActiveEngine es = Σ Engine (λ e → e ∈ₑ es)
  -- A pair: an engine `e` and a proof that `e` is in the set.
  -- The Σ type (dependent pair) is the existential quantifier.

-- Proof of totality: exhaustive case analysis on MaterialClass.
activation-total : ∀ (M : MaterialClass) → HasActiveEngine (activation M)
activation-total OPC        = Strength , tt
  -- OPC: the Strength engine is active (opcEngines Strength ≡ true).
  -- We could equally pick Hydration, Rheology, or Thermal.
  -- tt : ⊤ is the proof that T true holds.
activation-total RAC        = Strength , tt
  -- RAC: Strength is active (among five active engines).
activation-total Geopolymer = Strength , tt
  -- Geopolymer: Strength is active (among three active engines).
activation-total Lime       = Strength , tt
  -- Lime: Strength is active (among three active engines).
activation-total Earth      = Strength , tt
  -- Earth: Strength is active (among three active engines).
  -- Note: Strength is the common engine across ALL material classes.
  -- This is not coincidental — every construction material must have
  -- a strength model, because strength is what makes it a *structural*
  -- material.  This universality echoes the naturality theorem from
  -- Naturality.agda: some physics is truly material-agnostic.

------------------------------------------------------------------------
-- 8. Stronger Totality: Specific Engine Witnesses
------------------------------------------------------------------------

-- We can also prove that each material has its *characteristic*
-- engine active — the one that distinguishes it from the others.
-- This is a stronger statement than "at least one engine exists":
-- it says each material has its *specific* physics.

opc-has-hydration : Hydration ∈ₑ activation OPC
opc-has-hydration = tt
  -- OPC's characteristic engine is Hydration.
  -- T (opcEngines Hydration) = T true = ⊤, proved by tt.

rac-has-transport : Transport ∈ₑ activation RAC
rac-has-transport = tt
  -- RAC's distinguishing engine is Transport (extra porosity).
  -- This is what makes RAC modelling different from OPC modelling.

geopolymer-has-alkali : AlkaliActivation ∈ₑ activation Geopolymer
geopolymer-has-alkali = tt
  -- Geopolymer's characteristic engine is AlkaliActivation.
  -- No Portland clinker → no Hydration engine.

lime-has-carbonation : Carbonation ∈ₑ activation Lime
lime-has-carbonation = tt
  -- Lime's characteristic engine is Carbonation.
  -- CO₂ absorption, not water reaction, drives hardening.

earth-has-moisture : MoistureSorption ∈ₑ activation Earth
earth-has-moisture = tt
  -- Earth's characteristic engine is MoistureSorption.
  -- Clay minerals interact with ambient humidity, not with CO₂ or water
  -- in the cementitious sense.

------------------------------------------------------------------------
-- 9. Negative Proofs: Engines That Should NOT Activate
------------------------------------------------------------------------

-- Equally important: we can prove that certain engines are NOT active
-- for certain materials.  This prevents physical nonsense like running
-- hydration on raw earth or carbonation on OPC.

-- Negation of membership: e is NOT in the engine set.
_∉ₑ_ : Engine → EngineSet → Set
e ∉ₑ es = T (es e) → ⊥
  -- If es maps e to true, we derive a contradiction.
  -- If es maps e to false, T false = ⊥, and ⊥ → ⊥ holds vacuously.

earth-no-hydration : Hydration ∉ₑ activation Earth
earth-no-hydration ()
  -- Proof: T (earthEngines Hydration) = T false = ⊥.
  -- The empty pattern () discharges the impossible premise.
  -- Physical meaning: raw earth does not hydrate.

lime-no-hydration : Hydration ∉ₑ activation Lime
lime-no-hydration ()
  -- Air lime does not hydrate (hydraulic lime is modelled separately).

opc-no-carbonation : Carbonation ∉ₑ activation OPC
opc-no-carbonation ()
  -- Fresh OPC paste does not carbonate (carbonation of OPC is a
  -- degradation mechanism modelled separately in durability analysis).

opc-no-transport : Transport ∉ₑ activation OPC
opc-no-transport ()
  -- Standard OPC does not need the transport engine.
  -- RAC does, because of the extra porosity in recycled aggregates.

geopolymer-no-hydration : Hydration ∉ₑ activation Geopolymer
geopolymer-no-hydration ()
  -- Geopolymers have no Portland clinker; no C₃S/C₂S hydration.

------------------------------------------------------------------------
-- 10. Engine Count: How Many Engines Each Material Activates
------------------------------------------------------------------------

-- Expected engine counts per material class:
--   OPC:        4 engines (Hyd, Str, Rheo, Therm)
--   RAC:        5 engines (Hyd, Str, Rheo, Therm, Trans)
--   Geopolymer: 3 engines (Alk, Str, Rheo)
--   Lime:       3 engines (Carb, Str, Rheo)
--   Earth:      3 engines (Moist, Str, Rheo)

------------------------------------------------------------------------
-- 11. Activation is Decidable
------------------------------------------------------------------------

-- For any material and any engine, we can decide whether the engine
-- is active.  This is because EngineSet is Boolean-valued (not
-- Prop-valued), so membership is decidable by construction.

open import Relation.Nullary using (Dec; yes; no)

activation-decidable : ∀ (M : MaterialClass) (e : Engine) →
                       Dec (e ∈ₑ activation M)
activation-decidable M e with activation M e
... | true  = yes tt
  -- If the Boolean is true, T true = ⊤, witnessed by tt.
... | false = no (λ ())
  -- If the Boolean is false, T false = ⊥, and ⊥ is uninhabited.
  -- The absurd pattern () discharges the impossible proof.

------------------------------------------------------------------------
-- 12. Connecting Activation to the Gate
------------------------------------------------------------------------

-- The activation profile determines which physics engines update the
-- ThermodynamicState.  The gate (from Gate.agda) then checks whether
-- the updated state is admissible.  This section states the key
-- relationship: every activated engine must produce state transitions
-- that the gate can evaluate.
--
-- We express this as a postulate because the full proof requires
-- formalising each engine's output as a ThermodynamicState transformer.

postulate
  -- Each engine, when active for material M, produces a state
  -- transition that is well-formed (all four fields are defined).
  -- The gate then checks admissibility.
  engine-produces-state :
    ∀ (M : MaterialClass) (e : Engine) →
    e ∈ₑ activation M →
    (ThermodynamicState → ThermodynamicState)
  -- Given material M and an active engine e (with membership proof),
  -- we get a function from old state to proposed new state.
  -- The gate can then be applied: gate old (engine-produces-state M e p old).

------------------------------------------------------------------------
-- 13. Sheaf-Theoretic Commentary (Extended)
------------------------------------------------------------------------
--
-- The activation map  activation : MaterialClass → EngineSet  can be
-- understood through the lens of sheaf theory on a topological space:
--
-- Base space:
--   X = MaterialClass (discrete topology: every subset is open).
--
-- Sheaf:
--   F : Open(X) → Set
--   F({M}) = { valid engine configurations for material M }
--          = { es : EngineSet | es ≡ activation M }
--   F(∅)   = ⊤  (the terminal object — vacuously true)
--   F(X)   = ∏_M F({M})  (product over all materials)
--
-- Global section:
--   A global section σ ∈ F(X) is a function that assigns to each
--   material its engine set, consistently.  The activation function
--   is precisely such a global section.
--
-- Restriction maps:
--   For U ⊆ V, the restriction res_{V,U} : F(V) → F(U) is just
--   projection to the components in U.  Since the space is discrete,
--   every presheaf is a sheaf (the gluing condition is trivially
--   satisfied).
--
-- Multi-scale refinement (future work):
--   In the multi-scale setting, the base space becomes a poset of
--   length scales: micro (μm) → meso (mm) → macro (m).  The sheaf
--   assigns to each scale the set of valid engine configurations at
--   that resolution.  The restriction maps are homogenisation
--   (coarse-graining) operators:
--
--     res_{micro,meso} : F(micro) → F(meso)
--
--   A C-S-H nucleation engine active at the micro scale restricts
--   (homogenises) to the bulk hydration engine at the meso scale.
--   The sheaf gluing condition then says: if two meso-scale patches
--   agree on their overlap, they can be consistently glued into a
--   macro-scale model.  This is the mathematical version of
--   "multi-scale consistency".
--
-- Material sub-classification (future work):
--   If we refine MaterialClass into sub-classes (e.g., OPC-CEM-I,
--   OPC-CEM-II/A-LL), the topology becomes non-trivial (CEM-II is
--   an open subset of OPC).  The restriction map
--
--     res_{OPC, CEM-II} : F(OPC) → F(CEM-II)
--
--   must produce a valid CEM-II activation that is a refinement
--   (possibly superset) of the generic OPC activation.  The sheaf
--   condition prevents contradictory specialisations.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 14. Summary
------------------------------------------------------------------------
--
-- What we defined:
--   1. Engine: enumeration of 8 physics engines.
--   2. EngineSet: engine sets as characteristic functions.
--   3. Activation profiles for 5 material classes (OPC, RAC,
--      Geopolymer, Lime, Earth).
--   4. ActivatedUMST: dependent type indexed by MaterialClass,
--      bundling engine set with a correctness proof.
--
-- What we proved:
--   5. Activation totality: every material has ≥ 1 active engine.
--   6. Specific witnesses: each material has its characteristic engine.
--   7. Negative proofs: certain engines do NOT activate for certain
--      materials (e.g., Earth has no Hydration).
--   8. Decidability: engine membership is decidable for all materials.
--
-- Sheaf perspective:
--   9. The activation map is a global section of a sheaf over the
--      discrete space MaterialClass.
--  10. Multi-scale and sub-classification refinements correspond to
--      sheaf restriction maps and gluing conditions.
--
-- Why this matters:
--   The activation profiles are not arbitrary choices.  They reflect
--   which physical mechanisms dominate for each material class, as
--   established by materials science and corroborated by field
--   observation.  The dependent typing ensures that the profiles are
--   enforced at compile time — you cannot misconfigure the engine set
--   for a given material without
--   a type error.  This is safety-by-construction, not safety-by-
--   testing.
------------------------------------------------------------------------
