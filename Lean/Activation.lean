/-
  UMST-Formal: Activation.lean
  Lean 4 — Material activations as dependent types.

  Core idea: each material class activates a specific subset of
  physics engines.  This module encodes that relationship as a
  function ActivatedUMST : MaterialClass → Type that returns a record
  of engine flags indexed by the material.  The dependent typing
  ensures at compile time that every material has the correct engines
  enabled.

  Mirrors Agda/Activation.agda.

  Proof status: ALL theorems fully proved.  Zero sorry.

  Sheaf-theory perspective:
    The activation map is a global section of a sheaf over the discrete
    space MaterialClass.  The base space is MaterialClass (discrete
    topology).  The sheaf assigns to each singleton {M} the set of
    valid engine configurations for M.  See Activation.agda §13 for
    the extended sheaf commentary.
-/

import Gate
import Naturality

namespace UMST

open MaterialClass

-- ================================================================
-- SECTION 1: Physics Engine Enumeration
-- ================================================================

/-- Eight physics engines, each modelling one physical process.
    Correspondence to Rust: `PhysicsEngine` enum in `umst-core`. -/
inductive Engine where
  | Hydration        -- OPC/RAC: C₃S + H₂O → C-S-H + CH
  | AlkaliActivation -- Geopolymer: source + activator → N-A-S-H
  | Carbonation      -- Lime: Ca(OH)₂ + CO₂ → CaCO₃ + H₂O
  | MoistureSorption -- Earth: clay ↔ water vapour (hygroscopic)
  | Strength         -- All materials: strength evolution model
  | Rheology         -- All materials: workability / flow (Bingham)
  | Thermal          -- OPC/RAC: heat of reaction / transport
  | Transport        -- RAC: moisture and ion transport (Fick)
  deriving DecidableEq, Repr

open Engine

-- ================================================================
-- SECTION 2: EngineSet — Boolean Characteristic Function
-- ================================================================

/-- An EngineSet is a Boolean-valued predicate on Engine.
    `es e = true` iff engine e is active.
    Corresponds to `HashSet<PhysicsEngine>` in the Rust kernel. -/
abbrev EngineSet := Engine → Bool

/-- Engine membership: engine e is in set es. -/
def engineMember (e : Engine) (es : EngineSet) : Prop := es e = true

notation:50 e " ∈ₑ " es => engineMember e es
notation:50 e " ∉ₑ " es => ¬ engineMember e es

-- ================================================================
-- SECTION 3: Activation Profiles
-- ================================================================
-- Arguments order: Hyd, Alkali, Carb, Moist, Str, Rheo, Therm, Trans.

private def mkEngineSet
    (hyd alk carb moist str rheo therm trans : Bool) : EngineSet
  | Hydration        => hyd
  | AlkaliActivation => alk
  | Carbonation      => carb
  | MoistureSorption => moist
  | Strength         => str
  | Rheology         => rheo
  | Thermal          => therm
  | Transport        => trans

/-- OPC: Hydration + Strength + Rheology + Thermal. -/
def opcEngines    : EngineSet := mkEngineSet true  false false false true true true  false
/-- RAC: all OPC engines plus Transport (2-3× porosity). -/
def racEngines    : EngineSet := mkEngineSet true  false false false true true true  true
/-- Geopolymer: AlkaliActivation + Strength + Rheology. -/
def geoEngines    : EngineSet := mkEngineSet false true  false false true true false false
/-- Lime: Carbonation + Strength + Rheology. -/
def limeEngines   : EngineSet := mkEngineSet false false true  false true true false false
/-- Earth: MoistureSorption + Strength + Rheology. -/
def earthEngines  : EngineSet := mkEngineSet false false false true  true true false false

-- ================================================================
-- SECTION 4: Canonical Activation Map
-- ================================================================

/-- The activation function maps each material to its engine set.
    Type-level function; the core of the dependent typing. -/
def activation : MaterialClass → EngineSet
  | OPC        => opcEngines
  | RAC        => racEngines
  | Geopolymer => geoEngines
  | Lime       => limeEngines
  | Earth      => earthEngines

-- ================================================================
-- SECTION 5: ActivatedUMST — Dependent Type Indexed by Material
-- ================================================================

/-- An ActivatedUMST M is a record bundling an engine set together
    with a proof that it equals the canonical activation for M.
    This prevents misconfigurations: you cannot claim OPC activation
    while using lime's engine set — the proof would fail. -/
structure ActivatedUMST (M : MaterialClass) where
  engines   : EngineSet
  activated : engines = activation M

/-- Smart constructors — canonical activations for each material. -/
def activateOPC        : ActivatedUMST OPC        := ⟨opcEngines,   rfl⟩
def activateRAC        : ActivatedUMST RAC        := ⟨racEngines,   rfl⟩
def activateGeopolymer : ActivatedUMST Geopolymer := ⟨geoEngines,   rfl⟩
def activateLime       : ActivatedUMST Lime       := ⟨limeEngines,  rfl⟩
def activateEarth      : ActivatedUMST Earth      := ⟨earthEngines, rfl⟩

-- ================================================================
-- SECTION 6: Totality — Every Material Has at Least One Engine
-- ================================================================

/-- There exists at least one active engine in this set. -/
def HasActiveEngine (es : EngineSet) : Prop :=
  ∃ e : Engine, e ∈ₑ es

/-- Theorem (Activation Totality):
    Every material class has at least one active engine.
    Proved by exhaustive case analysis; Strength is the universal
    witness (active for all five materials). -/
theorem activationTotal (M : MaterialClass) :
    HasActiveEngine (activation M) := by
  cases M with
  | OPC        => exact ⟨Strength, rfl⟩
  | RAC        => exact ⟨Strength, rfl⟩
  | Geopolymer => exact ⟨Strength, rfl⟩
  | Lime       => exact ⟨Strength, rfl⟩
  | Earth      => exact ⟨Strength, rfl⟩

-- ================================================================
-- SECTION 7: Characteristic Engine Witnesses
-- ================================================================
-- Each material has its specific characteristic engine active.

theorem opc_has_hydration    : Hydration        ∈ₑ activation OPC        := rfl
theorem rac_has_transport    : Transport        ∈ₑ activation RAC        := rfl
theorem geo_has_alkali       : AlkaliActivation ∈ₑ activation Geopolymer := rfl
theorem lime_has_carbonation : Carbonation      ∈ₑ activation Lime       := rfl
theorem earth_has_moisture   : MoistureSorption ∈ₑ activation Earth      := rfl

-- ================================================================
-- SECTION 8: Negative Proofs
-- ================================================================
-- Certain engines must NOT activate for certain materials.
-- These prevent physical nonsense like running hydration on raw earth.

theorem earth_no_hydration     : Hydration    ∉ₑ activation Earth      := by simp [engineMember, activation, earthEngines, mkEngineSet]
theorem lime_no_hydration      : Hydration    ∉ₑ activation Lime       := by simp [engineMember, activation, limeEngines, mkEngineSet]
theorem opc_no_carbonation     : Carbonation  ∉ₑ activation OPC        := by simp [engineMember, activation, opcEngines, mkEngineSet]
theorem opc_no_transport       : Transport    ∉ₑ activation OPC        := by simp [engineMember, activation, opcEngines, mkEngineSet]
theorem geo_no_hydration       : Hydration    ∉ₑ activation Geopolymer := by simp [engineMember, activation, geoEngines, mkEngineSet]

-- ================================================================
-- SECTION 9: Decidability
-- ================================================================

/-- Engine membership is decidable for all materials and engines. -/
instance activationDecidable (M : MaterialClass) (e : Engine) :
    Decidable (e ∈ₑ activation M) :=
  decEq (activation M e) true

end UMST
