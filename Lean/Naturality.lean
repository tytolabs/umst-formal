/-
  UMST-Formal: Naturality.lean
  Lean 4 — Natural-transformation proof for the thermodynamic gate.

  Core claim: the gate is material-agnostic.  It evaluates four
  thermodynamic invariants and never inspects which material class
  produced the state.  In categorical language, the gate is a natural
  transformation η : F ⟹ G between two functors on the discrete
  category MaterialClass.

  Mirrors Agda/Naturality.agda.

  Proof status: ALL theorems fully proved.  Zero sorry.

  Physical meaning:
    Mass conservation, Clausius-Duhem, hydration irreversibility, and
    strength monotonicity are thermodynamic identities that hold
    regardless of binder chemistry.  Lime mortar and OPC concrete differ
    substantially in reaction kinetics and microstructure, but both must
    satisfy the same thermodynamic constraints.  The gate enforces those
    constraints uniformly.
-/

import Gate

namespace UMST

-- ================================================================
-- SECTION 1: MaterialClass — Objects of a Discrete Category
-- ================================================================
-- MaterialClass enumerates the five binder families.  In category
-- theory, a discrete category has only identity morphisms.  We model
-- material morphisms as propositional equality (M₁ = M₂), so the
-- naturality square commutes vacuously — the gate never inspects the
-- material label.

/-- Five binder families in the UMST system. -/
inductive MaterialClass where
  | OPC        -- Ordinary Portland Cement
  | RAC        -- Recycled-Aggregate Concrete
  | Geopolymer -- Alkali-activated alumino-silicate
  | Lime       -- Air lime or hydraulic lime
  | Earth      -- Raw or stabilised earth
  deriving DecidableEq, Repr

open MaterialClass

-- ================================================================
-- SECTION 2: Functor F : MaterialClass → ThermodynamicState
-- ================================================================
-- F assigns each material class a canonical initial state.
-- This models `default_state_for(material)` in the Rust kernel.

/-- Initial state for each material class.
    Density values: OPC ≈ 2300, RAC ≈ 2100, Geopolymer ≈ 1900,
    Lime ≈ 1700, Earth ≈ 1500 kg/m³.  All start at zero hydration,
    zero strength, and zero Helmholtz energy (fully unreacted). -/
def stateFor : MaterialClass → ThermodynamicState
  | OPC        => ⟨2300, 0, 0, 0⟩
  | RAC        => ⟨2100, 0, 0, 0⟩
  | Geopolymer => ⟨1900, 0, 0, 0⟩
  | Lime       => ⟨1700, 0, 0, 0⟩
  | Earth      => ⟨1500, 0, 0, 0⟩

-- ================================================================
-- SECTION 3: Gate Decision — Bundled Evidence
-- ================================================================

-- ================================================================
-- SECTION 4: Naturality Theorems
-- ================================================================

/-- Gate material-agnosticism (structural):
    `gateCheck` accepts `ThermodynamicState` values, not
    `(MaterialClass, ThermodynamicState)` pairs.  Material-agnosticism
    is therefore a consequence of the type signature: `M₁` and `M₂`
    appear in the quantifier but not in the body.  This theorem makes
    that observation explicit. -/
theorem gateMaterialAgnostic
    (_M₁ _M₂ : MaterialClass)
    (old new : ThermodynamicState) :
    gateCheck old new = gateCheck old new := rfl

/-- Gate state-determinism:
    The gate outcome is determined entirely by the state values, not
    by any other context.  Formally: equal states ⇒ equal gate verdict. -/
theorem gateStateDetermined
    (old₁ new₁ old₂ new₂ : ThermodynamicState)
    (hold : old₁ = old₂)
    (hnew : new₁ = new₂) :
    gateCheck old₁ new₁ = gateCheck old₂ new₂ := by
  subst hold; subst hnew; rfl

/-- Naturality square:
    For any material morphism (M₁ = M₂), the gate commutes with the
    functor F.  In the discrete category, every morphism is an
    identity, so the square commutes trivially.

    Concretely: if M₁ = M₂ then stateFor M₁ = stateFor M₂, so the
    gate applied to stateFor M₁ gives the same result as applied to
    stateFor M₂. -/
theorem naturalitySquare
    (M₁ M₂ : MaterialClass)
    (h : M₁ = M₂)
    (new : ThermodynamicState) :
    gateCheck (stateFor M₁) new = gateCheck (stateFor M₂) new := by
  subst h; rfl

-- ================================================================
-- SECTION 5: Concrete Naturality Examples
-- ================================================================

/-- OPC example (definitional): the gate on the OPC initial state
    is deterministic — a concrete instance of `gateStateDetermined`. -/
theorem opcGateWellDefined (new : ThermodynamicState) :
    gateCheck (stateFor OPC) new = gateCheck (stateFor OPC) new := rfl

/-- Gate-refl for any initial state:
    A material's initial state is trivially admissible with itself
    (no transition), regardless of material class. -/
theorem stateForAdmissibleRefl (M : MaterialClass) :
    Admissible (stateFor M) (stateFor M) :=
  admissibleRefl (stateFor M)

/-- Monoidal interpretation — mass as a monoidal constraint:
    If two states s1 and s2 both come from the same material initial
    state, the density difference is zero (≤ δMass).  This is the
    monoidal structure comment from Naturality.agda: mass conservation
    is a constraint that the gate η respects. -/
theorem initialStateMassConserved (M : MaterialClass) :
    MassCond (stateFor M) (stateFor M) := by
  simp [MassCond, sub_self, abs_zero, δMass]

end UMST
