/-
  UMST-Formal: DIBKleisli.lean
  Lean 4 — Discovery-Invention-Build loop as a Kleisli monad.

  The DIB loop is the methodological backbone of UMST:

    Discovery  →  Invention  →  Build
    (observe)     (formalise)   (implement)

  Each phase transforms one kind of knowledge into another.  In
  categorical terms, each phase is a Kleisli arrow in a State monad.
  Kleisli composition (>=>) threads the evolving state through all
  three phases.  The monad laws guarantee coherent composition.

  Mirrors Agda/DIB-Kleisli.agda.

  Proof status: monad laws and associativity fully proved by funext
  and computation.  Phase types are empty structures (no axioms); `discover`,
  `invent`, and `build` stay opaque Kleisli arrows — an execution model would
  refine them.  Zero sorry.

  Each phase has a concrete referent:
    Discovery: field measurement → Observation values (informal constraints)
    Invention: inductive generalisation → UMST types + gate predicates
    Build:     gate implementation in the Rust kernel (umst-prototype-2a)
-/

import Gate

namespace UMST

-- ================================================================
-- SECTION 1: State Monad
-- ================================================================
-- We define a State monad without relying on Mathlib's monad
-- infrastructure, keeping it readable for non-Lean specialists.
--
--   M A = DIBState → (A × DIBState)
--
-- The state S represents accumulated knowledge/artefacts.
-- The value A is the output of each phase.

/-- The mutable context threaded through the DIB pipeline.
    Contains everything from raw field notes through formal models to
    compiled artefacts.  Kept opaque — extending it is future work. -/
opaque DIBState : Type

/-- The State monad: a computation that reads and updates DIBState
    while producing a value of type A. -/
structure M (A : Type) where
  runM : DIBState → A × DIBState

-- ================================================================
-- SECTION 2: Monad Operations
-- ================================================================

/-- `pure a`: inject a pure value into M without modifying the state.
    Physical meaning: "accepting a fact without changing the knowledge base." -/
def pureM {A : Type} (a : A) : M A :=
  ⟨fun s => (a, s)⟩

/-- `m >>= f`: run m, then feed its output to f.
    Physical meaning: "apply the next phase of the pipeline." -/
def bindM {A B : Type} (m : M A) (f : A → M B) : M B :=
  ⟨fun s =>
    let (a, s') := m.runM s
    (f a).runM s'⟩

instance : Monad M where
  pure  := pureM
  bind  := bindM

/-- Kleisli composition: compose two Kleisli arrows. -/
def kleisliArrowCompose {A B C : Type}
    (f : A → M B) (g : B → M C) : A → M C :=
  fun a => bindM (f a) g

-- Local notation only: Mathlib (via `import Gate`) also defines `>=>`, which
-- would make `discover >=> invent >=> build` ambiguous.
local infixr:55 " >=>ᴹ " => kleisliArrowCompose

-- ================================================================
-- SECTION 3: Monad Laws
-- ================================================================
-- All three monad laws hold by funext + definitional computation.

/-- Left unit: pure a >>= f = f a. -/
theorem leftUnit {A B : Type} (a : A) (f : A → M B) :
    bindM (pureM a) f = f a := by
  simp [bindM, pureM]

/-- Right unit: m >>= pure = m. -/
theorem rightUnit {A : Type} (m : M A) :
    bindM m pureM = m := by
  cases m with | mk r => rfl

/-- Associativity: (m >>= f) >>= g = m >>= (fun a => f a >>= g). -/
theorem assocM {A B C : Type} (m : M A) (f : A → M B) (g : B → M C) :
    bindM (bindM m f) g = bindM m (fun a => bindM (f a) g) := by
  cases m with | mk r => rfl

-- ================================================================
-- SECTION 4: Kleisli Associativity
-- ================================================================

/-- Kleisli arrow composition is associative. -/
theorem kleisliAssoc {A B C D : Type}
    (f : A → M B) (g : B → M C) (h : C → M D) :
    (f >=>ᴹ g) >=>ᴹ h = f >=>ᴹ (g >=>ᴹ h) := by
  funext a
  cases (f a) with | mk r => rfl

/-- Left unit for Kleisli: pure >=> f = f. -/
theorem kleisliLeftUnit {A B : Type} (f : A → M B) :
    (pureM >=>ᴹ f) = f := by
  funext a
  simp [kleisliArrowCompose, bindM, pureM]

/-- Right unit for Kleisli: f >=> pure = f. -/
theorem kleisliRightUnit {A B : Type} (f : A → M B) :
    (f >=>ᴹ pureM) = f := by
  funext a
  simp only [kleisliArrowCompose, pureM]
  cases (f a) with | mk r =>
  simp [bindM]; rfl

-- ================================================================
-- SECTION 5: DIB Phase Types and Arrows
-- ================================================================
-- Empty carriers: document the phase discipline without axioms.  Field/Core
-- code can extend these with real payloads; the monad structure is unchanged.

/-- Output of the Discovery phase: structured field observation (synthetic root). -/
structure Observation deriving Inhabited
/-- Output of the Invention phase: formal invariant candidate (synthetic root). -/
structure Insight deriving Inhabited
/-- UMST mathematical specification produced in Invention (synthetic root). -/
structure Design deriving Inhabited
/-- Executable artefact from Build, e.g. kernel bundle (synthetic root). -/
structure Artifact deriving Inhabited

instance [Inhabited A] : Inhabited (M A) := ⟨⟨fun s => (default, s)⟩⟩

/-- Discovery phase: field observation → formal observation record. -/
noncomputable opaque discover : Observation → M Insight

/-- Invention phase: field insight → formal gate design. -/
noncomputable opaque invent : Insight → M Design

/-- Build phase: formal design → executable Rust kernel artefact. -/
noncomputable opaque build : Design → M Artifact

-- ================================================================
-- SECTION 6: The DIB Pipeline
-- ================================================================

/-- The full Discovery-Invention-Build pipeline as a Kleisli arrow.
    Starting from a field observation, it produces a compiled artefact.
    The monad laws ensure the pipeline is a coherent sequential
    composition with no information loss between phases. -/
noncomputable def dib : Observation → M Artifact :=
  (discover >=>ᴹ invent) >=>ᴹ build

/-- Pipeline associativity:
    (discover >=>ᴹ invent) >=>ᴹ build = discover >=>ᴹ (invent >=>ᴹ build).
    Follows from kleisliAssoc — order of bracketing doesn't matter. -/
theorem dibAssoc :
    (discover >=>ᴹ invent) >=>ᴹ build = discover >=>ᴹ (invent >=>ᴹ build) :=
  kleisliAssoc discover invent build

-- ================================================================
-- SECTION 7: Semantics tier — artifacts and the thermodynamic gate
-- ================================================================
-- Abstract `discover` / `invent` / `build` stay opaque.  This section fixes a
-- **minimal** interpretation of build outputs into state space and proves
-- admissibility + agreement with the executable `gateCheck`.
--
-- Full Field/Core functor story is future work; current witness is minimal but
-- non-vacuous: `Artifact` induces a **non-identity** dissipative step on ψ at
-- fixed (ρ, α, fc), then we show `gateCheck` returns true (lawful interpreter).

/-- Interpret a build artifact as a one-step thermodynamic evolution. -/
class DIBArtifactSemantics (α : Type) where
  nextState : α → ThermodynamicState → ThermodynamicState

/-- Apply semantic `nextState` for an artifact-like value. -/
@[simp]
def interpretArtifact {α : Type} [DIBArtifactSemantics α] (a : α) (s : ThermodynamicState) :
    ThermodynamicState :=
  DIBArtifactSemantics.nextState a s

/-- One-step post-Build thermo snapshot: decrease ψ by a fixed rational amount at
    unchanged (ρ, α, fc).  Models a documented irreversible relaxation carried
    through the artefact bundle (not the identity map on `ThermodynamicState`). -/
def artifactSemanticStep (s : ThermodynamicState) : ThermodynamicState :=
  ⟨s.density, s.freeEnergy - 1, s.hydration, s.strength⟩

/-- Canonical `Artifact` semantics: every build output triggers the same lawful
    dissipative micro-step (artifact tag ignored — payload lives in opaque DIB). -/
instance dibArtifactSemanticsArtifact : DIBArtifactSemantics Artifact where
  nextState := fun _ s => artifactSemanticStep s

theorem dib_semantic_step_admissible (a : Artifact) (s : ThermodynamicState) :
    Admissible s (interpretArtifact a s) := by
  simp only [interpretArtifact, DIBArtifactSemantics.nextState]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- mass: Δρ = 0
    simp [artifactSemanticStep, δMass, sub_self, abs_zero]
    rw [δMass]
    norm_num
  · simp [artifactSemanticStep]; linarith
  · simp [artifactSemanticStep]; exact le_refl _
  · simp [artifactSemanticStep]; exact le_refl _

/-- Boolean gate for “initial thermo state → state after artefact interpretation”. -/
def dibArtifactGateCheck (a : Artifact) (s : ThermodynamicState) : Bool :=
  gateCheck s (interpretArtifact a s)

/-- Lawful interpreter: semantic post-state always passes `gateCheck`
    (`gateCheckComplete` ∘ `dib_semantic_step_admissible`). -/
theorem dibArtifactGateCheck_eq_true (a : Artifact) (s : ThermodynamicState) :
    dibArtifactGateCheck a s = true :=
  gateCheckComplete _ _ (dib_semantic_step_admissible a s)

end UMST
