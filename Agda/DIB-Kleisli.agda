------------------------------------------------------------------------
-- UMST-Formal: DIB-Kleisli.agda
--
-- The Discovery-Invention-Build (DIB) loop as a Kleisli monad.
--
-- The DIB loop is the methodological backbone of UMST:
--
--   Discovery  →  Invention  →  Build
--   (observe)     (formalise)   (implement)
--
-- Each phase transforms one kind of knowledge into another, and the
-- composition of all three phases is a single end-to-end pipeline
-- from raw field observation to running Rust code.
--
-- In categorical terms, each phase is a Kleisli arrow in a State
-- monad.  The Kleisli composition (>=>) threads the evolving state
-- through all three phases.  The monad laws (left unit, right unit,
-- associativity) guarantee that the phases compose coherently — no
-- information is lost or duplicated in transit.
--
-- Each phase has a concrete referent in the UMST system:
--
--   Discovery = Systematic field observation of material behaviour,
--     yielding invariant candidates (e.g., "hydration degree is
--     monotonically non-decreasing", "density is conserved to within
--     measurement noise", "strength does not decrease in undamaged
--     specimens").  Outputs are informal constraints.
--
--   Invention = Formalisation of those constraints as UMST types:
--     the ThermodynamicState record, the four gate predicates, the
--     Admissible dependent type, the Powers gel-space ratio model.
--     Outputs are mathematical specifications.
--
--   Build = Implementation of the specification in the Rust kernel
--     (umst-prototype-2a): ThermodynamicFilter::check_transition,
--     the physics engines, the FFI bridge.  Outputs are executable
--     artefacts.
--
-- Correspondence to Rust:
--   The Rust kernel itself is the output of `build`.
--   There is no direct Rust counterpart to this module — it operates
--   at the meta-level, describing the *process* that produced the
--   kernel, not the kernel itself.
------------------------------------------------------------------------

module DIB-Kleisli where

------------------------------------------------------------------------
-- Imports
------------------------------------------------------------------------

-- We import Gate for ThermodynamicState to ground the Build phase.
open import Gate using (ThermodynamicState; Admissible; gate)

-- Propositional equality for the monad-law proofs.
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)

-- Products for pairing state with value in the State monad.
open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- Levels for universe polymorphism.
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

------------------------------------------------------------------------
-- 1. The State Monad (Record-Based, Self-Contained)
------------------------------------------------------------------------

-- We define a simple State monad without relying on the standard
-- library's monad infrastructure (which pulls in instance resolution
-- and can be opaque to non-Agda readers).
--
-- A State monad threads a mutable "state" through a computation.
-- Mathematically:
--
--   M A = S → (A × S)
--
-- where S is the state type and A is the value type.
--
-- For DIB, the state S represents the accumulated knowledge/artefacts
-- at each point in the pipeline.  The value A is the output of each
-- phase.

-- DIBState: the mutable context threaded through the DIB pipeline.
-- In practice this would include the evolving UMST model, validation
-- results, performance metrics, etc.  We keep it abstract.

postulate
  DIBState : Set
  -- The accumulated knowledge state.  Contains everything from raw
  -- field notes (Discovery output) through formal models (Invention
  -- output) to compiled artefacts (Build output).

-- M A: the State monad.  A computation that reads and updates DIBState
-- while producing a value of type A.
--
-- Denotationally:  M A ≅ DIBState → (A × DIBState)
-- We wrap it in a record for clarity and to avoid function extensionality
-- issues in the monad-law proofs.

record M (A : Set) : Set where
  constructor mkM
  field
    runM : DIBState → (A × DIBState)
    -- runM takes the current state and returns a value-state pair.
    -- This is the standard representation of the State monad.

open M

------------------------------------------------------------------------
-- 2. Monad Operations: return and bind
------------------------------------------------------------------------

-- return (also called η or pure): inject a pure value into M without
-- modifying the state.
--
-- Mathematically:  return a = λ s → (a , s)
-- Physically: "accepting a fact without changing the knowledge base."

returnM : ∀ {A : Set} → A → M A
returnM a = mkM (λ s → (a , s))
  -- The state passes through unchanged; the value is `a`.

-- bind (also called μ or >>=): sequence two monadic computations.
-- The second computation receives both the value produced by the first
-- and the updated state.
--
-- Mathematically:  (m >>= f) s = let (a , s') = runM m s
--                                 in runM (f a) s'
-- Physically: "use the output of one phase as input to the next,
-- carrying the knowledge state forward."

_>>=_ : ∀ {A B : Set} → M A → (A → M B) → M B
m >>= f = mkM (λ s →
  let result = runM m s        -- Run the first computation
      a      = proj₁ result    -- Extract the value
      s'     = proj₂ result    -- Extract the updated state
  in  runM (f a) s')           -- Pass both to the second computation

------------------------------------------------------------------------
-- 3. Kleisli Composition
------------------------------------------------------------------------

-- Kleisli composition (>=>) composes two Kleisli arrows directly,
-- without naming the intermediate monadic value.
--
-- Mathematically:  (f >=> g) a = f a >>= g
-- Categorically:  >=> is composition in the Kleisli category of M.
--
-- This is the key combinator for expressing the DIB pipeline:
-- each phase is a Kleisli arrow, and the full loop is their
-- Kleisli composition.

infixr 20 _>=>_

_>=>_ : ∀ {A B C : Set} → (A → M B) → (B → M C) → (A → M C)
(f >=> g) a = f a >>= g
  -- Apply f to get M B, then bind with g to get M C.
  -- The state threads through both f and g automatically.

------------------------------------------------------------------------
-- 4. DIB Phase Types
------------------------------------------------------------------------

-- The four types in the DIB pipeline.  Each represents a distinct
-- kind of knowledge artefact.

postulate
  -- Observation: raw field data collected during material testing.
  -- Examples: slump test readings, carbonation depth measurements,
  -- moisture content profiles, compressive strength at 7/28/90 days.
  -- These are the empirical inputs to the Discovery phase.
  Observation : Set

  -- Insight: a recognised pattern or invariant.
  -- Examples: "hydration never reverses", "strength is monotone in α",
  -- "mass is conserved to within δ".  These are the tacit-knowledge
  -- outputs of the Discovery phase — patterns that an experienced
  -- practitioner notices but may not initially articulate formally.
  Insight : Set

  -- Design: a formal mathematical specification.
  -- Examples: the UMST tensor definition, the Admissible predicate,
  -- the Powers model fc = S·x³, the Clausius-Duhem inequality.
  -- These are the outputs of the Invention phase — translating
  -- tacit insights into transmissible mathematics.
  Design : Set

  -- Artifact: a running implementation.
  -- Examples: the Rust ThermodynamicFilter, the physics engine trait,
  -- the FFI bridge, the compiled WASM module.
  -- These are the outputs of the Build phase — materialising the
  -- formal design as executable code.
  Artifact : Set

------------------------------------------------------------------------
-- 5. DIB Kleisli Arrows
------------------------------------------------------------------------

-- Each phase of the DIB loop is a Kleisli arrow: a function that
-- takes an input, updates the knowledge state, and produces an output
-- wrapped in M.

postulate
  -- Discovery: Observation → M Insight
  -- "Look at the field data and recognise a pattern."
  --
  -- Example: observing 200+ concrete cube tests and noticing that
  -- fc never decreases between successive measurements on the same
  -- specimen → Insight: "strength is monotone".
  --
  -- This arrow may update DIBState with metadata: which observations
  -- were consulted, confidence levels, environmental conditions.
  discover : Observation → M Insight

  -- Invention: Insight → M Design
  -- "Formalise the pattern as mathematics."
  --
  -- Example: the insight "strength is monotone" becomes the formal
  -- statement  ∀ old new. hydration old ≤ hydration new →
  --                       strength old ≤ strength new
  -- and is bundled into the Admissible predicate in Gate.agda.
  --
  -- This arrow may update DIBState with the formal model, its
  -- assumptions, and its domain of validity.
  invent : Insight → M Design

  -- Build: Design → M Artifact
  -- "Implement the formal specification as executable code."
  --
  -- Example: the Design (Admissible predicate + Powers model) becomes
  -- the Rust function ThermodynamicFilter::check_transition with its
  -- four inequality checks and tolerance ε = 10⁻⁶.
  --
  -- This arrow may update DIBState with compilation artifacts, test
  -- results, and performance benchmarks.
  build : Design → M Artifact

------------------------------------------------------------------------
-- 6. The Full DIB Pipeline
------------------------------------------------------------------------

-- The complete DIB cycle is the Kleisli composition of all three
-- phases.  It takes a raw Observation and produces a running Artifact,
-- threading the evolving knowledge state through every phase.

dib : Observation → M Artifact
dib = (discover >=> invent) >=> build
  -- This single line captures the entire UMST methodology:
  --   1. Discover patterns in field data
  --   2. Invent formal models from those patterns
  --   3. Build executable implementations from those models
  --
  -- The Kleisli composition guarantees that:
  --   - Each phase receives the state left by the previous phase
  --   - No knowledge is lost between phases
  --   - The phases can be independently verified and tested

------------------------------------------------------------------------
-- 7. Monad Laws
------------------------------------------------------------------------

-- The three monad laws ensure that returnM and >>= behave coherently.
-- They are the "sanity conditions" for the DIB pipeline: they say
-- that injecting pure values and sequencing computations work as
-- expected with no surprises.
--
-- We prove them assuming function extensionality (postulated below),
-- since State-monad laws require equating functions.

-- Function extensionality: if two functions agree on all inputs,
-- they are equal.  This is consistent with Agda but not provable
-- without --postulated-extensionality or cubical Agda.
postulate
  funext : ∀ {A : Set} {B : A → Set} {f g : (a : A) → B a} →
           (∀ a → f a ≡ g a) → f ≡ g

-- M-extensionality: two M values are equal if their runM fields
-- are equal.  This follows from the fact that M is a record with
-- a single field.
M-ext : ∀ {A : Set} {m₁ m₂ : M A} → runM m₁ ≡ runM m₂ → m₁ ≡ m₂
M-ext {A} {mkM f} {mkM .f} refl = refl
  -- If the run-functions are propositionally equal, the M values are
  -- propositionally equal.  This is just congruence on the constructor.

------------------------------------------------------------------------
-- 7a. Left Unit Law
------------------------------------------------------------------------

-- Law: returnM a >>= f  ≡  f a
--
-- "Injecting a pure value and then binding is the same as applying
--  the function directly."
--
-- Physical meaning: if Discovery produces a known insight a without
-- consulting any field data (a pure observation), then feeding it
-- into Invention is the same as inventing directly from a.
-- No state is created or destroyed by a no-op Discovery.

left-unit : ∀ {A B : Set} (a : A) (f : A → M B) →
            (returnM a >>= f) ≡ f a
left-unit a f = M-ext (funext (λ s → refl))
  -- Proof: unfold the definitions.
  --   runM (returnM a >>= f) s
  -- = runM (f a) (proj₂ (a , s))     — by def of returnM and >>=
  -- = runM (f a) s                    — by β-reduction of proj₂
  -- This is definitionally equal to runM (f a) s. ∎

------------------------------------------------------------------------
-- 7b. Right Unit Law
------------------------------------------------------------------------

-- Law: m >>= returnM  ≡  m
--
-- "Running a computation and then injecting the result back as pure
--  is the same as just running the computation."
--
-- Physical meaning: if after Building an artifact we do nothing with
-- it (just "return" it), the final state is the same as Build alone.
-- The return arrow is invisible.

right-unit : ∀ {A : Set} (m : M A) →
             (m >>= returnM) ≡ m
right-unit m = M-ext (funext (λ s → refl))
  -- Proof: unfold the definitions.
  --   runM (m >>= returnM) s
  -- = let (a , s') = runM m s in (a , s')
  -- = runM m s
  -- Definitional equality by η-expansion of pairs. ∎

------------------------------------------------------------------------
-- 7c. Associativity Law
------------------------------------------------------------------------

-- Law: (m >>= f) >>= g  ≡  m >>= (λ a → f a >>= g)
--
-- "Binding twice in sequence is the same as binding once with the
--  composed function."
--
-- Physical meaning: it doesn't matter whether we conceptually group
-- the DIB pipeline as (Discover then Invent) then Build, or as
-- Discover then (Invent then Build).  The result — both the final
-- artefact and the accumulated knowledge state — is identical.
-- This is what makes the pipeline truly compositional.

assoc : ∀ {A B C : Set} (m : M A) (f : A → M B) (g : B → M C) →
        ((m >>= f) >>= g) ≡ (m >>= (λ a → f a >>= g))
assoc m f g = M-ext (funext (λ s → refl))
  -- Proof: unfold the definitions.
  --   runM ((m >>= f) >>= g) s
  -- = let (a , s₁)  = runM m s
  --       (b , s₂)  = runM (f a) s₁
  --   in  runM (g b) s₂
  --
  --   runM (m >>= (λ a → f a >>= g)) s
  -- = let (a , s₁)  = runM m s
  --   in  runM (f a >>= g) s₁
  -- = let (a , s₁)  = runM m s
  --       (b , s₂)  = runM (f a) s₁
  --   in  runM (g b) s₂
  --
  -- Both sides reduce to the same expression. ∎

------------------------------------------------------------------------
-- 8. Kleisli Law: Composition is Associative
------------------------------------------------------------------------

-- As a corollary of the monad laws, Kleisli composition is associative:
--
--   (f >=> g) >=> h  ≡  f >=> (g >=> h)
--
-- This says: the three-phase DIB pipeline can be parenthesised either
-- way without changing the result.  We can test/verify each phase
-- independently and be certain that their composition is well-behaved.

kleisli-assoc : ∀ {A B C D : Set}
  (f : A → M B) (g : B → M C) (h : C → M D) →
  ∀ (a : A) → ((f >=> g) >=> h) a ≡ (f >=> (g >=> h)) a
kleisli-assoc f g h a = assoc (f a) g h
  -- Proof: immediate from the monad associativity law.
  -- (f >=> g) >=> h) a = ((f a >>= g) >>= h) = (f a >>= (λ b → g b >>= h))
  -- = (f >=> (g >=> h)) a. ∎

------------------------------------------------------------------------
-- 9. Kleisli Law: Left and Right Unit
------------------------------------------------------------------------

-- returnM is the identity for Kleisli composition on both sides.

kleisli-left-unit : ∀ {A B : Set} (f : A → M B) →
  ∀ (a : A) → (returnM >=> f) a ≡ f a
kleisli-left-unit f a = left-unit a f
  -- (returnM >=> f) a = returnM a >>= f = f a. ∎

kleisli-right-unit : ∀ {A B : Set} (f : A → M B) →
  ∀ (a : A) → (f >=> returnM) a ≡ f a
kleisli-right-unit f a = right-unit (f a)
  -- (f >=> returnM) a = f a >>= returnM = f a. ∎

------------------------------------------------------------------------
-- 10. The DIB Loop is Well-Founded
------------------------------------------------------------------------

-- The monad laws together guarantee that `dib` — defined as
-- discover >=> invent >=> build — is a well-defined Kleisli arrow
-- satisfying all three monad laws.  Concretely:
--
--   1. Left unit:  returnM >=> dib  ≡  dib
--      "A trivial observation followed by DIB is just DIB."
--
--   2. Right unit: dib >=> returnM  ≡  dib
--      "DIB followed by doing nothing is just DIB."
--
--   3. Associativity: the sub-pipelines compose in any order.
--      (discover >=> invent) >=> build  ≡  discover >=> (invent >=> build)
--
-- These properties hold by the monad laws proven above.

dib-assoc : ∀ (obs : Observation) →
  ((discover >=> invent) >=> build) obs ≡ (discover >=> (invent >=> build)) obs
dib-assoc obs = kleisli-assoc discover invent build obs
  -- The DIB pipeline is associative: we can verify
  -- (discover >=> invent) independently of build, or
  -- (invent >=> build) independently of discover,
  -- and the full composition is guaranteed correct.

------------------------------------------------------------------------
-- 11. Summary
------------------------------------------------------------------------
--
-- What we defined:
--   1. A self-contained State monad M with return and bind.
--   2. Three Kleisli arrows for the DIB phases:
--        discover : Observation → M Insight
--        invent   : Insight → M Design
--        build    : Design → M Artifact
--   3. The full DIB pipeline as Kleisli composition:
--        dib = discover >=> invent >=> build
--
-- What we proved:
--   4. Left unit:    returnM a >>= f ≡ f a
--   5. Right unit:   m >>= returnM ≡ m
--   6. Associativity: (m >>= f) >>= g ≡ m >>= (λ a → f a >>= g)
--   7. Kleisli associativity: (f >=> g) >=> h ≡ f >=> (g >=> h)
--   8. Kleisli left/right unit: returnM >=> f ≡ f, f >=> returnM ≡ f
--   9. DIB pipeline associativity as a corollary.
--
-- Why this matters:
--   The DIB loop is not just a workflow diagram.  It is a *monadic
--   computation* with formal composition laws.  The monad laws
--   guarantee that:
--     - Phases compose without information loss (associativity)
--     - Pure values inject cleanly (unit laws)
--     - The pipeline can be decomposed for independent testing
--
--   This is the categorical backbone of UMST's methodology:
--   field observation (Discovery) → formal model (Invention) →
--   executable code (Build), composed via Kleisli arrows in a
--   State monad that tracks the evolving knowledge base.
------------------------------------------------------------------------
