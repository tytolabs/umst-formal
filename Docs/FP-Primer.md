# Functional Programming and Category Theory: Concepts in UMST-Formal

This document explains the functional programming and category theory concepts used
in this repository. It is written for practitioners in architecture, materials science,
and engineering who are reading the formal proofs for the first time. No prior
programming or mathematics background is assumed beyond familiarity with functions in
the sense of a recipe: given fixed inputs, you always get the same output.

The concepts are presented in dependency order: each one builds directly on those
before it. The final section shows how they compose to form the UMST-Formal system.

---

## Concept Dependency Map

```
Function
  └── Higher-Order Function
        └── Type
              └── Higher-Order Type (Kind)
                    └── Recursion
                          └── Category
                                ├── Functor
                                │     └── Endofunctor
                                │           ├── Monad
                                │           │     ├── Kleisli Category
                                │           │     ├── Monad Transformer
                                │           │     ├── Free Monad
                                │           │     └── (uses) Monoid
                                │           └── Comonad
                                ├── Natural Transformation
                                │     ├── Applicative Functor
                                │     └── Adjunction
                                └── 2-Category (enriches the whole map)
```

---

## 1. Function

**Definition.** A function is a pure, reliable mapping that takes one or more inputs
and always produces exactly one output according to a fixed rule, with no hidden
changes to the world around it. Every time you supply the same inputs, you get the
same result.

**Precisely.** A function \(f: A \to B\) assigns to each element \(x \in A\) (the
domain) exactly one element \(f(x) \in B\) (the codomain). It is *referentially
transparent*: replacing a call \(f(x)\) with its result never changes the behaviour
of any surrounding computation.

**In this repository.** Every computation in `Haskell/UMST.hs` is a pure function.
`gateCheck`, `psiDot`, `massConserved`, and `fromMix` are all pure: given the same
`ThermodynamicState` inputs, they always return the same result, with no file access,
no random numbers, and no global variables. This is what makes property-based testing
valid — you can call them thousands of times and trust that the results are consistent.

```haskell
-- From Haskell/UMST.hs
gateCheck :: ThermodynamicState -> ThermodynamicState -> AdmissibilityResult
```

---

## 2. Higher-Order Function

**Definition.** A higher-order function is a function that treats other functions as
ordinary values: it can accept a function as an argument, return a function as its
result, or do both.

**Precisely.** If \(A \to B\) denotes a function space (the set of all functions from
\(A\) to \(B\)), a higher-order function operates at the level of these spaces:
\((A \to B) \to (C \to D)\), for example, takes a function and returns a different
function.

**In this repository.** The QuickCheck property tests in `Haskell/Props.hs` pass
functions as arguments to `forAll` and `property` — both higher-order functions.
The Kleisli composition operator `>=>` in `Haskell/KleisliDIB.hs` takes two
functions and returns a third: `(a -> m b) -> (b -> m c) -> (a -> m c)`. The entire
DIB pipeline is assembled this way without naming intermediate results.

```haskell
-- Kleisli composition from KleisliDIB.hs
dibCycle = discover >=> invent >=> build
```

---

## 3. Type

**Definition.** A type is a precise label that describes exactly which values are
allowed and which operations make sense for a piece of data. It acts as a contract
the program must satisfy, catching category errors at compile time rather than at
runtime.

**Precisely.** In type theory, a type is a collection of values sharing the same
structure and permitted operations. In category theory, types are the *objects* of
the relevant category — the things being connected by functions (morphisms).

**In this repository.** The central type is `ThermodynamicState`, which records
the thermodynamic condition of a material specimen at a single instant: density,
free energy, hydration degree, and compressive strength. The type system ensures
that the gate can only compare two states of the same structure — you cannot
accidentally pass a mix proportion where a state is expected.

```haskell
-- From Haskell/UMST.hs
data ThermodynamicState = ThermodynamicState
  { density     :: Double   -- kg/m³
  , freeEnergy  :: Double   -- J/kg   (Helmholtz ψ)
  , hydration   :: Double   -- [0,1]  (degree α)
  , strength    :: Double   -- MPa    (compressive fc)
  }
```

The same type is defined, with identical fields, in Agda (`Agda/Gate.agda`) and Coq
(`Coq/Gate.v`), giving three independent formal representations of the same physical
object.

---

## 4. Higher-Order Type (Kind)

**Definition.** A higher-order type, also called a type constructor, is a template
for creating new types: it takes one or more ordinary types as parameters and
produces a new type that carries additional structure.

**Precisely.** Types themselves have a classification called a *kind*. The kind `*`
(read "star") denotes a concrete type that can hold values. A type constructor has
kind `* -> *`: it takes a concrete type and produces another concrete type.
In Agda and Coq, this is expressed with universe levels.

**In this repository.** `Maybe ThermodynamicState` is a higher-order type: `Maybe`
is the template, `ThermodynamicState` is the parameter, and the result is a type
that means "possibly a state, or nothing." The `StateT` monad transformer in
`Haskell/KleisliDIB.hs` is also a type constructor — it adds mutable state to
any existing monad.

```haskell
-- StateT wraps IO with mutable UMSTState
type DIBM a = StateT UMSTState IO a
```

---

## 5. Recursion

**Definition.** Recursion is the technique of defining a function in terms of itself:
solve a problem by breaking it into smaller instances of the same problem, delegating
each to the same function, and combining the results once the smallest instance (the
base case) is reached.

**Precisely.** In functional programming, recursion replaces iteration because there
is no mutable loop counter. Each recursive call operates on its own local variables,
which is safe and provably correct when the inputs strictly decrease toward the base
case. Many proofs in this repository use *structural recursion* — recursion on the
shape of a data type — which Agda and Coq can verify terminates automatically.

**In this repository.** The Agda monad-law proofs in `Agda/DIB-Kleisli.agda` use
structural recursion on the `DIBState`. The QuickCheck arbitrary generators in
`Haskell/Props.hs` use recursion to generate lists of test states. The Coq extraction
of `gate_check` (`Coq/Gate.v`) uses a boolean conjunction pattern that compiles
to a recursive match over the invariant fields.

---

## 6. Category

**Definition.** A category is a mathematical framework for composable structure: a
collection of objects connected by arrows (morphisms), with a rule for chaining arrows
and a do-nothing arrow for every object. The chaining rule must be associative, and
the do-nothing arrows must leave every arrow unchanged.

**Precisely.** A category \(\mathcal{C}\) consists of:

- **Objects**: the things being connected (types, sets, spaces, etc.)
- **Morphisms**: arrows \(f: A \to B\) between objects
- **Composition**: given \(f: A \to B\) and \(g: B \to C\), their composite
  \(g \circ f: A \to C\) exists and is unique
- **Identity**: for every object \(A\), an arrow \(\mathrm{id}_A: A \to A\)

Axioms:
1. Associativity: \(h \circ (g \circ f) = (h \circ g) \circ f\)
2. Unit: \(f \circ \mathrm{id}_A = \mathrm{id}_B \circ f = f\)

**In this repository.** The category **Hask** — Haskell types as objects, pure
functions as morphisms, `.` as composition, `id` as identity — is the ambient
category for all Haskell code in `Haskell/UMST.hs` and `Haskell/KleisliDIB.hs`.
The formal justification that `gateCheck` composes correctly with other gate
predicates depends on these categorical laws. `Agda/Naturality.agda` proves that
the gate is a morphism in the subcategory of admissible transitions.

---

## 7. Functor

**Definition.** A functor is a structure-preserving map between two categories: it
sends objects to objects and morphisms to morphisms, in a way that respects
composition and identity.

**Precisely.** A functor \(F: \mathcal{C} \to \mathcal{D}\) must satisfy:

- \(F(\mathrm{id}_A) = \mathrm{id}_{F(A)}\) (identity is preserved)
- \(F(g \circ f) = F(g) \circ F(f)\) (composition is preserved)

In Haskell, all functors are endofunctors on **Hask** (see §8), expressed as the
`Functor` typeclass with `fmap`:

```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b
```

Laws: `fmap id = id` and `fmap (f . g) = fmap f . fmap g`.

**In this repository.** `Agda/Naturality.agda` defines two functors `F` and `G` on
the discrete category `MaterialClass` (one per binder family: OPC, lime, earth,
geopolymer, RAC). The central theorem proves that the gate forms a natural
transformation between them — which requires first establishing that `F` and `G`
are well-defined functors.

---

## 8. Endofunctor

**Definition.** An endofunctor is a functor from a category to itself. In functional
programming, since all types live in the same category (**Hask**), every `Functor`
instance is automatically an endofunctor.

**Precisely.** \(F: \mathcal{C} \to \mathcal{C}\). The significance is that an
endofunctor can be applied repeatedly — \(F(F(A))\), \(F(F(F(A)))\), and so on —
all within the same category. This self-application is what makes monads possible.

**In this repository.** `StateT UMSTState IO` in `KleisliDIB.hs` is an endofunctor
on **Hask**. Applying it twice gives `StateT UMSTState IO (StateT UMSTState IO a)`,
which `join` (the monad's flattening operation) collapses back to
`StateT UMSTState IO a` — all still in **Hask**.

---

## 9. Monoid

**Definition.** A monoid is an algebraic structure consisting of a set of values, an
associative binary operation for combining any two of them, and an identity element
that leaves any value unchanged when combined with it.

**Precisely.** A monoid \((M, \oplus, e)\) satisfies:

- Associativity: \((x \oplus y) \oplus z = x \oplus (y \oplus z)\)
- Left unit: \(e \oplus x = x\)
- Right unit: \(x \oplus e = x\)

Standard examples: natural numbers under addition (identity: 0), lists under
concatenation (identity: `[]`).

**In this repository.** The relevance of monoids is primarily structural: the monad
(§10) is precisely a *monoid object* inside the category of endofunctors. More
concretely, the `All` predicate used in the Haskell test suite is a monoid — all
four gate invariants must hold simultaneously, and `All` combines boolean properties
with `&&` (associative, identity `True`). The DIB state accumulates knowledge
monoidal under sequential composition.

---

## 10. Monad

**Definition.** A monad is an endofunctor equipped with two operations — one that
wraps a plain value into the context, and one that flattens nested contexts into a
single layer — satisfying laws that make the whole structure behave exactly like
a monoid. The result is a principled way to chain computations that carry extra
context (possibility, mutable state, I/O) while remaining fully composable.

**Precisely.** A monad is a triple \((T, \eta, \mu)\) where:

- \(T: \mathcal{C} \to \mathcal{C}\) is an endofunctor
- \(\eta: \mathrm{Id} \Rightarrow T\) is the *unit* (also called `return` or `pure`)
- \(\mu: T \circ T \Rightarrow T\) is the *multiplication* (also called `join`)

Laws (the monad is a monoid in the monoidal category of endofunctors under \(\circ\)):

\[
\mu \circ T\mu = \mu \circ \mu T \quad \text{(associativity)}
\]
\[
\mu \circ T\eta = \mu \circ \eta T = \mathrm{id}_T \quad \text{(unit laws)}
\]

In Haskell:

```haskell
class Functor m => Monad m where
  return :: a -> m a          -- η: pure injection
  (>>=)  :: m a -> (a -> m b) -> m b  -- bind, derived from join + fmap
```

**In this repository.** `Agda/DIB-Kleisli.agda` defines a State monad `M` from
scratch (without importing a library), proves the three monad laws (left unit, right
unit, associativity) as theorems, and uses it to represent the DIB pipeline.
`Haskell/KleisliDIB.hs` uses `StateT UMSTState IO` — the standard library monad
transformer that combines mutable state with I/O — for the same purpose.

```agda
-- From Agda/DIB-Kleisli.agda
record M (A : Set) : Set where
  field runM : DIBState → (A × DIBState)
```

---

## 11. Natural Transformation

**Definition.** A natural transformation is a way to convert between two different
functors while respecting the structure they both preserve. It provides one
conversion function per object, and those conversion functions must commute with
any morphism lifted by either functor.

**Precisely.** Given functors \(F, G: \mathcal{C} \to \mathcal{D}\), a natural
transformation \(\eta: F \Rightarrow G\) assigns to each object \(A \in \mathcal{C}\)
a morphism \(\eta_A: F(A) \to G(A)\) in \(\mathcal{D}\), such that for every
morphism \(f: A \to B\) in \(\mathcal{C}\):

\[
G(f) \circ \eta_A = \eta_B \circ F(f) \quad \text{(naturality square commutes)}
\]

**In this repository.** `Agda/Naturality.agda` is entirely about one natural
transformation: the thermodynamic gate viewed as \(\eta: F \Rightarrow G\) on the
discrete category `MaterialClass`. The central theorem `gate-natural` proves that
the naturality square commutes — equivalently, that applying the gate before or
after translating between material classes gives the same result. This is the
formal statement that the gate is material-agnostic.

The monad's `return` and `join` operations are also natural transformations (§10),
which is why the monad laws take the form they do.

---

## 12. Kleisli Category

**Definition.** Given a monad \(M\), the Kleisli category \(\mathcal{K}(M)\) is a
category whose morphisms are *monadic functions* of the form \(a \to M\, b\) —
functions that produce a monadic context rather than a plain value. The composition
rule for these morphisms is provided by bind (`>>=`).

**Precisely.** For a monad \(T\) on \(\mathcal{C}\), the Kleisli category
\(\mathcal{C}_T\) has:

- The same objects as \(\mathcal{C}\)
- A morphism \(A \to B\) in \(\mathcal{C}_T\) is a morphism \(A \to T\,B\) in
  \(\mathcal{C}\)
- Kleisli composition: given \(f: A \to T\,B\) and \(g: B \to T\,C\),
  \[g \circ_T f = \mu \circ T g \circ f\]
  where \(\mu: T \circ T \Rightarrow T\) is the monad multiplication. In Haskell:
  `(f >=> g) a = f a >>= g`
- Identity is the unit \(\eta\) (`return`)

The three monad laws (left unit, right unit, associativity) are precisely the proofs
that this composition is a valid category — no more, no less.

**In this repository.** `Agda/DIB-Kleisli.agda` proves the Kleisli category laws
directly: `left-unit`, `right-unit`, and `assoc` are theorem statements that
`discover`, `invent`, and `build` compose coherently as Kleisli arrows.
`Haskell/KleisliDIB.hs` uses the same structure operationally, with `>=>` from
`Control.Monad`.

```haskell
-- From Haskell/KleisliDIB.hs
dibCycle = discover >=> invent >=> build
```

The significance for the UMST system: the Kleisli category is the mathematical
justification that the DIB pipeline can be assembled from independently defined
phases without losing information or violating invariants at the seams.

---

## 13. Applicative Functor

**Definition.** An applicative functor sits between a plain functor (§7) and a full
monad (§10): it allows independent contextual values to be combined using ordinary
functions, without requiring the full sequential dependency that bind (`>>=`) imposes.

**Precisely.** An applicative functor \(F\) extends `Functor` with:

```haskell
class Functor f => Applicative f where
  pure  :: a -> f a                        -- embed a value
  (<*>) :: f (a -> b) -> f a -> f b        -- apply a lifted function
```

Laws: identity, composition, homomorphism, interchange — all weaker than monad laws.

**In this repository.** The QuickCheck generators in `Haskell/Props.hs` use
`Applicative` to construct random `ThermodynamicState` values from independent
random field values (`density`, `freeEnergy`, `hydration`, `strength`), since the
four fields are independent. This is the appropriate abstraction: the fields do not
depend on each other during generation, so monad is unnecessary and functor alone
is insufficient.

---

## 14. Monad Transformer

**Definition.** A monad transformer is a modular way to combine multiple monads into
one. It takes an existing monad and adds one layer of effect on top — mutable state,
error handling, logging, and so on — producing a new monad that inherits the
capabilities of both while satisfying all monad laws.

**Precisely.** A monad transformer is a functor \(t\) from monads to monads: given
any monad \(m\), the result \(t\,m\) is again a monad. It comes with a natural
operation

\[\mathrm{lift}: m\,a \to t\,m\,a\]

that injects computations from the inner monad into the combined monad without losing
their effects. In Haskell:

```haskell
class MonadTrans t where
  lift :: Monad m => m a -> t m a
```

Transformers stack: `StateT s (ExceptT e m)` is a monad that combines mutable state
(type `s`), error handling (error type `e`), and whatever effects `m` provides.

**In this repository.** The DIB pipeline in `Haskell/KleisliDIB.hs` uses
`StateT UMSTState IO` — the State transformer applied to the `IO` monad. This gives
the pipeline access to mutable material state (`UMSTState`) and I/O (sensor reads,
FFI calls, logging) simultaneously. The `lift` operation promotes plain `IO` actions
(e.g., calling the Rust kernel via FFI) into the combined monad without rewriting
them.

```haskell
-- From Haskell/KleisliDIB.hs
type DIBM a = StateT UMSTState IO a

-- FFI call promoted into the combined monad
callRustGate :: ThermodynamicState -> ThermodynamicState -> DIBM Bool
callRustGate old new = lift $ ffiGateCheck old new
```

---

## 15. 2-Category

**Definition.** A 2-category extends an ordinary category by adding a second layer of
morphisms: arrows between arrows. It has objects (0-cells), morphisms between objects
(1-cells), and morphisms between parallel 1-cells (2-cells), with two independent
composition rules for 2-cells — vertical and horizontal — satisfying an interchange
law.

**Precisely.** A 2-category \(\mathcal{K}\) consists of:

- **0-cells**: objects \(A, B, C, \ldots\)
- **1-cells**: morphisms \(f: A \to B\)
- **2-cells**: morphisms \(\alpha: f \Rightarrow g\) between parallel 1-cells
  \(f, g: A \to B\)
- **Vertical composition** \(\circ_1\): stacking 2-cells sharing a 1-cell boundary
- **Horizontal composition** \(\bullet\): composing 2-cells side by side

The interchange law must hold:

\[(\beta \circ_1 \alpha) \bullet (\delta \circ_1 \gamma) = (\beta \bullet \delta) \circ_1 (\alpha \bullet \gamma)\]

The canonical example is **Cat**: 0-cells are (small) categories, 1-cells are
functors, 2-cells are natural transformations. Vertical composition is natural
transformation composition; horizontal composition is Godement product (whiskering).

**In this repository.** The UMST-Formal system is itself a 2-categorical structure.
The three formal layers (Agda, Coq, Haskell) are 0-cells. The type correspondences
between layers (e.g., `ThermodynamicState` in Agda ↔ `thermo_state` in Coq) are
1-cells. The proofs that those correspondences commute with the gate (e.g., that the
Haskell `gateCheck` agrees with the Agda `gate` on all inputs) are 2-cells. The
synthesis table in `Docs/Architecture-Invariants.md` is a presentation of this
2-categorical structure in tabular form. The 2-categorical perspective also makes
precise why the three layers are redundant by design: they are three different
presentations of the same 2-categorical object, and agreement between them is a
2-cell — a natural transformation — not merely an informal claim.

---

## 16. Adjunction

**Definition.** An adjunction is a relationship between two functors going in
opposite directions — one a left adjoint, one a right adjoint — that are not
inverses of each other but are connected by a unit and counit satisfying
triangle identities. Adjunctions generate many standard constructions in
functional programming, including currying and the State monad.

**Precisely.** An adjunction \(F \dashv G\) between \(F: \mathcal{C} \to \mathcal{D}\)
(left adjoint) and \(G: \mathcal{D} \to \mathcal{C}\) (right adjoint) consists of
natural transformations

\[\eta: \mathrm{Id}_{\mathcal{C}} \Rightarrow G \circ F \qquad (\text{unit})\]
\[\varepsilon: F \circ G \Rightarrow \mathrm{Id}_{\mathcal{D}} \qquad (\text{counit})\]

satisfying the triangle identities:

\[\varepsilon F \circ F\eta = \mathrm{id}_F, \qquad G\varepsilon \circ \eta G = \mathrm{id}_G\]

Equivalently: \(\mathrm{Hom}_{\mathcal{D}}(F\,A, B) \cong \mathrm{Hom}_{\mathcal{C}}(A, G\,B)\)
naturally in \(A\) and \(B\).

The standard example is the **currying adjunction**: the product functor
\((- \times S)\) is left adjoint to the function-space functor \((S \to -)\),
giving the natural bijection

\[\mathrm{Hom}(A \times S, B) \cong \mathrm{Hom}(A, S \to B)\]

This is precisely what Haskell's `curry` and `uncurry` implement. The **State monad**
\(T\,A = S \to (A \times S)\) is the monad induced by this adjunction: composing
\((- \times S)\) with \((S \to -)\) gives \(T = G \circ F\), and the monad's unit
and multiplication are the adjunction's unit and the counit composed with the functor.

**In this repository.** `StateT UMSTState IO` in `Haskell/KleisliDIB.hs` is the
practical realisation of the adjunction-induced State monad. Understanding the
adjunction makes clear why the transformer has the structure it does — and in
particular why `runStateT :: StateT s m a -> s -> m (a, s)` is the natural unwrapping:
it is precisely the adjunction's hom-set isomorphism evaluated at the monad type.

---

## 17. Comonad

**Definition.** A comonad is the categorical dual of a monad. Where a monad wraps
values into a context and flattens nested contexts, a comonad extracts values from
a context and extends a context with new computations. Comonads are the natural
abstraction for computations that depend on surrounding or historical data rather
than producing new context.

**Precisely.** A comonad is a triple \((W, \varepsilon, \delta)\) where:

- \(W: \mathcal{C} \to \mathcal{C}\) is an endofunctor
- \(\varepsilon: W \Rightarrow \mathrm{Id}\) is the *extract* (the counit)
- \(\delta: W \Rightarrow W \circ W\) is the *duplicate* (the comultiplication)

satisfying the co-associativity and counit laws — the exact duals of the monad laws:

\[W\delta \circ \delta = \delta W \circ \delta \qquad (\text{co-associativity})\]
\[W\varepsilon \circ \delta = \varepsilon W \circ \delta = \mathrm{id}_W \qquad (\text{counit laws})\]

In Haskell:

```haskell
class Functor w => Comonad w where
  extract   :: w a -> a           -- ε: extract the focused value
  duplicate :: w a -> w (w a)     -- δ: extend the context one level
  extend    :: (w a -> b) -> w a -> w b  -- derived from duplicate + fmap
```

A standard example is the **product (environment) comonad** `(e, a)`:

```haskell
extract   (e, a) = a
duplicate (e, a) = (e, (e, a))   -- environment persists into duplicate
```

Another is the **zipper comonad** on lists, where the "focused" element is the
current position and the surrounding list is the context.

**In this repository.** Comonads do not appear in the current codebase, but they are
the natural extension for spatial and temporal material analysis. A specimen is never
isolated: its thermodynamic state depends on adjacent specimens (heat flux,
moisture gradients), prior history (loading path, wetting/drying cycles), and
environmental conditions. A `W ThermodynamicState` where `W` is a spatial-context
comonad would let the gate evaluate transitions using surrounding state without
restructuring the gate's pure interface. This is a documented direction for future
work (see `CONTRIBUTING.md`).

---

## 18. Free Monad

**Definition.** A free monad is the most general monad that can be constructed from
any functor. It represents all possible sequences of operations as an explicit tree
structure — a syntax tree — without prescribing any particular interpretation.
The tree is then evaluated by supplying a separate interpreter. This separates the
description of what operations to perform from the decision of how to perform them.

**Precisely.** Given any endofunctor \(F\), the free monad \(F^*\) is the initial
monad generated by \(F\), defined as the least fixed point:

\[F^*\,a = a + F(F^*\,a)\]

The left summand (`Pure`) injects a plain value; the right (`Free`) wraps one layer
of \(F\) around a recursive tree. In Haskell:

```haskell
data Free f a = Pure a | Free (f (Free f a))
```

`Functor`, `Applicative`, and `Monad` instances follow mechanically. An interpreter
is a natural transformation \(f \Rightarrow m\) into any target monad \(m\), lifted
to \(F^* \Rightarrow m\) by the initiality of \(F^*\).

**In this repository.** The current codebase uses `StateT UMSTState IO` directly
(a concrete monad stack). The free monad alternative would define a functor

```haskell
data GateF a
  = CheckTransition ThermodynamicState ThermodynamicState (Bool -> a)
  | LogResult String a
  | Done a
```

and build `type GateM a = Free GateF a`. The DIB pipeline would then be a
`GateM` value — a pure description of operations — and interpreters would handle
Rust FFI calls, simulation, or testing differently, without changing the pipeline
code. This architecture is noted in `CONTRIBUTING.md` as a possible refactor that
would simplify the addition of new gate backends.

---

## How These Concepts Combine in UMST-Formal

The table below maps each formal concept to its concrete role in this codebase.

| Concept | Role in UMST-Formal | Primary file |
|---|---|---|
| Function | Pure gate predicate; each invariant check | `Haskell/UMST.hs` |
| Higher-order function | Kleisli composition; QuickCheck property API | `Haskell/KleisliDIB.hs`, `Props.hs` |
| Type | `ThermodynamicState`, `MaterialClass`, `Admissible` | All layers |
| Higher-order type | `StateT`, `Maybe`, monad transformer stack | `Haskell/KleisliDIB.hs` |
| Recursion | Agda monad-law proofs; QuickCheck generators | `Agda/DIB-Kleisli.agda` |
| Category | **Hask** as ambient category; admissible subcategory | Conceptual foundation |
| Functor | `F`, `G` on `MaterialClass` | `Agda/Naturality.agda` |
| Endofunctor | All `Functor` instances; `StateT UMSTState IO` | `Haskell/KleisliDIB.hs` |
| Monoid | Monoid structure on `All`; DIB state accumulation | `Haskell/Props.hs` |
| Monad | State monad for DIB pipeline; law proofs | `Agda/DIB-Kleisli.agda`, `Haskell/KleisliDIB.hs` |
| Natural transformation | Gate as `η: F ⟹ G`; material-agnosticism proof | `Agda/Naturality.agda` |
| Kleisli category | DIB phase composition; law verification | `Agda/DIB-Kleisli.agda`, `Haskell/KleisliDIB.hs` |
| Applicative functor | Independent field generation in tests | `Haskell/Props.hs` |
| Monad transformer | `StateT UMSTState IO`; combining state + IO effects | `Haskell/KleisliDIB.hs` |
| 2-Category | Three formal layers as 0-cells; correspondences as 1-cells; agreement proofs as 2-cells | `Docs/Architecture-Invariants.md` (synthesis table) |
| Adjunction | Mathematical origin of the State monad and its `runStateT` isomorphism | `Haskell/KleisliDIB.hs` (structural) |
| Comonad | Future direction: spatial / historical context for gate evaluation | `CONTRIBUTING.md` |
| Free monad | Future direction: gate effect algebra separating description from interpretation | `CONTRIBUTING.md` |

### The central result in one sentence

The thermodynamic gate is a natural transformation in the Kleisli category of a
State monad — which means: it composes correctly across phases, works uniformly
across material classes, and preserves the four physical invariants under any
admissible sequence of material state transitions.

---

## Suggested Reading Order

For a practitioner reading the codebase for the first time:

1. **`Docs/Architecture-Invariants.md`** — understand what the four physical
   constraints are and where they come from before reading any proofs.

2. **`Haskell/UMST.hs`** — the simplest formal statement of the gate: pure
   Haskell functions, no category theory required. Read the type signatures and
   `gateCheck` to understand the structure.

3. **`Agda/Gate.agda`** — the dependent-type version: `Admissible` makes the
   gate's correctness a type-level property rather than a runtime boolean.
   Sections 1–3 are readable without prior Agda experience.

4. **`Coq/Gate.v`** — the proof-assistant version: Section 8 (`helmholtz_antitone`)
   shows a complete machine-checked proof of one invariant's mathematical basis.

5. **`Agda/Naturality.agda`** — the categorical statement: after understanding the
   gate (steps 2–3), this proves it is material-agnostic using the language of
   functors and natural transformations.

6. **`Agda/DIB-Kleisli.agda`** and **`Haskell/KleisliDIB.hs`** — the methodology
   layer: the DIB cycle as a Kleisli monad, with proof of the monad laws.

---

*Mathematical notation in this document follows standard usage:
\(\in\) means "is an element of"; \(\to\) denotes a function or morphism;
\(\circ\) denotes composition; \(\Rightarrow\) denotes a natural transformation;
\(\mathcal{C}\), \(\mathcal{D}\) denote categories;
\(\eta\), \(\mu\) are the standard names for the monad unit and multiplication;
\(\varepsilon\), \(\delta\) are the comonad counit and comultiplication;
\(F \dashv G\) denotes the adjunction "F is left adjoint to G";
\(\mathrm{Hom}_{\mathcal{C}}(A, B)\) denotes the set of morphisms from \(A\) to
\(B\) in category \(\mathcal{C}\).*
