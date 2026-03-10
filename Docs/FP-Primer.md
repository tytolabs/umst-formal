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
Lambda Calculus
  ├── Lambda Abstraction → Beta/Alpha/Eta · Y Combinator · Church Encoding · Combinatory Logic
  ├── Currying (→ CCC, Exponential Object)
  └── Referential Transparency (→ Monad / IO boundary)

Type Theory
  ├── Algebraic Data Type (Sum + Product)
  ├── Parametric Polymorphism (→ Natural Transformation)
  ├── Dependent Type (→ Curry-Howard)
  └── Curry-Howard Isomorphism (propositions ↔ types, proofs ↔ programs)

Category Theory
  └── Category
        ├── Product · Coproduct · Initial · Terminal · Isomorphism
        ├── Monoidal Category → String Diagram
        ├── Cartesian Closed Category → Exponential Object → Currying
        ├── Functor
        │     └── Endofunctor
        │           ├── Monad
        │           │     ├── Kleisli Category → Free Category on a Graph
        │           │     ├── Monad Transformer
        │           │     ├── Free Monad
        │           │     └── (uses) Monoid
        │           └── Comonad
        ├── Natural Transformation
        │     ├── Applicative Functor
        │     ├── Adjunction → (induces) Monad
        │     └── Yoneda Lemma
        ├── F-Algebra · Catamorphism
        ├── Limit · Colimit
        ├── Profunctor
        └── 2-Category (enriches the whole map)
```

**Sections §1–§18** cover concepts used directly in this repository.
**Sections §19–§41** extend to the full mathematical foundations that the code
builds on and the literature references.
**Sections §42–§52** apply the complete framework to geometric computation via SDF
and FRep, showing the same categorical laws operating on continuous geometry.

```
SDF / FRep (Application Domain — §42–§52)
  ├── Implicit Function (FRep)         ← pure function (§1), exponential (§23)
  │     └── SDF                        ← stronger contract (Eikonal)
  │           ├── R-Function           ← monoid (§9) on SDF
  │           ├── Functional CSG       ← semigroup / monoid composition
  │           ├── Blending Operator    ← applicative (§13) combination
  │           ├── Offset Surface       ← endofunctor action (§8), natural trans. (§11)
  │           ├── Gradient / Normal    ← natural transformation (§11)
  │           └── Ray Marching         ← Kleisli composition (§12), fixed point (§39)
  ├── Recursive Shape                  ← catamorphism (§26), Fix (§26)
  ├── Geometry DSL                     ← free monad (§18), initial algebra (§26)
  └── HFRep                            ← monad transformer stack (§14)
```

---

### Direct Repository Concepts (§1–§18)

`Function` → `Higher-Order Function` → `Type` → `Higher-Order Type` →
`Recursion` → `Category` → `Functor` → `Endofunctor` → `Monoid` →
`Monad` → `Natural Transformation` → `Kleisli Category` →
`Applicative Functor` → `Monad Transformer` → `2-Category` →
`Adjunction` → `Comonad` → `Free Monad`

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
gateCheck :: ThermodynamicState -> ThermodynamicState -> Double -> AdmissibilityResult
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

**In this repository.** The QuickCheck property tests in `Haskell/test/Test.hs` pass
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
  , maxStrength :: Double   -- MPa    (theoretical maximum at α = 1)
  }
```

The same type is defined, with identical fields, in Agda (`Agda/Gate.agda`), Coq
(`Coq/Gate.v`), Lean 4 (`Lean/Gate.lean`), and Haskell (`Haskell/UMST.hs`), giving
four independent formal representations of the same physical object.

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
`Haskell/test/Test.hs` use recursion to generate lists of test states. The Coq extraction
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

**In this repository.** The QuickCheck generators in `Haskell/test/Test.hs` use
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
The four formal layers (Agda, Coq, Lean 4, Haskell) are 0-cells. The type correspondences
between layers (e.g., `ThermodynamicState` in Agda ↔ `thermo_state` in Coq) are
1-cells. The proofs that those correspondences commute with the gate (e.g., that the
Haskell `gateCheck` agrees with the Agda `gate` on all inputs) are 2-cells. The
synthesis table in `Docs/Architecture-Invariants.md` is a presentation of this
2-categorical structure in tabular form. The 2-categorical perspective also makes
precise why the four layers are redundant by design: they are four different
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

## Extended Foundations

The sections above (§1–§18) cover every concept used directly in this repository.
The following sections complete the mathematical background: they are concepts that
the code's comments reference, that the proofs build on implicitly, or that any
reader pursuing the literature will encounter immediately. They are grouped by domain
but follow the same format.

---

### Category Theory: Structures and Constructions

---

## 19. Product and Coproduct

**Definition.** A product combines two objects into a single object that projects
uniquely back onto each original. A coproduct (sum) is the dual: either original
object injects uniquely into the combined object and can later be distinguished.

**Precisely.** The product \(A \times B\) has projection morphisms
\(\pi_1: A \times B \to A\) and \(\pi_2: A \times B \to B\) satisfying the universal
property: for any \(C\) with morphisms \(f: C \to A\), \(g: C \to B\), there is a
unique \(\langle f, g \rangle: C \to A \times B\) such that
\(\pi_1 \circ \langle f, g \rangle = f\) and \(\pi_2 \circ \langle f, g \rangle = g\).

The coproduct \(A + B\) has injection morphisms \(\iota_1: A \to A + B\),
\(\iota_2: B \to A + B\) satisfying the dual universal property for case analysis.

In Haskell: product is `(a, b)`; coproduct is `Either a b`.

```haskell
data Either a b = Left a | Right b

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x)  = f x
either _ g (Right y) = g y
```

**In this repository.** `ThermodynamicState` is a product type: five fields composed
by pairing (density × freeEnergy × hydration × strength × maxStrength). `AdmissibilityResult` is
also a product (accepted, dissipation, and four invariant-check fields). `MaterialClass`
in `Agda/Naturality.agda` is a coproduct — `OPC | Lime | Earth | Geopolymer | RAC` —
a sum of five distinct constructors. (The Haskell `MaterialType` in `UMST.hs` is a
finer-grained coproduct with 17 constructors covering individual concrete constituents.)

---

## 20. Initial and Terminal Object

**Definition.** An initial object has exactly one morphism to every other object in
the category. A terminal object receives exactly one morphism from every other object.

**Precisely.** An object \(0\) is initial if for every object \(A\) there is a unique
\(!_A: 0 \to A\). An object \(1\) is terminal if for every object \(A\) there is a
unique \(!_A: A \to 1\). In **Hask**:

```haskell
data Void                      -- initial: uninhabited, no constructors

absurd :: Void -> a
absurd x = case x of {}        -- unique morphism; vacuously defined

unit :: a -> ()
unit _ = ()                    -- unique morphism to terminal
```

**In this repository.** In `Agda/Gate.agda`, the Agda type `⊥` (bottom) is the
initial object: it is used in `⊥-elim` to discharge contradictory branches in the
`gate` decision procedure (e.g., when an invariant fails and we need to derive
`⊥`). The terminal type `⊤` appears as the trivially satisfied proof obligation
in the admissibility record's trivially-true fields.

---

## 21. Isomorphism

**Definition.** An isomorphism between two objects is a pair of morphisms that are
mutual inverses: composing them in either order yields the identity. Two isomorphic
objects are structurally indistinguishable within the category.

**Precisely.** Morphisms \(f: A \to B\) and \(g: B \to A\) form an isomorphism
\(A \cong B\) if \(g \circ f = \mathrm{id}_A\) and \(f \circ g = \mathrm{id}_B\).
Every property preserved by the category's structure transfers across an isomorphism.

```haskell
type Iso a b = (a -> b, b -> a)

-- Example: newtype isomorphism
newtype Density = Density Double
isoDensity :: Iso Density Double
isoDensity = (\(Density x) -> x, Density)
```

**In this repository.** The type correspondence table in `Docs/Architecture-Invariants.md`
presents a family of isomorphisms: `ThermodynamicState` (Agda) \(\cong\)
`thermo_state` (Coq) \(\cong\) `ThermodynamicState` (Haskell). These are not
equalities — the languages are different — but isomorphisms in an appropriate
2-category (§15). The Curry-Howard isomorphism (§34) is a further instance: the
Agda `Admissible` proof type is isomorphic to the Coq `admissible` proposition.

---

## 22. Cartesian Closed Category

**Definition.** A Cartesian closed category (CCC) is one that has all finite
products, a terminal object, and an internal function space (exponential object,
§23) for every pair of objects. This structure is exactly equivalent to the
simply-typed lambda calculus.

**Precisely.** A category \(\mathcal{C}\) is Cartesian closed if:
1. It has a terminal object \(1\)
2. Every pair of objects \(A, B\) has a product \(A \times B\)
3. Every pair \(A, B\) has an exponential \(B^A\) with evaluation
   \(\mathrm{ev}: B^A \times A \to B\) satisfying the universal currying property

The category **Hask** (ignoring non-termination) is Cartesian closed. This is the
formal reason why Haskell's type system corresponds to the simply-typed lambda
calculus.

**In this repository.** The CCC structure of **Hask** guarantees that every function
type in `Haskell/UMST.hs` and `Haskell/KleisliDIB.hs` composes lawfully. More
directly: the Agda type-theory underlying `Agda/Gate.agda` is the internal language
of a locally Cartesian closed category (LCCC), which is what enables dependent types
(§33) — the generalisation of CCC where the exponential object may depend on its
base.

---

## 23. Exponential Object

**Definition.** The exponential object \(B^A\) within a category represents the
collection of all morphisms from \(A\) to \(B\) as a first-class object in the
category. It is equipped with an evaluation morphism \(\mathrm{ev}: B^A \times A \to B\).

**Precisely.** For any morphism \(f: C \times A \to B\) there exists a unique
"curried" morphism \(\lambda f: C \to B^A\) such that
\(\mathrm{ev} \circ (\lambda f \times \mathrm{id}_A) = f\). This is the universal
property of the exponential.

In Haskell the exponential \(B^A\) is simply the function type `a -> b`; evaluation
is function application `($)`.

**In this repository.** The gate type
`gateCheck :: ThermodynamicState -> ThermodynamicState -> Double -> AdmissibilityResult`
is an exponential in **Hask**: it is an object of the category (a first-class value
that can be passed to higher-order functions, stored, composed). The QuickCheck
property `forAll arbitrary (\s -> ...)` takes the gate function as an exponential
object and applies it to generated inputs — precisely the evaluation morphism.

---

## 24. Monoidal Category

**Definition.** A monoidal category equips an ordinary category with a tensor product
that combines objects and morphisms in an associative way (up to natural isomorphism)
together with a unit object that acts neutrally under the tensor.

**Precisely.** A monoidal category \((\mathcal{C}, \otimes, I, \alpha, \lambda, \rho)\)
consists of:
- A bifunctor \(\otimes: \mathcal{C} \times \mathcal{C} \to \mathcal{C}\)
- A unit object \(I\)
- Natural isomorphisms: associator \(\alpha_{A,B,C}: (A \otimes B) \otimes C \cong A \otimes (B \otimes C)\),
  left unitor \(\lambda_A: I \otimes A \cong A\), right unitor \(\rho_A: A \otimes I \cong A\)

satisfying the pentagon and triangle coherence diagrams.

**In this repository.** The `Agda/Naturality.agda` monoidal section records that the
category of material states carries a monoidal structure under mass (density): tensoring
two specimens combines their densities additively, and the unit is the zero-mass specimen.
Mass conservation is the gate's constraint that this monoidal structure is respected:
\(|\rho_{\mathrm{new}} - \rho_{\mathrm{old}}| \leq \delta\) is a monoidal coherence
condition. String diagrams (§41) provide a natural notation for monoidal-category
reasoning about material batch composition.

---

## 25. Yoneda Lemma

**Definition.** The Yoneda lemma states that any object in a category is completely
and uniquely determined by the collection of all morphisms going into or out of it,
expressed as a natural isomorphism between the hom-functor at that object and any
other functor evaluated at that object.

**Precisely.** For any functor \(F: \mathcal{C} \to \mathbf{Set}\) and object
\(A \in \mathcal{C}\):
\[\mathrm{Nat}(\mathcal{C}(A, -), F) \cong F\,A\]
naturally in \(A\) and \(F\). The isomorphism sends a natural transformation
\(\phi\) to \(\phi_A(\mathrm{id}_A)\), and sends \(x \in F\,A\) to the natural
transformation \(\phi_B(f) = F(f)(x)\).

```haskell
newtype Yoneda f a = Yoneda { runYoneda :: forall x. (a -> x) -> f x }

toYoneda :: Functor f => f a -> Yoneda f a
toYoneda fa = Yoneda (\k -> fmap k fa)

fromYoneda :: Yoneda f a -> f a
fromYoneda (Yoneda y) = y id
```

**In this repository.** The Yoneda lemma underlies the parametric polymorphism
guarantees in `Haskell/test/Test.hs`: a QuickCheck property `forAll arbitrary p` that
holds for a universally quantified type variable is a natural transformation statement
— the property commutes with any type-level mapping. More concretely, the Yoneda
embedding is implicit in the Agda proof that the gate is natural: the naturality
square for `gate-natural` in `Agda/Naturality.agda` is a Yoneda-derived consequence
of the gate's parametric definition.

---

## 26. F-Algebra and Catamorphism

**Definition.** An F-algebra for an endofunctor \(F\) is a pair of an object \(X\)
and a morphism \(\alpha: F\,X \to X\) that folds one layer of \(F\)-structure into
\(X\). The initial F-algebra is the universal such pair, from which every other
F-algebra receives a unique morphism — the catamorphism — that recursively folds
any \(F\)-structured data into a single value.

**Precisely.** For endofunctor \(F\), an F-algebra is \((X, \alpha: F\,X \to X)\).
The initial F-algebra \((\mu F, \mathrm{in}: F(\mu F) \to \mu F)\) satisfies: for
any \((X, \alpha)\) there is a unique catamorphism \(\llbracket\alpha\rrbracket: \mu F \to X\)
with \(\llbracket\alpha\rrbracket \circ \mathrm{in} = \alpha \circ F\llbracket\alpha\rrbracket\).

```haskell
newtype Fix f = Fix { unFix :: f (Fix f) }   -- μF

cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . unFix
```

**In this repository.** The Agda monad-law proof in `Agda/DIB-Kleisli.agda` uses
structural recursion on the `M A` record, which is a catamorphism over the recursive
structure of monadic computations. The `DIBState → (A × DIBState)` representation
is the initial algebra of the state-monad functor. More directly: the `cata` pattern
is the mathematical justification for why the monad laws (`left-unit`, `right-unit`,
`assoc` in the Agda proof) can be established by structural induction rather than
requiring additional axioms.

---

## 27. Limit and Colimit

**Definition.** A limit is the universal object that maps into every object in a
diagram compatibly with all the diagram's morphisms. A colimit is the dual: a
universal object that every object in the diagram maps into.

**Precisely.** Given a diagram \(D: \mathcal{J} \to \mathcal{C}\), a limit
\((L, \{\pi_j: L \to D(j)\}_{j \in \mathcal{J}})\) is a cone such that every other
cone factors through it uniquely. Products, equalisers, and pullbacks are special
cases. Colimits are the dual construction; coproducts, coequalisers, and pushouts
are special cases.

**In this repository.** The multi-layer correspondence (Agda, Coq, Lean 4, Haskell all
formalising the same gate) is a limit in a suitable 2-category: the UMST-Formal
system is the universal object that maps into each formal layer compatibly. The
`make all` target in `GNUmakefile` computes this limit computationally, ensuring all
layers agree before accepting a build.

---

## 28. Profunctor

**Definition.** A profunctor is a functor that is contravariant in one argument and
covariant in another. It generalises the notion of a relation between two categories
and is the foundational abstraction for optics (lenses, prisms) and bidirectional
transformations.

**Precisely.** A profunctor \(P: \mathcal{C}^{\mathrm{op}} \times \mathcal{D} \to \mathbf{Set}\)
assigns to each pair \((A, B)\) a set \(P(A, B)\) and lifts morphisms
\(f: A' \to A\) in \(\mathcal{C}\) and \(g: B \to B'\) in \(\mathcal{D}\)
to a function \(P(f, g): P(A, B) \to P(A', B')\). The dinaturality law must hold.

```haskell
class Profunctor p where
  dimap :: (s -> a) -> (b -> t) -> p a b -> p s t
```

**In this repository.** Profunctors are not used directly in the current codebase,
but they are the natural abstraction for the FFI bridge in `Haskell/FFI.hs`:
a C-to-Haskell binding is a heterogeneous mapping (contravariant in input type,
covariant in output type) between two different type systems. A future version of
the FFI layer expressed as a `Profunctor` instance would make the bidirectionality
of the Rust ↔ Haskell correspondence compositional and verifiable.

---

## 29. Free Category on a Graph

**Definition.** Every category has an underlying directed graph whose vertices are
objects and directed edges are morphisms. The free category on a directed graph is
the smallest category generated by that graph: objects are the graph's vertices,
morphisms are all finite paths (sequences of composable edges), identity is the
empty path, and composition is path concatenation.

**Precisely.** Given graph \(G = (V, E)\), the free category \(\mathbf{F}(G)\) has
objects \(V\) and morphisms all finite paths \(v_0 \to v_1 \to \cdots \to v_n\).
This construction is the left adjoint to the forgetful functor from **Cat** to
directed graphs.

**In this repository.** The DIB pipeline is a path in a free category: Discovery,
Invention, Build are three edges (morphisms) on the graph of knowledge states.
Kleisli composition in `Agda/DIB-Kleisli.agda` and `Haskell/KleisliDIB.hs` is
exactly path concatenation — the free category's composition — lifted to a monadic
context. The Agda associativity proof (`assoc`) is the proof that path concatenation
is associative in this free category.

---

## 30. String Diagram

**Definition.** A string diagram is a two-dimensional graphical notation for
morphisms in a monoidal category: wires represent objects, boxes represent morphisms,
vertical stacking corresponds to composition, and horizontal juxtaposition corresponds
to the tensor product \(\otimes\). Interchange law and naturality become topological
deformations of the diagram.

**Precisely.** In a monoidal category, a morphism \(f: A \otimes B \to C \otimes D\)
is drawn as a box with two input wires (labelled \(A\), \(B\)) and two output wires
(\(C\), \(D\)). The naturality square for a natural transformation \(\eta\) becomes
the statement that the \(\eta\)-box can slide past any other box along a wire.

**In this repository.** The naturality proof `gate-natural` in `Agda/Naturality.agda`
can be rendered as a string diagram: the gate box sits between two material-class
wires, and the naturality condition is the topological statement that the gate box
slides freely past the material-class morphism boxes. This is visually equivalent to
the algebraic proof but provides immediate intuition: the gate is material-agnostic
because it can be placed anywhere along the wire without changing the result.

---

### Type Theory

---

## 31. Algebraic Data Type

**Definition.** An algebraic data type is a composite type formed from sums
(coproducts) and products of simpler types, with constructors that precisely and
uniquely identify how a value was built. Every value of such a type can be
deconstructed exhaustively and unambiguously by pattern matching.

**Precisely.** An ADT is the initial algebra of a polynomial endofunctor
\(F = c_1 \times (-) + c_2 \times (-) + \cdots\) built from constant factors
(field types) and the identity (recursive occurrences). Constructors are the
injections of the coproduct; destructors are projections of the product.

```haskell
data MaterialClass
  = OPC
  | Lime
  | Earth
  | Geopolymer
  | RAC
  deriving (Eq, Ord, Show, Bounded, Enum)
```

**In this repository.** Every named type in the codebase is an ADT:
`ThermodynamicState` (a product of five `Double` fields), `MaterialClass` (a sum of
five nullary constructors in Agda; 17 in Haskell's `MaterialType`),
`AdmissibilityResult` (a product of one `Double` and five `Bool` fields).
In Agda, the same structures appear as `record` (product) and `data`
(sum) declarations in `Gate.agda` and `Naturality.agda`.

---

## 32. Parametric Polymorphism

**Definition.** Parametric polymorphism allows a single definition to operate
uniformly over any type without inspecting it. The compiler guarantees that the
definition cannot behave differently depending on the concrete type chosen, producing
a "free theorem" about its behaviour.

**Precisely.** A parametrically polymorphic function \(f: \forall a.\ F\,a \to G\,a\)
is a natural transformation: for every function \(h: a \to b\),
\(G\,h \circ f_a = f_b \circ F\,h\). This naturality is enforced by the type system
(Theorems for Free, Wadler 1989) — no runtime inspection of the type variable is
possible.

**In this repository.** The monad-law proofs in `Agda/DIB-Kleisli.agda` are
parametrically polymorphic over the value type `A`. The QuickCheck properties in
`Haskell/test/Test.hs` use polymorphic combinators (`forAll`, `property`) that hold for
any generated input type. The gate function is not polymorphic (it is specific to
`ThermodynamicState`), but the naturality proof `gate-natural` in `Agda/Naturality.agda`
treats the material-class parameter polymorphically.

---

## 33. Dependent Type

**Definition.** A dependent type is a type whose definition or structure may depend
on the value of a term. This blurs the distinction between types and values: a type
can encode a proposition about a specific value, and a term of that type is a proof
of that proposition.

**Precisely.** The dependent product \(\Pi_{x:A} B(x)\) is the type of functions
that map each \(x: A\) to a term of type \(B(x)\), where \(B\) may mention \(x\).
Its introduction rule is lambda abstraction; its elimination rule is application.
Agda and Coq implement full dependent types; Haskell approximates them with GADTs
and type families.

```agda
-- From Agda/Gate.agda
-- Admissible depends on both `old` and `new` state values:
Admissible : ThermodynamicState → ThermodynamicState → Set
```

**In this repository.** Dependent types are the central mechanism of `Agda/Gate.agda`.
The `Admissible` type is dependent: it takes two specific state values and produces
a type that is inhabited only when those states satisfy all four invariants. A
function returning `Admissible old new` is not just a boolean gate — it is a proof
that the specific transition `old → new` is physically consistent. This is why the
Agda layer provides strictly stronger guarantees than the Haskell layer: the gate's
correctness is encoded in the type, not deferred to runtime.

---

## 34. Curry-Howard Isomorphism

**Definition.** The Curry-Howard isomorphism establishes a direct correspondence
between propositions in logic and types in programming, and between proofs and
programs. A proposition is provable if and only if its corresponding type is
inhabited by a term.

**Precisely.** The correspondence maps:

| Logic | Type theory |
|---|---|
| Proposition \(P\) | Type \(P\) |
| Proof of \(P\) | Term of type \(P\) |
| Implication \(A \Rightarrow B\) | Function type \(A \to B\) |
| Conjunction \(A \land B\) | Product type \(A \times B\) |
| Disjunction \(A \lor B\) | Sum type \(A + B\) |
| False \(\bot\) | Empty type `Void` |
| True \(\top\) | Unit type `()` |
| Universal quantification \(\forall x.\ P(x)\) | Dependent product \(\Pi_{x:A} B(x)\) |

Under this correspondence, type checking is proof checking.

**In this repository.** The Curry-Howard isomorphism is the reason `Agda/Gate.agda`
and `Coq/Gate.v` are proofs, not just programs. When `gate old new` returns
`yes admissible-proof`, the `admissible-proof` term *is* a proof of the proposition
"this transition satisfies all four invariants." The Haskell `Bool` gate returns
evidence only at runtime; the Agda gate returns a proof object that can be inspected,
composed, and verified at compile time. The theorem `gate-natural` in
`Agda/Naturality.agda` is simultaneously a program (a function) and a proof
(a derivation that the naturality square commutes).

---

### Lambda Calculus

---

## 35. Currying

**Definition.** Currying is the transformation of a function that accepts multiple
arguments simultaneously into a chain of single-argument functions, each returning
the next until all arguments are supplied.

**Precisely.** Currying corresponds to the natural isomorphism in a Cartesian closed
category (§22):
\[\mathrm{Hom}(A \times B, C) \cong \mathrm{Hom}(A, B \Rightarrow C)\]
where \(B \Rightarrow C\) is the exponential object \(C^B\). In Haskell:

```haskell
curry :: ((a, b) -> c) -> a -> b -> c
curry f x y = f (x, y)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (x, y) = f x y
```

The right-associativity of `->` means `a -> b -> c` is `a -> (b -> c)`: every
multi-argument Haskell function is already curried by default.

**In this repository.** Every multi-argument function in the codebase is curried.
`gateCheck :: ThermodynamicState -> ThermodynamicState -> Double -> AdmissibilityResult`
is a function that takes a state, returns a function that takes another state,
returns a function that takes a time step, and returns a result. This means `gateCheck old` is a
valid partial application that can be stored, mapped over a list of new states, or
passed to a higher-order function. The adjunction \((- \times S) \dashv (S \to -)\)
described in §16 is the categorical statement that this currying isomorphism exists.

---

## 36. Referential Transparency

**Definition.** Referential transparency is the property that any expression can be
replaced by its evaluated result anywhere in the program without altering the
program's overall meaning or behaviour.

**Precisely.** An expression \(e\) is referentially transparent if for any context
\(C[-]\), substituting \(e\) with its denotation \(\llbracket e \rrbracket\) leaves
the meaning of \(C[e]\) unchanged:
\[e_1 \equiv e_2 \implies C[e_1] \equiv C[e_2]\]
This holds for all pure Haskell expressions. It fails in the presence of mutable
state, I/O, or non-determinism — which is why those effects are quarantined in the
`IO` monad.

**In this repository.** All functions in `Haskell/UMST.hs` (`gateCheck`, `fromMix`)
and their internal computations are referentially transparent: calling them with the same
arguments twice gives the same result. This property is what makes the QuickCheck
property tests in `Haskell/test/Test.hs` valid — if `gateCheck` had hidden mutable
state, the same test input could produce different results on different runs.
The `IO` boundary in `Haskell/KleisliDIB.hs` is precisely the line at which
referential transparency ends and managed effects begin.

---

## 37. Lambda Abstraction

**Definition.** Lambda abstraction is the mechanism for forming anonymous functions
by binding a variable name to an expression body. The resulting term, written
\(\lambda x.\ e\), denotes a function that maps any value \(v\) to \(e\) with \(x\)
replaced by \(v\).

**Precisely.** The typing rule for lambda abstraction in the simply-typed lambda
calculus:
\[\frac{\Gamma, x: A \vdash M: B}{\Gamma \vdash \lambda x^A.\ M : A \to B}\]
This is the introduction rule for the function type (the exponential object).
In Haskell: `\x -> e`.

**In this repository.** The `discover`, `invent`, and `build` Kleisli arrows in
`Haskell/KleisliDIB.hs` are defined using lambda abstraction:
`discover = \obs -> StateT (\s -> ...)`. The Agda proofs use lambda abstraction
to construct proof terms: `\s → (a , s)` in the definition of `returnM` in
`Agda/DIB-Kleisli.agda`. In Coq, `fun x => e` is the equivalent notation.

---

## 38. Beta Reduction, Alpha Conversion, and Eta Conversion

**Definition.** Beta reduction applies a lambda abstraction to an argument by
substituting the argument for the bound variable. Alpha conversion renames a bound
variable without changing the function's meaning. Eta conversion removes a redundant
lambda that does nothing but pass its argument to another function.

**Precisely.**

- **Beta**: \((\lambda x.\ M)\ N \to_\beta M[N/x]\) (substitute \(N\) for \(x\) in \(M\))
- **Alpha**: \(\lambda x.\ M \equiv_\alpha \lambda y.\ M[y/x]\) (rename bound variable)
- **Eta**: \(\lambda x.\ (M\ x) \equiv_\eta M\) when \(x\) does not appear free in \(M\)

These three conversion rules define observational equality in the lambda calculus.

**In this repository.** Agda's proof checker applies all three conversions during
type checking: it beta-reduces function applications when checking that a proof term
has the claimed type, alpha-converts internally to avoid variable capture, and uses
eta-expansion to compare functions. The Coq tactic `simpl` in `Coq/Gate.v` applies
beta and eta reductions when simplifying proof goals. Referential transparency (§36)
in Haskell is the semantic statement that beta reduction preserves meaning.

---

## 39. Y Combinator

**Definition.** The Y combinator is a fixed-point operator expressible in pure lambda
calculus that enables recursive definitions without named self-reference. It
satisfies \(Y\, f = f\,(Y\, f)\) for any function \(f\).

**Precisely.**
\[Y \equiv \lambda f.\ (\lambda x.\ f\,(x\,x))\ (\lambda x.\ f\,(x\,x))\]

In Haskell, where the type system prevents the untyped self-application \(x\,x\),
recursion is expressed via the built-in `fix`:

```haskell
fix :: (a -> a) -> a
fix f = let x = f x in x
```

**In this repository.** The Y combinator is implicit in every recursive Agda proof.
The structural recursion used in `Agda/DIB-Kleisli.agda` to prove the monad laws
is a typed fixed-point computation: Agda's termination checker verifies that the
self-reference decreases on a well-founded ordering, which is the disciplined version
of the Y combinator. The `cata` function in §26 is the categorical generalisation
of Y: both compute fixed points, but `cata` does so over a functor-shaped recursive
type rather than an untyped term.

---

## 40. Church Encoding

**Definition.** Church encoding represents data values — natural numbers, booleans,
pairs, lists — as higher-order functions that encode their own elimination rules.
A Church-encoded value *is* its own case-analysis function.

**Precisely.** A Church natural number \(n\) is \(\lambda f.\ \lambda x.\ f^n\,x\)
(apply \(f\) exactly \(n\) times to \(x\)). In Haskell:

```haskell
type ChurchNat = forall a. (a -> a) -> a -> a

zero :: ChurchNat
zero f x = x

succ :: ChurchNat -> ChurchNat
succ n f x = f (n f x)

toInt :: ChurchNat -> Int
toInt n = n (+1) 0
```

**In this repository.** Church encoding is the conceptual ancestor of Agda's
inductive types. The `Admissible` record in `Agda/Gate.agda` is a dependent Church
encoding: instead of returning `Bool`, the gate returns a proof object that encodes
its own elimination rule — you can only extract the invariant witnesses from
`Admissible` by providing case handlers for each field. The Coq `Inductive` types
in `Coq/Gate.v` are the proof-assistant realisation of the same idea.

---

## 41. Combinatory Logic

**Definition.** Combinatory logic is a variable-free reformulation of the lambda
calculus using a small set of primitive combinators that rewrite expressions through
pure application. The SKI system is the canonical minimal base.

**Precisely.** The three combinators and their reduction rules:
\[\mathbf{I}\,x = x, \qquad \mathbf{K}\,x\,y = x, \qquad \mathbf{S}\,x\,y\,z = x\,z\,(y\,z)\]

Any lambda term can be translated into an equivalent SKI term (bracket abstraction),
eliminating all variable binding. In Haskell, `id`, `const`, and `(<*>)` for
functions correspond to \(\mathbf{I}\), \(\mathbf{K}\), and \(\mathbf{S}\).

**In this repository.** Combinatory logic is not used directly, but it is the
theoretical foundation for point-free style — writing functions without naming
their arguments — which appears throughout `Haskell/test/Test.hs` and `Haskell/UMST.hs`.
For example, `cata alg = alg . fmap (cata alg) . unFix` is a point-free definition;
its combinator translation would use \(\mathbf{S}\) to handle the shared `cata alg`
argument. The proof irrelevance properties used in `Agda/Gate.agda` (where two proofs
of the same proposition are considered equal) correspond to the \(\mathbf{K}\)
combinator: the proof term is present but its specific value is discarded.

---

## How These Concepts Combine in UMST-Formal

The table below maps each formal concept to its concrete role in this codebase.

| Concept | Role in UMST-Formal | Primary file |
|---|---|---|
| Function | Pure gate predicate; each invariant check | `Haskell/UMST.hs` |
| Higher-order function | Kleisli composition; QuickCheck property API | `Haskell/KleisliDIB.hs`, `Haskell/test/Test.hs` |
| Type | `ThermodynamicState`, `MaterialClass`, `Admissible` | All layers |
| Higher-order type | `StateT`, `Maybe`, monad transformer stack | `Haskell/KleisliDIB.hs` |
| Recursion | Agda monad-law proofs; QuickCheck generators | `Agda/DIB-Kleisli.agda` |
| Category | **Hask** as ambient category; admissible subcategory | Conceptual foundation |
| Functor | `F`, `G` on `MaterialClass` | `Agda/Naturality.agda` |
| Endofunctor | All `Functor` instances; `StateT UMSTState IO` | `Haskell/KleisliDIB.hs` |
| Monoid | Monoid structure on `All`; DIB state accumulation | `Haskell/test/Test.hs` |
| Monad | State monad for DIB pipeline; law proofs | `Agda/DIB-Kleisli.agda`, `Haskell/KleisliDIB.hs` |
| Natural transformation | Gate as `η: F ⟹ G`; material-agnosticism proof | `Agda/Naturality.agda` |
| Kleisli category | DIB phase composition; law verification | `Agda/DIB-Kleisli.agda`, `Haskell/KleisliDIB.hs` |
| Applicative functor | Independent field generation in tests | `Haskell/test/Test.hs` |
| Monad transformer | `StateT UMSTState IO`; combining state + IO effects | `Haskell/KleisliDIB.hs` |
| 2-Category | Four formal layers as 0-cells; correspondences as 1-cells; agreement proofs as 2-cells | `Docs/Architecture-Invariants.md` (synthesis table) |
| Adjunction | Mathematical origin of the State monad and its `runStateT` isomorphism | `Haskell/KleisliDIB.hs` (structural) |
| Comonad | Future direction: spatial / historical context for gate evaluation | `CONTRIBUTING.md` |
| Free monad | Future direction: gate effect algebra separating description from interpretation | `CONTRIBUTING.md` |
| Product / Coproduct | `ThermodynamicState` (product); `MaterialClass` (sum of 5 constructors) | `Haskell/UMST.hs`, `Agda/Gate.agda` |
| Initial / Terminal | `⊥` in Agda contradiction branches; `⊤` for trivial obligations | `Agda/Gate.agda` |
| Isomorphism | Layer correspondences (Agda ≅ Coq ≅ Haskell types) | `Docs/Architecture-Invariants.md` |
| Cartesian closed category | Ambient structure of **Hask**; locally CCC for Agda dependent types | Conceptual foundation |
| Exponential object | Every function type; `gate` as first-class value | All layers |
| Monoidal category | Material batch composition; mass conservation as monoidal constraint | `Agda/Naturality.agda` |
| Yoneda lemma | Parametricity; gate-natural proof | `Agda/Naturality.agda`, `Haskell/test/Test.hs` |
| F-algebra / Catamorphism | Monad-law proof by structural induction | `Agda/DIB-Kleisli.agda` |
| Limit / Colimit | Multi-layer agreement as limit; `make all` as computational realisation | `GNUmakefile` |
| Profunctor | Future direction: typed FFI bridge | `Haskell/FFI.hs` |
| Free category | DIB pipeline as path; associativity proof as path associativity | `Agda/DIB-Kleisli.agda` |
| String diagram | Graphical naturality proof for gate material-agnosticism | `Agda/Naturality.agda` |
| Algebraic data type | Every named type in the codebase | All layers |
| Parametric polymorphism | Monad-law proofs; QuickCheck universals | `Agda/DIB-Kleisli.agda`, `Haskell/test/Test.hs` |
| Dependent type | `Admissible old new` — correctness encoded in the type | `Agda/Gate.agda` |
| Curry-Howard | Agda proof terms are programs; type checking = proof checking | `Agda/Gate.agda`, `Coq/Gate.v` |
| Currying | All multi-argument functions; `gateCheck old` as partial application | All Haskell files |
| Referential transparency | Foundation of all pure functions; QuickCheck validity | `Haskell/UMST.hs` |
| Lambda abstraction | Kleisli arrows; proof term construction | `Haskell/KleisliDIB.hs`, `Agda/DIB-Kleisli.agda` |
| Beta/Alpha/Eta | Agda type checking; Coq `simpl` tactic; equational reasoning | `Agda/Gate.agda`, `Coq/Gate.v` |
| Y combinator / `fix` | Implicit in all structural recursion and monad-law proofs | `Agda/DIB-Kleisli.agda` |
| Church encoding | Ancestor of Agda inductive types; `Admissible` as proof object | `Agda/Gate.agda` |
| Combinatory logic | Point-free style throughout; proof irrelevance in Agda | `Haskell/test/Test.hs`, `Agda/Gate.agda` |
| Implicit function (FRep) | Gate as implicit surface in state-product space | Conceptual (all layers) |
| SDF | Clausius-Duhem as signed distance to equilibrium surface | `Haskell/SDFGate.hs` (`clausiusDuhemSDF`) |
| R-Function | Gate as R-intersection of four invariant surfaces | `Agda/Gate.agda`, `Haskell/SDFGate.hs` |
| Functional CSG | Four-invariant conjunction = CSG intersection in state space | All gate layers |
| Blending operator | Tolerance bands (`massTolerance`, `tolerance`) as soft offsets | `Haskell/UMST.hs` |
| Offset surface | Each gate tolerance = offset of a hard invariant surface | `Haskell/SDFGate.hs` |
| Recursive shape / Catamorphism | Kleisli monad-law proof by structural recursion | `Agda/DIB-Kleisli.agda` |
| Ray marching | Gate checks as Kleisli composition in `Maybe`; fixed-point search | `Haskell/KleisliDIB.hs` |
| Gradient / Normal | Helmholtz gradient = −Q_hyd; `helmholtzAntitone` | `Haskell/SDFGate.hs`, `Coq/Gate.v` |
| Geometry DSL (Free/Initial) | Same pattern as `GateF` free monad; `foldFree` = interpreter | `CONTRIBUTING.md` |
| HFRep | Four formal layers = hybrid representations of same gate semantics | All layers + `ffi-bridge` |

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

### Geometric Computation via Function Representation

The following sections extend the framework to Signed Distance Functions (SDF) and
Function Representation (FRep). Every concept maps directly onto one already
introduced: implicit functions are pure functions, CSG is functional composition,
blending is applicative combination, recursive shapes are catamorphisms, and
the embedded geometry DSL is an instance of the free monad (§18). The UMST gate
function is itself an implicit surface in the product space of material states:
the admissible region is where the gate evaluates to "inside."

---

## 42. Implicit Function (FRep Core)

**Definition.** A Function Representation (FRep) object is a continuous real-valued
function \(f: \mathbb{R}^n \to \mathbb{R}\) such that the geometric surface is the
zero level set \(\{x \mid f(x) = 0\}\), the interior is where \(f(x) \leq 0\), and
the exterior is where \(f(x) > 0\). The object is defined entirely by the function;
no mesh, boundary representation, or sampling is needed.

**Precisely.** An FRep is a pure, referentially transparent function (§36). The
surface has no explicit representation — it is implicit in the function's zero set.
All geometric operations (union, intersection, offset, transformation) reduce to
function composition and arithmetic.

```haskell
type FRep = V3 Double -> Double   -- point in ℝ³ → signed value
```

The type `FRep` is an exponential object (§23) in **Hask**: a first-class value
that can be stored, passed, returned, and composed exactly like any other function.

**In this repository.** The UMST gate function viewed over state space defines an
implicit surface: the boundary of the admissible region in
\(\mathrm{ThermodynamicState} \times \mathrm{ThermodynamicState}\) is the zero set
of the gate's indicator. Points "inside" (all four invariants satisfied) correspond
to \(f \leq 0\); points "outside" (any invariant violated) to \(f > 0\). This
geometric reading of the gate is not just analogy — it is the precise reason the gate
is a decidable predicate (`Dec Admissible` in Agda): the zero set is a computable
level surface.

---

## 43. Signed Distance Function (SDF)

**Definition.** A Signed Distance Function (SDF) is an implicit function (§42) with
the additional property that \(|f(x)|\) equals the exact Euclidean distance from
\(x\) to the nearest surface point. The sign encodes interior (negative) or exterior
(positive).

**Precisely.** An SDF satisfies the Eikonal equation almost everywhere:
\(\|\nabla f(x)\| = 1\). This constraint — that the gradient has unit magnitude — is
the formal statement that \(f\) is a distance function, not merely an implicit one.
Many operations (e.g., offset by \(d\)) work correctly only when this condition holds.

```haskell
type SDF = V3 Double -> Double   -- same type as FRep; stronger contract

sphere :: Double -> SDF
sphere r p = norm p - r          -- distance from origin minus radius
```

**In this repository.** The Clausius-Duhem dissipation
\(D_\mathrm{int} = -\rho \cdot \dot{\psi} \geq 0\) in the UMST gate can be read as
a signed distance to the thermodynamic equilibrium surface: \(D_\mathrm{int} = 0\)
is the boundary, \(D_\mathrm{int} > 0\) is the admissible interior (energy
dissipating), and \(D_\mathrm{int} < 0\) would be the inadmissible exterior (energy
increasing). The tolerance \(\delta\) in mass conservation \(|\rho_\mathrm{new} -
\rho_\mathrm{old}| \leq \delta\) is an offset of this implicit surface (§47).

---

## 44. R-Function

**Definition.** An R-function is a real-valued continuous function that exactly
realises a Boolean set operation (union, intersection, difference) on the zero level
sets of two FRep/SDF functions while remaining \(C^\infty\)-smooth everywhere. It
generalises the `min`/`max` operations (which are \(C^0\) only) to smooth geometry.

**Precisely.** The R-union \(f \lor g\) satisfies: its zero set is exactly the
set-theoretic union of the zero sets of \(f\) and \(g\). One standard form:

\[f \lor g = \frac{f + g - \sqrt{f^2 + g^2}}{1 + \sqrt{2}}\]

```haskell
rUnion :: SDF -> SDF -> SDF
rUnion a b p =
  let f = a p; g = b p
  in (f + g - sqrt (f*f + g*g)) / (1 + sqrt 2)
```

The set of all SDF/FRep values under `rUnion` forms a commutative monoid with
identity the constant \(+\infty\) function (the "empty" shape with no interior).
This is the same monoid structure (§9) that appears in `All`, `&&`, and the test
suite — applied to continuous geometry rather than discrete booleans.

**In this repository.** The UMST gate combines four invariant sub-conditions using
logical conjunction (R-intersection, not union), but the structure is identical: each
sub-condition is an implicit function on state space, and the gate is their
R-intersection. The monoid identity is the vacuously satisfied condition (the
universal set). The `Admissible` record in `Agda/Gate.agda` is the dependent-type
realisation of R-intersection: all four fields must be inhabited simultaneously.

---

## 45. Functional Constructive Solid Geometry (CSG)

**Definition.** Functional CSG builds composite geometry by applying higher-order
combinators (union, intersection, subtraction, blending) directly to implicit or
signed-distance functions, producing a new function that represents the combined
object. The result is a tree of function compositions, not an explicit boundary.

**Precisely.** The set of FRep/SDF values with union (`min`) and intersection
(`max`) forms a semiring; with R-functions (§44) it forms a smooth semiring. Both
union and intersection are associative with identities, satisfying the monoid laws
(§9) in both dimensions:

```haskell
instance Semigroup SDF where
  (<>) = rUnion              -- smooth union; or `min` for exact SDF union

instance Monoid SDF where
  mempty = const 1e100       -- the "empty" shape: every point is outside
```

**In this repository.** The gate's conjunction of four invariants is a functional
CSG intersection in state space:

\[\mathrm{gate}(s_1, s_2) = \mathrm{massCond}(s_1, s_2) \;\cap\; \mathrm{clausiusCond}(s_1, s_2) \;\cap\; \mathrm{hydrationCond}(s_1, s_2) \;\cap\; \mathrm{strengthCond}(s_1, s_2)\]

The Haskell `gateCheck` function evaluates this CSG intersection explicitly; the
Agda `Admissible` record encodes it dependently; the Coq `admissible` proposition
encodes it as a logical conjunction; Lean 4 `Admissible` mirrors the Agda structure.
All four are the same CSG intersection, in four different formal languages.

---

## 46. Blending Operator

**Definition.** A blending operator is a higher-order function that takes two
implicit/SDF values and returns a smooth transition surface between them, controlled
by a parameter that determines the blend radius or smoothness. It extends CSG union
by allowing the surfaces to interpenetrate and merge gradually rather than sharply.

**Precisely.** One standard polynomial smooth-union (Quilez 2015):

```haskell
smoothUnion :: Double -> SDF -> SDF -> SDF
smoothUnion k a b p =
  let av = a p
      bv = b p
      h  = max (k - abs (av - bv)) 0 / k
  in min av bv - h * h * h * k * (1/6)
```

The parameter `k` controls the blend radius: as \(k \to 0\) the operator converges
to `min` (exact union); as \(k \to \infty\) the blend region expands to encompass
all space.

**In this repository.** The tolerance parameter \(\delta\) in the mass-conservation
check \(|\rho_\mathrm{new} - \rho_\mathrm{old}| \leq \delta\) is a blending operator
applied to the hard step at \(\delta = 0\): it replaces the binary pass/fail with a
soft band of width \(\delta\) around the exact conservation surface. The
`massTolerance` constant in `Haskell/UMST.hs` is this blend parameter. This is
precisely the Applicative (§13) pattern: independent effects (density change and
tolerance) are combined before any sequential dependency is introduced.

---

## 47. Offset Surface (Minkowski Sum with a Ball)

**Definition.** Offsetting an SDF by distance \(d\) moves its zero level set outward
by \(d\) (positive offset) or inward (negative). For a true SDF, this operation is
exact and requires only point-wise subtraction.

**Precisely.** Given SDF \(f\), the offset surface at distance \(d\) is:
\[f_d(x) = f(x) - d\]

This is a natural transformation (§11) on SDF values: it commutes with all CSG
operations, lifts uniformly across any shape, and preserves the Eikonal condition
\(\|\nabla f_d\| = 1\) identically (since \(\nabla f_d = \nabla f\)).

```haskell
offset :: Double -> SDF -> SDF
offset d f p = f p - d           -- functorial: works for any shape
```

The offset operation is an endofunctor action on SDF space: applying `offset d`
to any shape gives another shape of the same type, and the naturality condition
\(\mathrm{offset}\, d \circ \mathrm{op} = \mathrm{op} \circ \mathrm{offset}\, d\)
holds for any CSG operation `op`.

**In this repository.** Every tolerance-band in the UMST gate is an offset:
\(|\rho_\mathrm{new} - \rho_\mathrm{old}| \leq \delta\) is the zero-set condition of
the SDF \(f(s_1, s_2) = |\rho_\mathrm{new} - \rho_\mathrm{old}| - \delta\), i.e.,
the surface \(|\rho_\mathrm{new} - \rho_\mathrm{old}| = 0\) offset outward by
\(\delta\). The gate tolerances (`massTolerance` for density, `tolerance` for floating-point
comparisons, both in `Haskell/UMST.hs`) are offset parameters for the invariant surfaces.

---

## 48. Procedural and Recursive Shape Definition

**Definition.** Procedural geometry in FRep/SDF defines complex shapes through
recursive function calls on transformed coordinates — fractals, self-similar tilings,
subdivision surfaces — where a primitive base-case terminates the recursion. Each
recursive level refines the shape without an explicit limit mesh.

**Precisely.** This is catamorphism (§26) applied to geometry. A recursive shape
type is the initial F-algebra for a shape functor:

```haskell
data ShapeF a
  = Sphere  Double
  | Union   a a
  | Scale   (V3 Double) a
  deriving Functor

type Shape = Fix ShapeF

toSDF :: Shape -> SDF
toSDF = cata alg
  where
    alg (Sphere r)   = sphere r
    alg (Union a b)  = rUnion a b
    alg (Scale s f)  = \p -> f (p / s) * norm s
```

`cata alg` folds the shape tree into a single SDF function, exactly as a list fold
reduces a list to a single value. The `Functor` instance on `ShapeF` is what enables
the catamorphism — `fmap` lifts the recursive interpretation one level at a time.

**In this repository.** The Agda proof of the Kleisli monad laws in
`Agda/DIB-Kleisli.agda` uses structural recursion on the `M A` record — the same
pattern as `cata`: fold over the monadic computation tree, applying the algebra at
each node. The `ShapeF` functor is structurally identical to the DIB phase functor:
leaf nodes are base computations, internal nodes are compositions.

---

## 49. Ray Marching (Sphere Tracing)

**Definition.** Ray marching (sphere tracing) is a rendering algorithm that finds
the intersection of a ray with an SDF surface by iteratively stepping along the ray
by the exact SDF value at the current position. Each step is guaranteed safe —
the sphere of that radius contains no surface — and the iteration terminates when
the SDF value drops below an epsilon threshold.

**Precisely.** Let \(\mathrm{ro}\) be the ray origin, \(\mathrm{rd}\) the unit
direction, and \(f\) the SDF. Define the iterated map:

\[d_{n+1} = d_n + f(\mathrm{ro} + d_n \cdot \mathrm{rd})\]

This converges to the surface intersection when \(|f(\mathrm{ro} + d_n \cdot \mathrm{rd})| < \varepsilon\).

```haskell
rayMarch :: SDF -> V3 Double -> V3 Double -> Double -> Maybe (V3 Double)
rayMarch sdf ro rd maxDist = go 0
  where
    go d
      | d > maxDist                         = Nothing
      | abs (sdf (ro + d *^ rd)) < 1e-4    = Just (ro + d *^ rd)
      | otherwise                           = go (d + sdf (ro + d *^ rd))
```

**In this repository.** Ray marching is a fixed-point search — the categorical
fixed-point (§39, Y combinator) applied to the step function
\(d \mapsto d + f(\mathrm{ro} + d \cdot \mathrm{rd})\). The `go` function is
exactly `fix step` where `step` returns `Nothing` at termination and recurses
otherwise. This is Kleisli composition (§12) in the `Maybe` monad: each step is a
Kleisli arrow `Double -> Maybe Double`, and `rayMarch` is their Kleisli composition
under `>=>`. The UMST gate check is analogous: iterating through each invariant
check in sequence, short-circuiting to `Nothing` (inadmissible) as soon as any
condition fails — sphere tracing through the space of physical constraints.

---

## 50. Gradient and Normal Computation

**Definition.** The gradient \(\nabla f(x)\) of an SDF at a surface point gives the
outward unit normal vector. For a true SDF, \(\|\nabla f\| = 1\) everywhere, so
the gradient is already normalised. Gradients can be computed analytically,
symbolically, or via finite differences.

**Precisely.** The gradient is the categorical derivative of the SDF functor: it is
a natural transformation from the functor `SDF` to the functor `SDF -> V3` that
commutes with all CSG operations. For an SDF built from R-functions and offsets, the
gradient satisfies the chain rule automatically, which is the FRep analogue of
functor composition preserving structure.

Numeric approximation via finite differences:

```haskell
normal :: SDF -> V3 Double -> V3 Double
normal f p = normalize
  (V3 (f (p + e3 (1e-4, 0, 0)) - f p)
      (f (p + e3 (0, 1e-4, 0)) - f p)
      (f (p + e3 (0, 0, 1e-4)) - f p))
```

Automatic differentiation (dual numbers) computes the exact gradient at the cost
of evaluating `f` once with dual-number inputs instead of `Double`.

**In this repository.** The Helmholtz free-energy gradient
\(\dot{\psi} = \partial \psi / \partial \alpha \cdot \dot{\alpha} = -Q_\mathrm{hyd} \cdot \dot{\alpha}\)
computed inside `gateCheck` in `Haskell/UMST.hs` is the gradient of the Helmholtz SDF in the
one-dimensional hydration state space.  The Helmholtz SDF itself (`helmholtzSDF`) is
defined in `Haskell/SDFGate.hs` as an exact analytic formula rather than a finite
difference. The `helmholtz_antitone` theorem proved in `Coq/Gate.v` is the formal
statement that this gradient is negative (the SDF is antitone in \(\alpha\)):
the surface moves in the admissible direction as hydration advances.

---

## 51. Embedded DSL for Geometry (Free and Initial Algebra)

**Definition.** An embedded geometry DSL defines a set of primitive shape
constructors and combinators as an algebraic data type, then uses a free monad or
initial algebra to represent any composite geometry as a pure syntax tree. An
interpreter — a natural transformation from the DSL functor to any target monad
— evaluates the tree into a concrete SDF, a mesh, or a simulation result.

**Precisely.** Using the free monad (§18) over `ShapeF`:

```haskell
type ShapeDSL a = Free ShapeF a

-- a DSL program is a syntax tree
example :: ShapeDSL ()
example = do
  s1 <- liftF (Sphere 1.0)
  s2 <- liftF (Sphere 0.5)
  liftF (Union s1 s2)

-- the interpreter is the catamorphism toSDF
interpret :: ShapeDSL () -> SDF
interpret = foldFree (\case
  Sphere r   -> sphere r
  Union a b  -> rUnion a b
  Scale s f  -> \p -> f (p / s) * norm s)
```

The `foldFree` function is the free monad's universal property: it is the unique
monad homomorphism from `Free ShapeF` to any other monad, determined by a natural
transformation `ShapeF ~> m`.

**In this repository.** The Free Monad section (§18) described a `GateF` functor
for the gate effect algebra. The geometry DSL here is the exact same pattern applied
to shapes instead of gate operations. Both use `Free` to separate description from
interpretation; both use `cata`/`foldFree` as the interpreter combinator; both
produce a function (SDF or `AdmissibilityResult`) as output. The `toSDF` interpreter
is the geometry analogue of the DIB pipeline interpreter in `Haskell/KleisliDIB.hs`.

---

## 52. Hybrid Function Representation (HFRep)

**Definition.** Hybrid Function Representation (HFRep) combines FRep (continuous
implicit functions) with discrete or distance-based representations (SDF, ADF, IDF)
inside a single unified function, using higher-order wrappers to select between
representations contextually or by scale.

**Precisely.** An HFRep is a monad transformer stack (§14) applied to geometry:
different "effect layers" (continuous, discrete, sampled) are combined while each
preserving its own laws. The outer layer selects the representation; the inner layer
evaluates within it.

```haskell
-- Conceptual structure: hybrid of continuous FRep and discrete SDF
data HFRepF a
  = Continuous (V3 Double -> Double)   -- FRep layer
  | Discrete   (V3 Double -> Double)   -- SDF layer (with Eikonal contract)
  | Blend Double (HFRepF a) (HFRepF a) -- weighted combination

type HFRep = Fix HFRepF
```

The composition laws of the transformer stack (§14) guarantee that crossing layer
boundaries does not violate either representation's invariants, exactly as `lift`
promotes `IO` actions into `StateT IO` without losing the state-threading invariant.

**In this repository.** The UMST multi-layer system (Agda + Coq + Lean 4 + Haskell) is an
HFRep of formal representations: each layer uses a different formalism (dependent
types, propositions, tactics, pure functions) but encodes the same underlying gate semantics.
The `ffi-bridge` crate is the layer-crossing mechanism — analogous to `lift` — that
promotes Rust SDF evaluations (concrete, discrete, machine-level) into the Haskell
layer (abstract, continuous, type-checked). The synthesis table in
`Docs/Architecture-Invariants.md` is the HFRep's type correspondence: the same
"shape" (gate semantics) expressed in four different representation layers.

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
