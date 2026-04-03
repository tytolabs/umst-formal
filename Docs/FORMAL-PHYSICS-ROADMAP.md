# Formal physics extensions — roadmap for `umst-formal`

This document plans **optional future mathematics** in this repository. It does
not assert that any listed item is true in nature; it records **what would need
to be added** as definitions, axioms, or proofs to expand the **current** formal
artifact.

**Authoritative status today:** `PROOF-STATUS.md` and the build outputs of Agda,
Coq, Lean, and Haskell tests.

**Derivation obligations (what “prove” would require):** see
`Docs/FORMAL-PHYSICS-DERIVATION-PLAN.md` — precise statement shapes, required
extensions \(\Delta L\) and axiom bundles, and the logical sense in which those
claims are **not** well-formed in the current core language **L₀**.

---

## 1. Design: physical theories as structured types

A fragment of physics is represented as data (records / Σ-types), not as informal prose:

| Component | Role |
|-----------|------|
| State / spacetime carrier | Manifold, measurable space, or discrete set (as in `Gate`) |
| Observables | Real-valued or operator-valued maps |
| Dynamics / laws | Fields, ODEs, or step relations (`admissible` is an example) |
| Constitutive / SI data | Parameters with documented physical dimension |
| Interpretation | Operational reading; **outside** the proof unless formalized |

**Category-theoretic view (optional):** functors for unit systems and admissible
coarse-graining; **naturality** only under explicitly stated side conditions.

**Dependency discipline:** every formal claim should be a node in a proof DAG:
definitions → axioms (if any) → lemmas → theorems.  No claim without a file and
a `PROOF-STATUS.md` row.

---

## 2. What this repository already proves (relevant background)

| Layer | Content |
|-------|---------|
| **Gate** | Mass tolerance, **Clausius–Duhem** (`D_int ≥ 0`), hydration monotonicity, strength monotonicity — mechanized in Agda/Coq/Lean/Haskell. |
| **Helmholtz / SDF** | Concrete free-energy model and gradient lemmas where in scope. |
| **Landauer–Einstein fragment** | `Coq/LandauerEinsteinBridge.v`, `Lean/LandauerEinsteinBridge.lean`: \(m_{\mathrm{eq}}(T) = (k_B T\ln 2)/c^2\) from definitions + SR; Lean adds SI-exact constants and 300 K numeric brackets. |
| **Kleisli / constitutional** | Subject reduction; **graded** N-step composition (`admissibleN_compose` / `admissible_N_compose`, `WellTypedN`, `kleisliFoldWellTypedN`). The old `admissible_trans` / `admissibleTrans` axiom was **removed** (refutable); see `PROOF-STATUS.md`. |

**MaOS / implementation link:** the Rust gate and Haskell `UMST.hs` are **reference
implementations** checked against the formal predicate where the FFI/test suites
apply. They are not substitutes for the proof assistants.

---

## 3. Landauer–Einstein fragment — boundaries (no speculation)

**Mechanized:** algebra and numeric brackets as in `PROOF-STATUS.md`.

**Not mechanized here (would be new work):**

- A **theorem** that all physically realizable bit erasures cost at least \(k_B T\ln 2\)
  in a stated thermodynamic model (Landauer as **derived** in that model).
- Any **identification** of \(m_{\mathrm{eq}}\) with experimentally separated
  “gravitational mass of information” beyond applying \(E=mc^2\) to the **defined**
  energy scale.

**Coq `ln2` vs Lean `Real.log 2`:** Coq keeps a positive parameter; Lean uses
Mathlib’s logarithm. Alignment is **policy + documentation** unless Coq gains a
matching analysis development.

**Agda:** `LandauerEinsteinTrace.agda` is an empty traceability module; no duplicate
of real analysis.

---

## 4. Phased extensions (definitions-first; no hidden physics)

### Phase A — Clausius identity in a continuum interface (+ Landauer law track)

- **Goal:** State reversible heat / entropy differentials in a smooth model, with
  hypotheses (e.g. local equilibrium) explicit.
- **Relation to repo:** complements the **discrete** Clausius–Duhem in `Gate`;
  does not replace it without a morphism between models.
- **Landauer as law:** requires process class **𝒞**, entropy functional, and second
  law or microscopic model — see **§1** of `FORMAL-PHYSICS-DERIVATION-PLAN.md`.

### Phase B — Entropy bounds (holographic / Bekenstein-style)

- **Goal:** Fix one literature variant (hypotheses on spacetime and entropy
  functional) and formalize the inequality as `∀ h : Hyp, …`.
- **Expectation:** heavy axiom load (QFT on curved background, etc.) unless scope
  is drastically simplified.
- **Derivation prerequisites:** **§4** of `FORMAL-PHYSICS-DERIVATION-PLAN.md`.

### Phase C — Cosmology (e.g. Friedmann + stress–energy ansätze)

- **Goal:** Separate FLRW **definitions** and ODEs from **phenomenological** terms
  (e.g. information density) so the latter are never mistaken for gate theorems.
- **Derivation prerequisites:** **§5** of `FORMAL-PHYSICS-DERIVATION-PLAN.md`.

### Phase C′ — Gravitational “information mass” (beyond SR bridge)

- **Goal:** Any coupling to **\(G_{\mu\nu}\)** or operational weighing requires
  **T_GR** + explicit **\(T_{\mu\nu}\)** / measurement map — **§2** of
  `FORMAL-PHYSICS-DERIVATION-PLAN.md`.

### Phase A′ — Jacobson-type field equations from horizon thermodynamics

- **Prerequisites:** Lorentzian geometry, horizon heat, entropy — **§3** of
  `FORMAL-PHYSICS-DERIVATION-PLAN.md`.

### Phase D — Cross-prover constant alignment

- **Goal:** Maintain tables mapping Coq parameters to Lean `def`s (already done
  informally for \(k_B\), \(c\), \(\ln 2\)).

---

## 5. Release checklist (formal artifact hygiene)

Use this list when **adding** new physics to the tree.

- [ ] Every **new** physics claim has a module, build command, and `PROOF-STATUS.md` row.
- [ ] **Axioms** are listed in the axiom inventory; no “implicit” physics.
- [ ] `cd Agda && make check`, `cd Coq && make`, `cd Lean && lake build UMST`,
      default Haskell gate tests, and `cabal test landauer-einstein-sanity` all succeed.

### 5a. Present tree (satisfied for core + Landauer–Einstein fragment)

| Item | Status |
|------|--------|
| Gate / Kleisli / SDF core | Mechanized; see `PROOF-STATUS.md` |
| Landauer–Einstein algebra | `Coq/LandauerEinsteinBridge.v` |
| SI + ln 2 + 300 K brackets | `Lean/LandauerEinsteinBridge.lean` |
| Agda traceability | `Agda/LandauerEinsteinTrace.agda` |
| Haskell rational sanity vs Lean tight numerators | `cabal test landauer-einstein-sanity` |
| Axiom inventory | `PROOF-STATUS.md` §Complete Axiom / Postulate Inventory |
| Cross-tool ln(2) policy | Coq parameter `ln2`; Lean `Real.log 2` (documented in Coq header + `PROOF-STATUS.md`) |

---

## 6. What this roadmap explicitly does **not** do

- It does not rate truth claims about Nature beyond what is **proved or axiomatized**
  in this repository.
- It does not tie `umst-formal` to external documents; those map **to** this
  artifact only through explicit engineering and documentation work.
