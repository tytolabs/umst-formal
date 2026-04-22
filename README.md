<!--
SPDX-License-Identifier: MIT
-->
<!-- markdownlint-disable-file MD013 MD040 MD001 MD026 — hero README is intentionally dense; other docs stay strict via shared config. -->

<div align="center">

# The Thermodynamic Cost of Acting

### Every proposed transition is a claim on coherence. The gate answers in the negative as often as the model demands. What survives is what the inequalities allow.

This repository is the **classical meso-layer**: rational state changes, Shannon and Landauer bookkeeping, and lemmas that bind “growth stories” to explicit hypotheses. It extends [**The Thermodynamic Cost of Knowing**](https://doi.org/10.5281/zenodo.19159660) (observation and collapse in **`umst-formal-double-slit`**) toward **acts and commitments** without pretending that optimism is an axiom.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18940933.svg)](https://doi.org/10.5281/zenodo.18940933)
[![Lean](https://github.com/tytolabs/umst-formal/actions/workflows/lean.yml/badge.svg)](https://github.com/tytolabs/umst-formal/actions/workflows/lean.yml)
[![Haskell](https://github.com/tytolabs/umst-formal/actions/workflows/haskell.yml/badge.svg)](https://github.com/tytolabs/umst-formal/actions/workflows/haskell.yml)
[![Formal (Agda+Coq)](https://github.com/tytolabs/umst-formal/actions/workflows/formal.yml/badge.svg)](https://github.com/tytolabs/umst-formal/actions/workflows/formal.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-black.svg)](LICENSE)

**Machine-checked UMST formal core** — Agda · Coq · Lean 4 · Haskell QuickCheck · optional Rust FFI.

**Lean 4 (default roots):** **45** modules · **221** `theorem` + **17** `lemma` (line-start; `python3 scripts/lean_declaration_stats.py`; CI checks a frozen snapshot) · **0** tactic `sorry` · **1** project `axiom` (`physicalSecondLaw` in `LandauerLaw.lean` — [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md)).

The Economic filenames that sound like oracles are **parameterised predicates**. They do not see the world. Read [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md) before you cite them off-repo.

<br>

</div>

---

## From the cost of knowing to the cost of acting

[**The Thermodynamic Cost of Knowing**](https://doi.org/10.5281/zenodo.19159660) (**`umst-formal-double-slit`**) mechanises observation and collapse: path information has a Landauer-scale price. **This** tree holds the meso-scale follow-on — rational transitions, Shannon/Landauer lines in the ledger, and questions posed as **admissibility** and **burden** under stated assumptions. Quantum RCC does not load unless you attach the other artifact.

## Economic intuition (plain language)

Growth can outrun friction in the stories people tell. The formal layer does not endorse those stories. It **binds** them: **`Lean/Economic/`** (Wave 6.5.2) writes burden and information as **classical** quantities and keeps surrogate alarms explicit — thresholds and margins, not black-box “detectors” ([`SAFETY-LIMITS.md`](SAFETY-LIMITS.md), [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md)).

## Seventeen Economic modules — one sentence each

Shared scaffolding lives in [`Lean/Economic/EconomicDomain.lean`](Lean/Economic/EconomicDomain.lean). Each file below is a **lake** root; proofs **compose** existing gate, Landauer, and information theory lemmas (**no** new physics axioms).

| # | Module | Plain-English purpose |
|---|--------|------------------------|
| 1 | [`EconomicTemperature.lean`](Lean/Economic/EconomicTemperature.lean) | Relates a Shannon-style information rate to a Landauer-scale “economic temperature” bracket. |
| 2 | [`BurdenRecursionIsAdmissible.lean`](Lean/Economic/BurdenRecursionIsAdmissible.lean) | Shows a discrete burden update stays compatible with the thermodynamic gate when hypotheses hold. |
| 3 | [`StochasticBurdenExpectation.lean`](Lean/Economic/StochasticBurdenExpectation.lean) | Studies mean burden under symmetric noise and geometric decay of the deterministic part. |
| 4 | [`DynamicEpsilonCalibration.lean`](Lean/Economic/DynamicEpsilonCalibration.lean) | Maps observables into an entropy-margin parameter using the Landauer bridge under stated assumptions. |
| 5 | [`SelfReferentialEconomicTensor.lean`](Lean/Economic/SelfReferentialEconomicTensor.lean) | Packages contractive / iterated burden-style updates without paradoxical fixed-point logic. |
| 6 | [`NPVIsSpecialCaseOfThermodynamicBurden.lean`](Lean/Economic/NPVIsSpecialCaseOfThermodynamicBurden.lean) | Recovers ordinary discounted-sum behaviour when entropy cost is turned off. |
| 7 | [`HallucinationDetector.lean`](Lean/Economic/HallucinationDetector.lean) | Classical surrogate flag when adoption entropy crosses a user-set threshold (not semantic truth). |
| 8 | [`LowEntropyLieDetector.lean`](Lean/Economic/LowEntropyLieDetector.lean) | Classical surrogate relating dissipation margin to entropy slack — not deception detection in the wild. |
| 9 | [`CreativityBudget.lean`](Lean/Economic/CreativityBudget.lean) | Separates declared output cost from an explicit creative slack so benign exploration is not conflated with gate violation. |
| 10 | [`ThermodynamicUncertaintyCertificate.lean`](Lean/Economic/ThermodynamicUncertaintyCertificate.lean) | Bundles proved quantities into a certificate-style tuple for documentation, not a legal seal. |
| 11 | [`PhysicsConstrainedAI.lean`](Lean/Economic/PhysicsConstrainedAI.lean) | Stages “propose then gate-check” so imagination is not equated with admissible action. |
| 12 | [`EpistemicSensingModule.lean`](Lean/Economic/EpistemicSensingModule.lean) | Uses marginal / mutual-information bounds from `InfoTheory` under explicit distributions. |
| 13 | [`KleisliAdmissibilityComposition.lean`](Lean/Economic/KleisliAdmissibilityComposition.lean) | Re-exports or composes constitutional Kleisli lemmas for multi-step admissibility. |
| 14 | [`NuanceIsolator.lean`](Lean/Economic/NuanceIsolator.lean) | Splits classical “productive” vs “waste” cost lines for bookkeeping, not aesthetic judgment. |
| 15 | [`HorizonAwareGrounding.lean`](Lean/Economic/HorizonAwareGrounding.lean) | Compares short- vs long-horizon weights under hypotheses (no free lookahead oracle). |
| 16 | [`CollectiveCoherenceCost.lean`](Lean/Economic/CollectiveCoherenceCost.lean) | Adds a classical penalty term for multi-agent spread / disagreement, user-parameterised. |
| 17 | [`CreativeExplorationTolerance.lean`](Lean/Economic/CreativeExplorationTolerance.lean) | Allows a temporary high-dissipation window for exploration when hypotheses explicitly permit it. |

**Index of claims:** full cross-layer map in [`PROOF-STATUS.md`](PROOF-STATUS.md).

## Meso-scale features (high level)

- **Physics-constrained AI with an imagination sandbox** — propose freely in the model, then **gate-check** before treating output as admissible ([`PhysicsConstrainedAI.lean`](Lean/Economic/PhysicsConstrainedAI.lean)).
- **Classical surrogate flags** — “hallucination” and “low-entropy lie” names mean **explicit predicates** in [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md), not deployed AI safety products.
- **Nuance and creativity** — productive vs waste split ([`NuanceIsolator.lean`](Lean/Economic/NuanceIsolator.lean)); creative slack ([`CreativityBudget.lean`](Lean/Economic/CreativityBudget.lean)); exploration windows ([`CreativeExplorationTolerance.lean`](Lean/Economic/CreativeExplorationTolerance.lean)).
- **Horizon and collectives** — time-weighted tradeoffs ([`HorizonAwareGrounding.lean`](Lean/Economic/HorizonAwareGrounding.lean)); collective penalty ([`CollectiveCoherenceCost.lean`](Lean/Economic/CollectiveCoherenceCost.lean)).
- **Automatic visuals (GIF/PNG)** — `make visuals` or `python3 scripts/generate_visuals.py` ([`requirements-visuals.txt`](requirements-visuals.txt)); CI job **`visuals`**. Checked-in fixtures can illustrate **exponential decay** of burden-style series (pedagogical plots — not a claim about real markets or ML loss curves without separate data).

## Honest safety limits (read this before citing externally)

- This framework **measures dissipation-style costs** and **biases reasoning toward lower-dissipation paths** under the model — it does **not** define **moral truth**, **legal compliance**, or **factual correctness** of natural-language claims.
- **Truth and values** remain human, cultural, and goal-dependent. The Lean code says what follows **from explicit axioms and hypotheses**, not what society ought to do.
- Economic and “AI safety” **names are not certifications**. For quantum RCC, double-slit bridges, or deployment claims, follow [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md) and sibling [`umst-formal-double-slit`](https://doi.org/10.5281/zenodo.19159660).

## Layered architecture

| Layer | Repository | Role |
|--------|------------|------|
| **Quantum foundation** | **`umst-formal-double-slit`** | **59** lake roots, **537** `theorem` + **34** `lemma` (line-start, roots-only), **0** `sorry`, **1** axiom (`physicalSecondLaw`); complementarity, dephasing + stream-D limits, epistemic MI. Zenodo: [10.5281/zenodo.19159660](https://doi.org/10.5281/zenodo.19159660). Counts: sibling `README.md` / `PROOF-STATUS.md`. |
| **Meso-scale classical** | **`umst-formal` (this repo)** | Rational gate, Kleisli constitution, Shannon/Landauer bridge, and **`Lean/Economic/`** lemmas — **no** dependency on the double-slit package unless you add one. |

Both share the **single** project Lean **`axiom`** pattern documented in [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md) (`physicalSecondLaw`).

---

## Background

The **Unified Material-State Tensor (UMST)** is a framework for material state transitions. Core ideas:

- **Thermodynamic gate** — accepts or rejects a proposed transition using four constraints (mass, Clausius–Duhem, hydration, strength).
- **Naturality** — the gate is material-agnostic across material classes.
- **Constitutional sequences** — Kleisli-style composition of gate-checked steps with subject reduction.
- **Geometry** — admissible region as SDF / CSG; Helmholtz free energy as gradient field.
- **DIB cycle** — Discovery–Invention–Build as a monad with proved laws.

The Rust kernel (`umst-prototype-2a`) implements the gate. This repository proves consistency across **Agda, Coq, Lean 4, and Haskell QuickCheck**; Rust correspondence uses optional FFI tests.

## What this repository does not claim (scope guardrail)

This tree is a **standalone formal artifact**. Claims are exactly those in [`PROOF-STATUS.md`](PROOF-STATUS.md) with passing builds.

- **Mechanized:** gate invariants, naturality, Kleisli structure, SDF lemmas in scope, Landauer–Einstein fragment, and **`Lean/Economic/`** (classical meso-layer).
- **Not mechanized** unless listed: large ethical state spaces, informal “dignity” predicates, or any property absent from `PROOF-STATUS.md`.

[Docs/Architecture-Invariants.md](Docs/Architecture-Invariants.md) records how field observations informed constraints.

## What this repository proves (core invariants)

Four invariants, across all formal layers:

| # | Invariant | Physical meaning | Formal statement |
|---|-----------|------------------|------------------|
| 1 | Mass conservation | Density cannot jump discontinuously | Single-step mass gap bounded by `delta` (see `Gate.lean`) |
| 2 | Clausius–Duhem | Free energy must not increase (2nd law model) | `D_int = -rho * psi_dot >= 0` |
| 3 | Hydration irreversibility | Hydration cannot reverse | `alpha_new >= alpha_old` |
| 4 | Strength monotonicity | Undamaged concrete does not lose strength | `fc_new >= fc_old` |

## What is verified (index)

| Claim | Mechanized in |
|-------|----------------|
| Four gate invariants | `Agda/Gate.agda`, `Coq/Gate.v`, `Lean/Gate.lean`, `Haskell/UMST.hs` |
| Naturality | `Agda/Naturality.agda`, `Lean/Naturality.lean`, `Lean/Activation.lean` |
| Subject reduction; Kleisli admissibility | `Coq/Constitutional.v`, `Lean/Constitutional.lean` |
| Landauer–Einstein mass equivalent | `Coq/LandauerEinsteinBridge.v`, `Lean/LandauerEinsteinBridge.lean` |
| SDF / FRep; CSG; Eikonal | `Agda/Gate.agda §7`, `Agda/Helmholtz.agda §6`, `Lean/Helmholtz.lean`, `Haskell/SDFGate.hs` |
| Full Lean layer + Economic meso-scale | `Lean/` — **45** roots, **221** theorems + **17** lemmas; see [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md) |
| Haskell QuickCheck + sanity | **33** `prop_*` in [`Haskell/test/Test.hs`](Haskell/test/Test.hs); `cabal test landauer-einstein-sanity` — details in [`Haskell/README.md`](Haskell/README.md) and [`PROOF-STATUS.md`](PROOF-STATUS.md) § Cross-Layer Consistency |

See [`PROOF-STATUS.md`](PROOF-STATUS.md) for the complete per-theorem index (§ **Lean 4 Layer Summary** lists every lake root with theorem counts and flagship lemmas).

## Lean core (non-Economic) — module roles

The **22** Lean roots outside `Lean/Economic/` are summarized below; full counts and paths are in [`PROOF-STATUS.md`](PROOF-STATUS.md). All are **0** tactic `sorry` in the default closure.

| Module | Role (indicative) | Flagship identifiers |
|--------|-------------------|----------------------|
| `Gate` | `Admissible`, graded `AdmissibleN`, gate soundness / completeness | `admissibleN_compose`, `gateCheckSound` |
| `Helmholtz` | Concrete ψ model, SDF / Eikonal | `helmholtzGradient`, `helmholtzStateAdmissible` |
| `Constitutional` | N-step Kleisli, subject reduction | `kleisliFoldWellTypedN`, `kleisliComposeWellTypedN` |
| `Naturality` | Material-agnostic gate | `gateMaterialAgnostic`, `naturalitySquare` |
| `Activation` | Engine activations, sheaf-style sections | (see module) |
| `DIBKleisli` | DIB monad laws, semantic step vs `gateCheck` | `dibArtifactGateCheck_eq_true` |
| `FormalFoundations` | Corpus witness importing core stack | `umst_formal_complete` |
| `LandauerEinsteinBridge` | SI Landauer scale, `E=mc²` mass brackets | numeric bracket lemmas at 300 K |
| `GraphProperties` | Mass non-transitivity, DAG lemmas | `mass_not_transitive`, `admissibleTrans_refuted` |
| `Powers` | Powers gel-space ratio witness | `powersStateFcMonotone` |
| `Convergence` | Streams, Lyapunov-style bounds | `HydrationInUnitInterval`, `ConstitutionalStream` |
| `GaloisGate` | Galois connection on gate conditions | (see module) |
| `EnrichedAdmissibility` | Lawvere metric vs `AdmissibleN` | triangle-inequality lemmas |
| `LandauerLaw` | `T_LandauerLaw`; **only** project `axiom` `physicalSecondLaw` | `landauerBound` family |
| `InfoTheory` | Joint Shannon entropy, product joint laws | `marginalX_product`, `sumOne` |
| `EndConditions` | Terminal / end-state style constraints | (see module) |
| `MeasurementCost` | Observation cost layer | (see module) |
| `LandauerExtension` | n-bit scaling, temperature scaling | (see module) |
| `FiberedActivation` | `engineFiber`, universality | (see module) |
| `MonoidalState` | `combine` on ℚ states, convexity lemmas | `combine_one`, `combine_zero` |
| `SeparationBound` | Accuracy–safety separation (real line) | `accuracy_safety_separation_real` |

**Axiom / surrogate honesty:** [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md), [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md), [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md). **Count methodology:** [`Docs/COUNT-METHODOLOGY.md`](Docs/COUNT-METHODOLOGY.md).

### Documentation hub

| Document | Role |
|:---------|:-----|
| [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md) | Axioms, DIB audit, paper-claim map, AutoExperimenter boundary |
| [`PROOF-STATUS.md`](PROOF-STATUS.md) | Master cross-layer index; Lean roots table |
| [`Docs/COUNT-METHODOLOGY.md`](Docs/COUNT-METHODOLOGY.md) | How theorem/lemma counts are computed |
| [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md) | Surrogate predicates vs deployment claims |
| [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md) | Economic “detector” naming scope |
| [`Docs/PROOF-REPLAY.md`](Docs/PROOF-REPLAY.md) | Reproducible build / replay commands |

## Architecture

```
umst-formal/
├── Agda/                   Default `make check` (see Agda/Makefile)
│   ├── Gate.agda … Helmholtz.agda  (core + CSG / Eikonal)
│   ├── Naturality.agda, Activation.agda, DIB-Kleisli.agda
│   ├── InfoTheory.agda, MeasurementCost.agda
│   └── LandauerEinsteinTrace.agda  (traceability shell; proofs in Lean/Coq)
├── Coq/                    `make` → `.vo` + OCaml extraction
│   ├── Gate.v, Constitutional.v, LandauerEinsteinBridge.v
│   ├── InfoTheory.v, MeasurementCost.v
│   └── Extraction.v
├── Lean/                   Mathlib 4.14 — **39** `lakefile` roots (authoritative list: `lakefile.lean`)
│   ├── Gate … SeparationBound.lean   (22 non-Economic roots; see § Lean core above)
│   ├── Economic/*.lean               (18 files; 17 theorem roots + EconomicDomain)
│   ├── lakefile.lean, lean-toolchain
│   └── _check_ext.lean               (scratch — not a root)
├── Haskell/                See Haskell/README.md — 33 QuickCheck props + optional FFI
├── ffi-bridge/             C ABI to umst-core (no README; see PROOF-REPLAY.md)
├── scripts/                lean_declaration_stats.py, generate_visuals.py, …
├── visuals/, Makefile      `make lean-stats`, `make visuals`
├── Docs/                   PROOF-REPLAY, COUNT-METHODOLOGY, FALSIFIABILITY_DASHBOARD, roadmaps, …
├── PROOF-STATUS.md         Master cross-layer index
├── FORMAL_FOUNDATIONS.md   Axioms, audit, paper-claim map
└── SAFETY-LIMITS.md        Economic surrogate scope
```

### Layer relationships (specification → bridge → Rust)

```
┌─────────────────────────────────────────────────────────────────┐
│  Agda — specification                                           │
└──────────────┬──────────────────────────────────────────────────┘
               ▼
┌─────────────────────────────────────────────────────────────────┐
│  Coq — QArith proofs + OCaml extraction                         │
└──────────────┬──────────────────────────────────────────────────┘
               ▼
┌─────────────────────────────────────────────────────────────────┐
│  Haskell — QuickCheck + optional FFI to Rust                    │
└──────────────┬──────────────────────────────────────────────────┘
               ▼
┌─────────────────────────────────────────────────────────────────┐
│  ffi-bridge / umst-prototype-2a — executable gate               │
└─────────────────────────────────────────────────────────────────┘
```

### Categorical backbone (sketch)

Objects include `MaterialClass`, `ThermodynamicState`, `Bool`; the gate is a natural transformation on materialised state pairs; mass conservation is monoidal; DIB lives in a Kleisli category over state. See [Docs/OnePager-Categorical.tex](Docs/OnePager-Categorical.tex).

---

## Building

### Prerequisites

| Tool | Version | Purpose |
|------|---------|---------|
| Rust | 1.75+ | FFI bridge |
| Agda | 2.6.4+ | Proofs |
| Coq | 8.18+ | Proofs + extraction |
| Lean | 4.14.0 | Mathlib proofs |
| GHC / cabal | 9.6+ / 3.10+ | Haskell |

Full environment notes: **[Docs/PROOF-REPLAY.md](Docs/PROOF-REPLAY.md)**.

```bash
./scripts/check-formal-environment.sh   # optional

cd ffi-bridge && cargo build --release && cd ..
cd Agda && make check && cd ..
cd Coq && make && cd ..
cd Lean && lake build && cd ..
cd Haskell && cabal build lib:umst-formal -f -with-ffi && cabal test umst-properties -f -with-ffi && cd ..

# Optional: Rust ↔ Haskell (after ffi build)
cd Haskell && cabal test umst-ffi-correspondence -f with-ffi && cd ..

# Optional: Lean stats + visuals (from repository root)
make lean-stats
make visuals
```

## Contributing

We welcome corrections, proof refactors that **preserve** the layer graph, and documentation that tightens the line between **machine-checked** claims and **analogy**. Please:

- Run `cd Lean && lake build` before opening a PR that touches Lean.
- Run `python3 scripts/lean_declaration_stats.py` if you add roots; update [`PROOF-STATUS.md`](PROOF-STATUS.md), [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md), and [`scripts/expected_lean_declaration_snapshot.json`](scripts/expected_lean_declaration_snapshot.json) in the **same** commit when totals change (CI enforces the snapshot).
- Read [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md) before renaming or exporting “detector” modules.

**Zenodo:** this artifact is archived at [doi.org/10.5281/zenodo.18940933](https://doi.org/10.5281/zenodo.18940933); browse [zenodo.org](https://zenodo.org/) for versioned uploads and community collections. An **upcoming preprint** will align prose with the Economic layer — check the record’s **related identifiers** and the **Citation** block below for the latest bib entry.

## Extending (new material class)

1. **Agda:** extend `MaterialClass` / `ActivatedUMST` in `Activation.agda`.
2. **Coq:** mirror in `Gate.v`.
3. **Haskell:** `MaterialType` in `UMST.hs` and activation in `KleisliDIB.hs`.
4. **FFI:** unchanged if naturality still holds.

## Correspondence to the Rust kernel

Haskell QuickCheck compares the pure gate to Rust via FFI; Coq extraction supplies a second reference; Rust `KleisliArrow` tests mirror monad laws. See [`Haskell/test/Test.hs`](Haskell/test/Test.hs).

**Continuum engineering backlog (Θ / Σ / splat / CI)** is decomposed as **typed morphisms** (first-principles steps + a light λ-shaped planning vocabulary) in **`MaOS-Core/docs/CONTINUUM_GAP_REMEDIATION_PLAN.md`** §17 — same discipline as proofs: small total steps, explicit composition, effects at the rim.

## License

MIT. See [LICENSE](LICENSE).

## Citation

```
Shyamsundar, S., Shenbagamoorthy, S. P. (2026).
UMST-Formal: Categorical Verification of Physics-Gated Material State Transitions.
Zenodo. https://doi.org/10.5281/zenodo.18940933
```

Also cite the [**Thermodynamic Cost of Knowing**](https://doi.org/10.5281/zenodo.19159660) artifact when you rely on the quantum track.
