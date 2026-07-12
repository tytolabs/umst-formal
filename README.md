<!--
SPDX-License-Identifier: MIT
-->
<!-- markdownlint-disable-file MD013 MD040 MD001 MD026 — hero README is intentionally dense; other docs stay strict via shared config. -->

<div align="center">

# The Thermodynamic Cost of Acting

### `umst-formal` — acting / economic-admissibility formal fiber

> _This ecosystem is dedicated to the thousands of unnamed contributors who wrote formal proofs, maintained open-source compilers, and built mathematical libraries for years — often without evidence that any of it would be used beyond pure theory. They chose to make their work free, because they understood that knowledge about physical reality cannot be owned. Whatever this system achieves is yours._

### Every proposed transition is a claim on coherence. The gate answers in the negative as often as the model demands. What survives is what the inequalities allow.

**What it is.** Machine-checked formalizations (Lean 4 · Agda · Coq · Haskell QuickCheck) of the **thermodynamic admissibility gate** for **acts and commitments** — rational state changes, Shannon/Landauer bookkeeping, and Kleisli composition of gate-checked steps. This is a **proof tree**, not a runtime solver and not an MCP host.

**The gate idea.** A proposed transition is admissible only if mass/density and free-energy (Clausius–Duhem) constraints hold under explicit hypotheses — structural accept/reject in logic, not a soft penalty at inference time.

**Honest is / isn't.** **Is:** lake-rooted Lean modules with declared theorem/lemma counts, cross-layer gate mirrors, Economic meso-layer predicates. **Isn't:** live inference on a robot, MCP tools, or “seeing the world.” Economic filenames that sound like oracles are **parameterised predicates** — read [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md) before citing them off-repo.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18940933.svg)](https://doi.org/10.5281/zenodo.18940933)
<!-- readme:status -->
[![CI](https://github.com/tytolabs/umst-formal/actions/workflows/ci.yml/badge.svg)](https://github.com/tytolabs/umst-formal/actions/workflows/ci.yml)
[![CI — Lean](https://github.com/tytolabs/umst-formal/actions/workflows/lean.yml/badge.svg)](https://github.com/tytolabs/umst-formal/actions/workflows/lean.yml)
[![CI — Haskell](https://github.com/tytolabs/umst-formal/actions/workflows/haskell.yml/badge.svg)](https://github.com/tytolabs/umst-formal/actions/workflows/haskell.yml)
[![CI — Formal (Agda+Coq)](https://github.com/tytolabs/umst-formal/actions/workflows/formal.yml/badge.svg)](https://github.com/tytolabs/umst-formal/actions/workflows/formal.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-black.svg)](LICENSE)

</div>

### Shared stack (matter · knowing · acting · time)

These public repos share **one** thermodynamic admissibility gate, applied across domains:

| Domain | Public repo | Role |
|:---|:---|:---|
| **Matter** | [`umst-manifold`](https://github.com/tytolabs/umst-manifold) + [`umst-concrete-cartridge`](https://github.com/tytolabs/umst-concrete-cartridge) | DEC carrier + cementitious constitutive law |
| **Knowing** | [`umst-formal-double-slit`](https://github.com/tytolabs/umst-formal-double-slit) | Observation / measurement-cost formal fiber |
| **Acting** | **this repo** ([`umst-formal`](https://github.com/tytolabs/umst-formal)) **← you are here** | Economic-admissibility formal fiber |
| **Time** | [`umst-ucrs`](https://github.com/tytolabs/umst-ucrs) | Temporal witness / stamp spine |

Sibling links only — no paper-series arc naming in this README. Already-public per-repo DOI badges stay where they exist.

### What this is, in plain words

Knowing (observation cost) is mechanised in the sibling double-slit fiber. **Acting** is this tree: once you propose a state change, the formal layer asks whether that change is **admissible** under mass and dissipation constraints, and how Shannon/Landauer-style costs compose along Kleisli sequences of gate-checked steps. Optimism is not an axiom.

### Real objects (categorical — not “the proofs”)

| Symbol | Role | Defined at |
|:---|:---|:---|
| `ThermodynamicSystem K S` | Objects: states with density + free energy over scalar field `K` | [`Lean/Core/State.lean:9`](Lean/Core/State.lean) |
| `CoreAdmissible K S` | 1-step morphism: mass metric ball + free-energy descent | [`Lean/Core/Gate.lean:23`](Lean/Core/Gate.lean) |
| `CoreAdmissibleN` | N-step mass-budget path | [`Lean/Core/Gate.lean:29`](Lean/Core/Gate.lean) |
| `KleisliArrow` / `WellTyped` / `kleisliCompose` | Kleisli morphisms that only fire when the step is admissible | [`Lean/Core/Constitutional.lean:9–32`](Lean/Core/Constitutional.lean) |
| `econ_kleisliComposeWellTypedN` | Economic-layer re-export of graded Kleisli composition | [`Lean/Economic/KleisliAdmissibilityComposition.lean:14`](Lean/Economic/KleisliAdmissibilityComposition.lean) |
| Compat `Admissible` | Legacy cement cartridge alias over `ConcreteAdmissible` | [`Lean/Compat/Gate.lean:15`](Lean/Compat/Gate.lean) |

Port detail across Core / Concrete / Compat: [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md).

### Performance honesty

This repository is a **machine-checked proof artifact**. It does **not** run on the manifold hot arena path and it does **not** host MCP. Runtime gating and cold-edge agent tools live in [`umst-manifold`](https://github.com/tytolabs/umst-manifold) / [`umst-concrete-cartridge`](https://github.com/tytolabs/umst-concrete-cartridge). Agents **consume** this fiber via the manifold catalog lock export — they do not `lake build` mid-inference.

### Honesty ledger (counts @ `4132be0`)

**One status pointer for Economic naming risk:** [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md). Foundations / axiom story: [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md). Claim index: [`PROOF-STATUS.md`](PROOF-STATUS.md).

**Lean 4 (default lake roots)** — paste from `python3 scripts/lean_declaration_stats.py` on `origin/main` @ **`4132be0`** (2026-07-12):

```text
Repository: umst-formal
Lake roots: 62 modules
Roots-only:  289 theorem, 24 lemma, total 313
All Lean/*:  296 theorem, 24 lemma, total 320
Axioms (^axiom ):
  LandauerLaw.lean:155  physicalSecondLaw
```

- **0** tactic `sorry` in the default rooted closure (see module headers / CI).
- **1** project `axiom`: `physicalSecondLaw` in [`Lean/LandauerLaw.lean:155`](Lean/LandauerLaw.lean).
- After `lake build`, CI runs **`scripts/check_print_axioms.sh`** (Mathlib axiom baseline on headline cartridge-anchor theorems). Paste (same SHA):

```text
check_print_axioms: OK (all closures ⊆ Mathlib baseline + optional physicalSecondLaw)
```

Counts must match [`PROOF-STATUS.md`](PROOF-STATUS.md) and the pasted script output above (62 / 289 / 24). **Script wins** on any mismatch. Methodology: [`Docs/COUNT-METHODOLOGY.md`](Docs/COUNT-METHODOLOGY.md).

**Strengthen — do not soften:** Economic modules are **parameterised predicates**. They do not see the world. They do not certify moral truth, legal compliance, or factual correctness of natural-language claims ([`SAFETY-LIMITS.md`](SAFETY-LIMITS.md)). Soften none of those limits.

### Quick verify

```bash
git checkout 4132be0   # or origin/main
python3 scripts/lean_declaration_stats.py
# after lake build:
bash scripts/check_print_axioms.sh
cd Lean && lake build
```

---

## Economic intuition (plain language)

Growth can outrun friction in the stories people tell. The formal layer does not endorse those stories. It **binds** them: **`Lean/Economic/`** writes burden and information as **classical** quantities and keeps surrogate alarms explicit — thresholds and margins, not black-box “detectors” ([`SAFETY-LIMITS.md`](SAFETY-LIMITS.md), [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md)).

## Seventeen Economic modules — one sentence each

Shared scaffolding lives in [`Lean/Economic/EconomicDomain.lean`](Lean/Economic/EconomicDomain.lean). Each file below is a **lake** root; proofs **compose** existing gate, Landauer, and information theory lemmas (**no** new physics axioms beyond the single project axiom above).

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
- Economic and “AI safety” **names are not certifications**. For observation-cost formalizations, see sibling [`umst-formal-double-slit`](https://github.com/tytolabs/umst-formal-double-slit) (public DOI kept on that artifact). Deployment / surrogate claims: [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md).
- Soften **none** of the above. Prefer under-claiming.

## Shared stack vs this fiber

This repo is the **Acting** row of the gate-spine table above. It does **not** depend on the double-slit package unless you add a dependency. Both fibers share the single project Lean **`axiom`** pattern documented in [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md) (`physicalSecondLaw`). Sibling lake-root counts for Knowing live in that sibling’s README / `PROOF-STATUS.md` (do not hardcode here).

---

## Background

The **Unified Material-State Tensor (UMST)** is a framework for material state transitions. Core ideas:

- **Thermodynamic admissibility gate** — accepts or rejects a proposed transition using mass and Clausius–Duhem (and cartridge-specific constitutive) constraints.
- **Naturality** — the gate is material-agnostic across material classes.
- **Constitutional sequences** — Kleisli-style composition of gate-checked steps with subject reduction.
- **Geometry** — admissible region as SDF / CSG; Helmholtz free energy as gradient field.
- **DIB cycle** — Discovery–Invention–Build as a monad with proved laws.

Optional Rust FFI correspondence tests exist; this repository’s primary deliverable remains the formal layers (Agda, Coq, Lean 4, Haskell QuickCheck).

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
| Four gate invariants | `Agda/Gate.agda`, `Coq/Gate.v`, `Lean/Compat/Gate.lean` + `Lean/Concrete/Gate.lean`, `Haskell/UMST.hs` |
| Naturality | `Agda/Naturality.agda`, `Lean/Naturality.lean`, `Lean/Concrete/Activation.lean` |
| Subject reduction; Kleisli admissibility | `Coq/Constitutional.v`, `Lean/Core/Constitutional.lean`, `Lean/Compat/Constitutional.lean` |
| Landauer–Einstein mass equivalent | `Coq/LandauerEinsteinBridge.v`, `Lean/LandauerEinsteinBridge.lean` |
| SDF / FRep; CSG; Eikonal | `Agda/Concrete/Helmholtz.agda`, `Lean/Concrete/Helmholtz.lean`, `Haskell/SDFGate.hs` |
| Full Lean layer + Economic meso-scale | `Lean/` — **62** roots, **289** theorems + **24** lemmas; see [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md) |
| Haskell QuickCheck + sanity | **33** `prop_*` in [`Haskell/test/Test.hs`](Haskell/test/Test.hs); `cabal test landauer-einstein-sanity` — details in [`Haskell/README.md`](Haskell/README.md) and [`PROOF-STATUS.md`](PROOF-STATUS.md) § Cross-Layer Consistency |

See [`PROOF-STATUS.md`](PROOF-STATUS.md) for the complete per-theorem index (§ **Lean 4 Layer Summary** lists every lake root with theorem counts and flagship lemmas).

## Lean core (non-Economic) — Science Cartridge layout

The **40** Lean roots outside `Lean/Economic/` use **Core / Concrete / Compat** (see [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md)). All are **0** tactic `sorry` in the default closure.

| Layer | Modules | Role |
|-------|---------|------|
| **Core** | `Core.State`, `Core.Gate`, `Core.Constitutional` | Universal `ThermodynamicSystem`, `AdmissibleSystem`, `δMass`, generic graded Kleisli |
| **Concrete** | `Concrete.State`, `Concrete.Gate`, `Concrete.Helmholtz`, `Concrete.Powers`, `Concrete.Convergence`, `Concrete.GraphProperties`, `Concrete.Activation`, `Concrete.EndConditions`, `Concrete.EnrichedAdmissibility`, `Concrete.GaloisGate` | OPC cement cartridge: `Q_hyd`, `helmholtz`, `ConcreteAdmissible`, constitutive witnesses |
| **Compat** | `Compat.Gate`, `Compat.Constitutional` | Legacy `UMST` names (`ThermodynamicState`, `Admissible`, `gateCheck`, `makeGateArrow`) |
| **Universal extensions** | `Naturality`, `DIBKleisli`, `LandauerLaw`, `LandauerEinsteinBridge`, `DEC`, `Adjoint`, … | Material-agnostic or cross-cartridge lemmas |

Flagship identifiers: `admissibleN_compose`, `gateCheckSound`, `kleisliFoldWellTypedN`, `ψAntitoneHelmholtz`, `powers_monotone`, `hydrationConverges`.

| Module | Role | Flagship |
|--------|------|----------|
| `EtaCog` | MI-per-Joule cockpit metric | `eta_cog_nonneg` |
| `RhoEstimator` | Gaussian ρ–MI in bits | `rho_based_mi_formula` |
| `MedianConvergence` | `N_warmup` ceiling / empirical CDF tail | (see module) |
| `OrderStatisticsBand` | Quantile band / split-sample inequality | (see module) |
| `Memory.MergeSafe` | Merge-safe memory policy | (see module) |
| `Memory.TierDisjoint` | Tier-disjointness | (see module) |
| `DEC` | Triangle DEC / discrete Stokes witness | `discrete_stokes`, `hodge_laplacian_symmetric` |
| `Adjoint` | Linear adjoint vs terminal gradient (matrix exp) | `adjoint_recovers_gradient` |
| `RegimeSoundness` | Rational hyperbox regime vs warnings | `warnings_empty_iff_in_regime` |
| `JenningsGelSpace` | Jennings–Brownyard gel-space strength | `jennings_strength_monotone` |

**Axiom / surrogate honesty:** [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md), [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md), [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md). **Count methodology:** [`Docs/COUNT-METHODOLOGY.md`](Docs/COUNT-METHODOLOGY.md).

### Documentation hub

| Document | Role |
|:---------|:-----|
| [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md) | Axioms, DIB audit, paper-claim map, AutoExperimenter boundary |
| [`PROOF-STATUS.md`](PROOF-STATUS.md) | Master cross-layer index; Lean roots table |
| [`Docs/COUNT-METHODOLOGY.md`](Docs/COUNT-METHODOLOGY.md) | How theorem/lemma counts are computed |
| [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md) | Surrogate predicates vs deployment claims |
| [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md) | Economic “detector” naming scope |
| [`Docs/PROOF-REPLAY.md`](Docs/PROOF-REPLAY.md) | Reproducible build / replay commands (`check_print_axioms.sh`, stats, link check) |

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
├── Lean/                   Mathlib 4.14 — **62** `lakefile` roots (authoritative list: `lakefile.lean`)
│   ├── Gate … JenningsGelSpace.lean  (33 non-`Economic.*` roots incl. FPD, `Memory.*`, cartridge anchors)
│   ├── Economic/*.lean               (18 `Economic.*` theorem roots + `EconomicDomain` definitions)
│   ├── lakefile.lean, lean-toolchain
│   └── _check_ext.lean               (scratch — not a root)
├── Haskell/                See Haskell/README.md — 33 QuickCheck props + optional FFI
├── ffi-bridge/             C ABI to umst-core (no README; see PROOF-REPLAY.md)
├── scripts/                lean_declaration_stats.py, check_print_axioms.sh, generate_visuals.py, …
├── visuals/, Makefile      `make lean-build`, `make lean-stats`, `make lean-print-axioms`, `make visuals`
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
│  Optional FFI correspondence (Rust gate executable — not this proof tree) │
└─────────────────────────────────────────────────────────────────────────────┘
```

Lean sits beside Agda/Coq as a first-class machine-checked layer (not shown as a sequential “after Haskell” step). This diagram is pedagogical — it does **not** mean Lean proofs run on the inference path.

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

# Optional: Lean stats + cartridge-anchor axiom baseline + visuals (from repository root)
make lean-stats
make lean-print-axioms
make visuals
```

## Contributing

We welcome corrections, proof refactors that **preserve** the layer graph, and documentation that tightens the line between **machine-checked** claims and **analogy**. Please:

- Run `cd Lean && lake build` before opening a PR that touches Lean; optionally `make lean-print-axioms` after a successful build to match CI’s Mathlib-baseline gate on headline cartridge theorems.
- Run `python3 scripts/lean_declaration_stats.py` if you add roots; update [`PROOF-STATUS.md`](PROOF-STATUS.md), [`FORMAL_FOUNDATIONS.md`](FORMAL_FOUNDATIONS.md), and [`scripts/expected_lean_declaration_snapshot.json`](scripts/expected_lean_declaration_snapshot.json) in the **same** commit when totals change (CI enforces the snapshot).
- Read [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md) before renaming or exporting “detector” modules.

**Zenodo:** this artifact is archived at [doi.org/10.5281/zenodo.18940933](https://doi.org/10.5281/zenodo.18940933). Browse [zenodo.org](https://zenodo.org/) for versioned uploads.

## Extending (new material class)

1. **Agda:** extend `MaterialClass` / `ActivatedUMST` in `Activation.agda`.
2. **Coq:** mirror in `Gate.v`.
3. **Haskell:** `MaterialType` in `UMST.hs` and activation in `KleisliDIB.hs`.
4. **FFI:** unchanged if naturality still holds.

## Correspondence to the Rust kernel

Haskell QuickCheck compares the pure gate to Rust via FFI; Coq extraction supplies a second reference; Rust `KleisliArrow` tests mirror monad laws. See [`Haskell/test/Test.hs`](Haskell/test/Test.hs).

**Continuum engineering backlog** items (if any) live outside this public formal tree — do not treat them as mechanized claims here.

## License

MIT. See [LICENSE](LICENSE).

## Citation

```
Shyamsundar, S., Shenbagamoorthy, S. P. (2026).
UMST-Formal: Categorical Verification of Physics-Gated Material State Transitions.
Zenodo. https://doi.org/10.5281/zenodo.18940933
```

Also cite the sibling observation-cost formal artifact ([DOI 10.5281/zenodo.19159660](https://doi.org/10.5281/zenodo.19159660)) when you rely on that fiber.
