# Proof Status

This document maps every formal claim about the Unified Material-State
Tensor (UMST) mechanized **in this repository** to its machine-checked proof
artefact. It is the primary index for the `umst-formal` artifact.

**Maintainer QA (optional):** Layer 0–5 documentation closure, execution log, and Rust/Continuum honesty boundary — [`Docs/DOCUMENTATION-COVERAGE-PLAN.md`](Docs/DOCUMENTATION-COVERAGE-PLAN.md). Per product choice, that file is **not** linked from [`README.md`](README.md); open it from `Docs/` when auditing coverage.

## Scope boundary (mechanized vs not in this artifact)

This repository is a **standalone mathematical artifact**: it mechanizes **gate
invariants, naturality, constitutional sequence composition**, the **Landauer–Einstein
mass-equivalent fragment** (Coq/Lean), and related lemmas.  Anything **not** listed
in this file as mechanized or as a named axiom/postulate is **out of scope** for this
repository—regardless of narratives elsewhere in the MaOS / UMST ecosystem.

| Status | Meaning in this repo |
|---|---|
| Mechanized | Machine-checked theorem/proof exists in Agda/Coq/Lean (or computational test in Haskell where noted), plus build command |
| Structural | Property follows by construction / pattern matching in the formal model |
| Not in this artifact | No theorem or axiom bundle here; do not infer provability from this repo alone |

### Outside the mechanized core (no formal artifact here)

The following are **not** represented as theorems in this repository (unless and until
dedicated modules and `PROOF-STATUS` rows are added):

- Axiological veto semantics over large ethical/cultural state spaces.
- Axiological **“dignity floor”** framing and **humour modulus** as formal predicates (distinct from the mechanized thermodynamic–epistemic dignity scalar in `Lean/Dignity.lean`; see Phase N3-FPD-a in `PROOF-STATUS.md`).
- Full autopoietic / cultural-closure semantics beyond the DIB abstract interface.
- End-to-end certification of arbitrary external runtime or narrative claims.

This list is **descriptive** (current coverage), not a forecast of what is true in nature.

**Proof layers:**

| Layer | Tool | Build command | Status |
|-------|------|---------------|--------|
| Agda | Agda 2.8 + bundled stdlib (Homebrew) or 2.6.4+ | `cd Agda && make check` | Physical postulates in `Gate.agda` (see key); `InfoTheory.agda` (definitions + 3 postulates mirroring Lean/Coq product laws; small length lemmas proved); default `make check` is not `--safe` |
| Coq / Rocq | Rocq 9 / Coq 8.18 + QArith | `cd Coq && make` | No `Admitted`; `admissible_trans` REMOVED (refutable); replaced by graded `admissible_N_compose`; `InfoTheory.v` (product joint, `joint_mass_product`, both marginals as `Forall2 Qeq`, incl. `marginal_second_product` / normalized corollary) |
| Lean 4 | Lean 4.14+ + Mathlib4 | `cd Lean && lake build` | No tactic `sorry`; `admissibleTrans` REMOVED; graded `admissibleN_compose` across **47** `UMST` library roots (`Lean/lakefile.lean`), including **`Lean/Economic/`** (classical Shannon/Landauer + burden lemmas; see `SAFETY-LIMITS.md`). Counts: **226** `theorem` + **17** `lemma` (line-start, roots only) — run `python3 scripts/lean_declaration_stats.py` from **`umst-formal/`**. See `FORMAL_FOUNDATIONS.md` / `Docs/COUNT-METHODOLOGY.md`. |
| Haskell | GHC 9.6+ (tested 9.14) + QuickCheck | `cd Haskell && cabal test umst-properties -f -with-ffi` | **62** properties (gate, SDF, InfoTheory, Landauer, monoidal state, burden/stochastic drift, Economic-layer mirrors, **CreditGreedy**, **Dignity**, **EtaCog**, **RhoEstimator**, **MedianConvergence**, **OrderStatisticsBand**); plus `cabal test landauer-einstein-sanity` (Rational check vs Lean tight bracket) |
| Haskell ↔ Rust | same + `libumst_ffi` | `cd ffi-bridge && cargo build --release` then `cd Haskell && cabal test umst-ffi-correspondence -f with-ffi` | Fixed scenarios via `FFI.runCorrespondenceTests` (gate + credit + **Dignity** + **η_cog** + **ρ-MI bits** + **`umst_n_warmup`** + **`umst_n_quantile`** correspondence; optional suite). **No `LD_LIBRARY_PATH` required** when the `umst-ffi-correspondence` test stanza embeds `rpath` to `umst-formal/target/release` (GHC 9.10.3 verified). **Fragility:** `$ORIGIN`-relative depth is layout-sensitive; canonical portable fix = `build-tool-depends` pre-test `.so` copy (**Phase N-hygiene-ffi**, scheduled). |

**Legend:**

| Symbol | Meaning |
|--------|---------|
| `proved` | Machine-checked proof, no gaps |
| `postulate` | Physical axiom (constitutive law, not a logical hole; see note) |
| `structural` | Holds by construction / pattern matching |
| `by ring` | Closed by the `ring` or `nlinarith` tactic |
| `--` | Not applicable in this layer |

**Note on postulates:** Agda's `ψ-antitone` and `fc-monotone` are *physical
model axioms* encoding cement chemistry (Clausius-Duhem, Powers model).  They
are not logical gaps — they are interface specifications.  The concrete
arithmetic witness for `ψ-antitone` is fully proved in `Coq/Gate.v`
(helmholtz_antitone, §8) and `Lean/Gate.lean` (helmholtzAntitone).  The
concrete witness for Helmholtz-consistent states is in `Agda/Helmholtz.agda`
(`helmholtz-antitone`) and `Lean/Helmholtz.lean` (`helmholtzStateAdmissible`).

---

## Complete Axiom / Postulate Inventory

Every `Axiom` (Coq/Lean), `postulate` (Agda), or `opaque` abstract type is
listed below with its classification. **No hidden assumptions exist outside
this table.**

### Physical model axioms (constitutive laws, not logical gaps)

| Declaration | Coq | Agda | Lean | Classification |
|---|---|---|---|---|
| Free-energy antitone under hydration | `psi_antitone` (Gate.v) | `ψ-antitone` (Gate.agda) | `helmholtzAntitone` (Gate.lean); state witness `ψAntitoneHelmholtz` (Helmholtz.lean) — **not** a Lean `axiom` | Clausius-Duhem / Helmholtz model |
| Strength monotone under hydration | `fc_monotone` (Gate.v) | `fc-monotone` (Gate.agda) | `powersStateFcMonotone` (Powers.lean) — **not** a Lean `axiom` | Powers gel-space ratio model |
| Second Law of Thermodynamics (erasure) | -- | -- | `physicalSecondLaw` + `physicalSecondLawUniformBinary` (LandauerLaw.lean) | T_LandauerLaw only; Clausius entropy form; uniform-binary binders use `physicalSecondLawUniformBinary proc` (Lean parse) |

### Composition / transitivity (RESOLVED — axiom removed)

The former `admissibleTrans` / `admissible_trans` axiom has been **removed** from the
Lean and Coq layers.  It was **refutable**: two consecutive 99 kg/m³ density jumps
satisfy the single-step mass bound (`|99| ≤ 100`), but the composed gap (`|198| > 100`)
violates it.  Formal counterexample: `GraphProperties.lean` (`mass_not_transitive`,
`admissibleTrans_refuted`).

**Replacement (proved, no axiom):**

| Declaration | Lean | Coq | Haskell QC | Classification |
|---|---|---|---|---|
| Graded admissibility | `AdmissibleN n` (Gate.lean §10) | `admissible_N` (Constitutional.v) | -- | Structure indexed by step count n |
| Graded composition | `admissibleN_compose` (Gate.lean §10) | `admissible_N_compose` (Constitutional.v) | -- | Proved via triangle inequality |
| 0-step identity | `admissibleNRefl 0` (Gate.lean §10) | `admissible_N_refl` (Constitutional.v) | -- | Proved |
| General Kleisli composition | `kleisliComposeWellTypedN` (Constitutional.lean) | `kleisli_compose_well_typed_N` (Constitutional.v) | -- | m+n-step graded |
| N-step Kleisli | `kleisliFoldWellTypedN` (Constitutional.lean) | `kleisli_fold_well_typed_N` (Constitutional.v) | -- | WellTypedN n; no axiom |
| Mass non-transitivity | `mass_not_transitive` (GraphProperties.lean) | -- | `prop_mass_not_transitive` | Formal counterexample |
| Accuracy–safety separation (per-sample $L^1$ / MAE core) | `accuracy_safety_separation_real`, `accuracy_safety_separation_real_symm` (SeparationBound.lean) | -- | -- | Triangle inequality on ℝ |

### Agda postulates (pending mechanization / abstract interfaces)

| Declaration | File | Classification |
|---|---|---|
| `helmholtz-linear` | Helmholtz.agda | Proved in Coq (`helmholtz_additive`) and Lean (`helmholtzAdditive`) |
| `helmholtz-gradient-const` | Helmholtz.agda | Proved in Coq (`helmholtz_gradient`) and Lean (`helmholtzGradient`) |
| `stateAfter` | Naturality.agda | Abstract functor G (material → post-step state) |
| `DIBState`, `Observation`, `Insight`, `Design`, `Artifact` | DIB-Kleisli.agda | Abstract phase types for the DIB monad |
| `discover`, `invent`, `build` | DIB-Kleisli.agda | Abstract Kleisli arrows (pipeline phases) |
| `funext` | DIB-Kleisli.agda | Function extensionality (standard meta-axiom) |
| `engine-produces-state` | Activation.agda | Abstract engine-to-state-transformer interface |
| `jointMassProduct`, `marginalFirstProduct`, `marginalSecondProduct` | InfoTheory.agda | **Algebraic laws** for product joint / marginals: proved in Lean (`InfoTheory.lean`) and Coq (`InfoTheory.v`); Agda keeps definitions + postulates for cross-language parity |

### Lean opaque / synthetic carriers (DIB; matching Agda postulates)

| Declaration | File | Classification |
|---|---|---|
| `DIBState` (opaque) | DIBKleisli.lean | Abstract state type |
| `Observation`, `Insight`, `Design`, `Artifact` (`structure`, `Inhabited`) | DIBKleisli.lean | Synthetic phase types (not Lean `axiom`) |
| `discover`, `invent`, `build` (noncomputable opaque) | DIBKleisli.lean | Abstract Kleisli arrows |

### Not formalized in this repository

No machine-checked definitions/theorems for the following **as stated in continuum /
gravitational / cosmological theories** (this is not a claim that they are false).
For **precise** logical status — not expressible in the core signature **L₀** vs
derivable in a named extension **T_ext** — see `Docs/FORMAL-PHYSICS-DERIVATION-PLAN.md`:

- Jacobson-style field-theoretic derivation of thermodynamic identities
- Holographic / Bekenstein-type area-law entropy bounds as theorems in a chosen spacetime axiom system
- Landauer’s bound as a **theorem** for a class of physical erasure processes (irreversibility packaged in a full thermodynamic formalization)
- Friedmann equations / stress–energy ansätze involving information density
- Identification of the mass-equivalent `m_eq` below with **measured** gravitational effects of “information” as a substance hypothesis beyond `E = mc²` applied to the defined energy

**In-repo thermodynamics (for comparison):** the **gate** layer already includes a
**Clausius–Duhem dissipation inequality** and Helmholtz-based constitutive axioms
(`Gate.v` / `Gate.lean` / `Gate.agda`). That is the **material-state** formalization
in this artifact; it does **not** subsume the continuum items above unless explicitly
linked in a future module.

### Phase M4 — credit aggregate (Case A), 2026-04-20

| Theorem (primary) | Module path | proof-status | Dependencies | Date | Informal statement |
|---|---|---|---|---|---|
| `credit_greedy_optimal` | `UMST.Formal.CreditGreedy` (`Lean/CreditGreedyOptimal.lean`) | **FORMAL** | `Mathlib.Data.Real.Basic`, `Mathlib.Algebra.BigOperators.Group.List`, `Mathlib.Algebra.Order.BigOperators.Group.List` | 2026-04-20 | Greedy admissible-mass scan equals exhaustive sum over the same per-candidate admissibility predicate (no matching constraint). |

### Phase N3-FPD-a — thermodynamic–epistemic dignity, 2026-04-20

| Theorem (primary) | Module path | proof-status | Dependencies | Date | Informal statement |
|---|---|---|---|---|---|
| `dignity_monotone_under_mi_gain` | `UMST.Formal.Dignity` (`Lean/Dignity.lean`) | **FORMAL** | `LandauerEinsteinBridge` (`landauerBitEnergy`), `Mathlib` order/tactics, list sums where used | 2026-04-20 | Dignity in `[0, d_max]` with Landauer-gated `dignity_step`: honest spend (energy ≥ `landauerBitEnergy T` per claimed MI bit) preserves or increases value; sub-Landauer claims do not increase it; convex combination and list sums stay nonnegative; RCC-style link (`dignity_scalar_matches_rcc_one_minus_epistemic_gap`) ties the scalar to residual-coherence bookkeeping. |

### Phase N3-FPD-b — MI-per-Joule η_cog (cockpit metric), 2026-04-21

| Theorem (primary) | Module path | proof-status | Dependencies | Date | Informal statement |
|---|---|---|---|---|---|
| `eta_cog_nonneg` | `UMST.Formal.EtaCog` (`Lean/EtaCog.lean`) | **FORMAL** | `UMST.Formal.Dignity` (`Dignity.lean`, `landauer_joules_per_bit`), `Mathlib` ordered-field lemmas; ecosystem narrative cross-ref: `umst-formal-double-slit/Lean/LandauerBound.lean`, `InformationCostIdentity.lean` (same SI Landauer scale, not imported in this lake closure) | 2026-04-21 | `η_cog d c = d.value · ΔMI / (ΔE + k_B T ln 2)` — denominator **(i)** (single-bit floor per COCKPIT_DESIGN_BRIEF §5 / §14bis.b N3). Nonnegativity, monotonicity in dignity and MI, antitone in dissipated energy, saturation at `ΔE = 0`, list aggregation, and equality of η under dishonest `dignity_step` (dignity freeze) so deception cannot inflate the dignity-weighted channel. |

### Phase FPD-RhoEstimator — Gaussian ρ-MI (Tier 2), 2026-04-21

| Theorem (primary) | Module path | proof-status | Dependencies | Date | Informal statement |
|---|---|---|---|---|---|
| `rho_based_mi_formula` | `UMST.Formal.RhoEstimator` (`Lean/RhoEstimator.lean`) | **FORMAL** | `Mathlib.Analysis.SpecialFunctions.Log.Base`, `Mathlib.Data.Real.Basic` | 2026-04-21 | Bivariate Gaussian MI in bits: `−½ log₂(1−ρ²)` on `ρ² < 1`; nonnegativity, monotonicity in \|ρ\|, value at `ρ = 0`, boundedness below a fixed `\|ρ_max\| < 1`, and a classical nonnegative plug-in variance envelope `(1−ρ²)²/n`. |

### New theorems (Phase 0-2, 2026-03-19)

| Declaration | File | Classification |
|---|---|---|
| `AdmissibleN n` | `Lean/Gate.lean` §10 | Graded admissibility structure |
| `admissibleN_compose` | `Lean/Gate.lean` §10 | Proved (triangle inequality) |
| `admissible_iff_admissibleN1` | `Lean/Gate.lean` §10 | Proved (ring/simp) |
| `admissibleNRefl n` | `Lean/Gate.lean` §10 | Proved |
| `WellTypedN n` | `Lean/Constitutional.lean` | Definition |
| `kleisliComposeWellTypedN` | `Lean/Constitutional.lean` | Proved |
| `kleisliFoldWellTypedN` | `Lean/Constitutional.lean` | Proved |
| `mass_not_transitive` | `Lean/GraphProperties.lean` | Proved (norm_num) |
| `admissibleTrans_refuted` | `Lean/GraphProperties.lean` | Proved (norm_num) |
| `dissipCond_transitive` | `Lean/GraphProperties.lean` | Proved (le_trans) |
| `hydratCond_transitive` | `Lean/GraphProperties.lean` | Proved (le_trans) |
| `strengthCond_transitive` | `Lean/GraphProperties.lean` | Proved (le_trans) |
| `hydration_acyclic` | `Lean/GraphProperties.lean` | Proved (linarith) |
| `powers_monotone` | `Lean/Powers.lean` | Proved (nlinarith) |
| `PowersState` | `Lean/Powers.lean` | Definition (w/c-indexed) |
| `powersStateAdmissible` | `Lean/Powers.lean` | Proved |
| `hydrationConverges` | `Lean/Convergence.lean` | Proved (Monotone Convergence) |
| `freeEnergyConverges` | `Lean/Convergence.lean` | Proved (Monotone Convergence) |
| `lyapunov_nondecreasing` | `Lean/Convergence.lean` | Proved |
| `massDist`, `massDist_triangle` | `Lean/EnrichedAdmissibility.lean` | Proved (abs_add) |
| `OrderAdmissible`, `orderAdmissible_trans` | `Lean/EnrichedAdmissibility.lean` | Proved |
| `admissibleN_decomp`, `admissibleN_mono` | `Lean/EnrichedAdmissibility.lean` | Proved |
| `condMeet_full_iff_admissible` | `Lean/GaloisGate.lean` | Proved |
| `mass_condition_independent` | `Lean/GaloisGate.lean` | Proved (norm_num) |

### Mechanized: Landauer–Einstein mass-equivalent fragment

**Definitions proved from:** energy scale \(k_{\mathrm B} T \ln 2\) (per bit, conventional
factor) and special-relativistic \(E = m c^2\), giving
\(m_{\mathrm{eq}}(T) = (k_{\mathrm B} T \ln 2) / c^2\).

| Result | Coq | Lean 4 | Notes |
|--------|-----|--------|-------|
| Definitions | `E_Landauer_bit`, `m_mass_equivalent` | `landauerBitEnergy`, `massEquivalent` | Coq: `kB_SI`, `c_SI`, `ln2` + positivity. Lean: exact SI reals, `Real.log 2`. |
| Positivity for \(T > 0\) | `E_Landauer_bit_pos`, `m_mass_equivalent_pos` | `landauerBitEnergy_pos`, `massEquivalent_pos` | |
| Linear scaling in \(T\) | `m_mass_equivalent_linear` | `massEquivalent_linear` | |
| Coarse numeric bracket at 300 K | -- | `massEquivalent_three_hundred_interval` | \(3.18\times10^{-38} < m < 3.20\times10^{-38}\) kg. |
| Tight numeric bracket at 300 K | -- | `massEquivalent_three_hundred_interval_tight` | `Real.log_two_near_10`; e.g. \(319439481694054/10^{52} < m < 319439481786228/10^{52}\) kg. |
| Agda | -- | -- | `Agda/LandauerEinsteinTrace.agda` (empty traceability module; proofs in Lean/Coq). |
| Haskell (engineering) | -- | -- | `cabal test landauer-einstein-sanity` — exact `Rational` check vs Lean tight numerators (`Haskell/test/LandauerEinsteinSanity.hs`); **not** a proof. |

**Extension plan (not theorems yet):** `Docs/FORMAL-PHYSICS-ROADMAP.md`.  
**Derivation prerequisites (exact statement shapes, \(\Delta L\), axiom bundles, and
why claims are not in the core language):** `Docs/FORMAL-PHYSICS-DERIVATION-PLAN.md`.

**Coq axioms:** `kB_SI_pos`, `c_SI_pos`, `ln2_pos`. The parameter `ln2` is not defined
as `ln(2)` inside Coq; Lean binds `ln 2` via Mathlib.

**What the 300 K brackets entail.** They follow from the **definitions** above,
special-relativistic \(E=mc^2\), the **SI** formalization used in Lean, **fixed**
\(T=300\) K, and Mathlib’s bounds on \(\ln 2\) (the tight interval uses
`Real.log_two_near_10`, \(\sim 10^{-10}\) on \(\ln 2\); finer bounds require a
stronger Mathlib certificate). They do **not** by themselves entail device-level
erasure theorems, measured gravitational couplings, or cosmological models.

---

## Gate Invariants

| Theorem | Agda | Coq | Lean 4 | Haskell QC |
|---------|------|-----|--------|------------|
| Mass conservation: `\|ρ_new − ρ_old\| ≤ δ` | `Gate.agda` (in Admissible) | `Gate.v` (admissible) | `Gate.lean` (Admissible) | `prop_mass_conservation_spec` |
| Clausius-Duhem: `D_int ≥ 0` | `Gate.agda` (in Admissible) | `clausius_duhem_forward` | `clausiusDuhemFwd` | `prop_clausius_spec` |
| Hydration irreversibility: `α_new ≥ α_old` | `Gate.agda` (in Admissible) | `Gate.v` (admissible) | `Gate.lean` (hydrationMono) | `prop_hydration_spec` |
| Strength monotonicity: `fc_new ≥ fc_old` | `Gate.agda` (in Admissible) | `Gate.v` (admissible) | `Gate.lean` (strengthMono) | `prop_strength_spec` |
| Gate soundness: `check = true → admissible` | `gate` (Dec) | `gate_check_sound` | `gateCheckSound` | -- |
| Gate completeness: `admissible → check = true` | `gate` (Dec) | `gate_check_complete` | `gateCheckComplete` | -- |
| Main safety theorem (forward hydration) | `forward-hydration-admissible` | `forward_hydration_admissible` | `forwardHydrationAdmissible` | `prop_gate_deterministic` |
| Gate determinism | structural | structural | `gateStateDetermined` | `prop_gate_deterministic` |

---

## Naturality and Activation

| Theorem | Agda | Coq | Lean 4 | Haskell QC |
|---------|------|-----|--------|------------|
| Gate material-agnosticism | `gate-material-agnostic` | -- | `gateMaterialAgnostic` | -- |
| Gate state-determinism | `gate-state-determined` | -- | `gateStateDetermined` | -- |
| Naturality square commutes | `naturality-square` | -- | `naturalitySquare` | -- |
| Every material has ≥1 active engine | `activation-total` | -- | `activationTotal` | -- |
| OPC characteristic engine (Hydration) | `opc-has-hydration` | -- | `opc_has_hydration` | -- |
| RAC characteristic engine (Transport) | `rac-has-transport` | -- | `rac_has_transport` | -- |
| Geopolymer characteristic (AlkaliActivation) | `geopolymer-has-alkali` | -- | `geo_has_alkali` | -- |
| Lime characteristic engine (Carbonation) | `lime-has-carbonation` | -- | `lime_has_carbonation` | -- |
| Earth characteristic engine (MoistureSorption) | `earth-has-moisture` | -- | `earth_has_moisture` | -- |
| Earth has no Hydration engine | `earth-no-hydration` | -- | `earth_no_hydration` | -- |
| OPC has no Transport engine | `opc-no-transport` | -- | `opc_no_transport` | -- |
| Engine membership decidable | `activation-decidable` | -- | `activationDecidable` | -- |

---

## Constitutional Sequences and Subject Reduction

| Theorem | Agda | Coq | Lean 4 | Haskell QC |
|---------|------|-----|--------|------------|
| ConstitutionalSeq (well-typed list) | -- (Agda uses DIB monad) | `ConstitutionalSeq` | `ConstitutionalSeq` | -- |
| Subject Reduction Lemma | structural | `subject_reduction` | `subjectReduction` | -- |
| Kleisli Admissibility Theorem (N-step) | `dib-assoc` (via monad laws) | `kleisli_admissibility` + `kleisli_fold_well_typed` | `kleisliAdmissibility` + `kleisliFoldWellTyped` | -- |
| Sequential composition safe | structural | `sequential_composition_safe` | `sequentialCompositionSafe` | -- |
| Gate arrow is well-typed | -- | `gate_arrow_well_typed` | `gateArrowWellTyped` | -- |
| Kleisli compose preserves well-typedness | -- | `kleisli_compose_well_typed` † | `kleisliComposeWellTyped` † | -- |
| Kleisli left unit | `kleisli-left-unit` | -- | `kleisliLeftUnit` | -- |
| Kleisli right unit | `kleisli-right-unit` | -- | `kleisliRightUnit` | -- |
| Kleisli associativity | `kleisli-assoc` | -- | `kleisliComposeAssoc` | -- |
| State monad left unit | `left-unit` | -- | `leftUnit` | -- |
| State monad right unit | `right-unit` | -- | `rightUnit` | -- |
| State monad associativity | `assoc` | -- | `assocM` | -- |
| DIB pipeline associativity | `dib-assoc` | -- | `dibAssoc` | -- |
| Admissible reflexivity | structural | `admissible_refl` | `admissibleRefl` | -- |

Scope note: the Subject Reduction and Kleisli rows above are mechanized for the
formal state-transition model used here. They should not be read as automatic
proof of every empirical protocol variant unless the protocol is explicitly
mapped to this model.

† **Kleisli compose (Coq/Lean):** `kleisli_compose_well_typed` /
`kleisliComposeWellTyped` prove `well_typed_N 2` (graded 2-step type), **not**
`WellTyped`.  The old `admissible_trans` / `admissibleTrans` axiom was **removed**
(it was refutable — see the non-transitivity counterexample in `GraphProperties.lean`).
The general N-step theorem is `kleisli_fold_well_typed_N` / `kleisliFoldWellTypedN`
(proved via `admissible_N_compose` / `admissibleN_compose` using the triangle
inequality).  Coq and Lean are fully in sync.

---

## SDF / FRep Interpretation

| Theorem | Agda | Coq | Lean 4 | Haskell QC |
|---------|------|-----|--------|------------|
| CSG decomposition (gate = ∩ of 4 half-spaces) | `admissible-to-csg` + `csg-to-admissible` | -- | `admissibleIffCSG` | `prop_gateSDF_matches_gateCheck` |
| Helmholtz antitone (gradient direction) | `helmholtz-antitone` (postulate; stdlib API pending) | `helmholtz_antitone` (proved) | `helmholtzAntitone` (proved) | `prop_helmholtz_antitone` |
| Helmholtz gradient constant (Eikonal) | `helmholtz-gradient-const` (postulate) | `helmholtz_gradient` (by ring) | `helmholtzGradient` (by ring) | `prop_helmholtz_gradient_const` |
| Helmholtz additive (linear SDF) | `helmholtz-linear` (postulate) | `helmholtz_additive` (by ring) | `helmholtzAdditive` (by ring) | -- |
| HelmholtzState admissible under forward hyd | `ψ-antitone-helmholtz` | -- | `helmholtzStateAdmissible` | -- |
| Admissible direction = negative gradient dir | -- | -- | `admissibleDirIsNegGrad` | -- |
| SDF intersection = max of two SDFs | -- | -- | -- | `prop_intersect_is_max` |
| Offset admissible expansion | -- | -- | -- | `prop_offset_admissible_expansion` |
| rUnion commutativity | -- | -- | -- | `prop_rUnion_commutative` |
| Offset distributivity | -- | -- | -- | `prop_offset_distributive` |

---

## Lean 4 Layer Summary

The Lean 4 layer matches Agda and Coq on the gate / Kleisli core, **plus** an extra
root `UMST.LandauerEinsteinBridge` (exact SI + `Real.log 2` + 300 K brackets). Coq
has the algebraic fragment with parameters.  Summary:

| Module | `theorem` | `lemma` | Source |
|--------|-----------|---------|--------|
| `UMST.Gate` | 14 | 0 | `Lean/Gate.lean` — AdmissibleN, `admissibleN_compose`, gate soundness/complete |
| `UMST.Helmholtz` | 5 | 0 | `Lean/Helmholtz.lean` — `helmholtzGradient`, `helmholtzStateAdmissible`, SDF/Eikonal |
| `UMST.Constitutional` | 11 | 0 | `Lean/Constitutional.lean` — Kleisli graded fold/compose (`kleisliComposeAssoc`, …) |
| `UMST.Naturality` | 6 | 0 | `Lean/Naturality.lean` — `gateMaterialAgnostic`, `naturalitySquare` |
| `UMST.Activation` | 11 | 0 | `Lean/Activation.lean` — engine profiles; `ActivatedUMST` |
| `UMST.DIBKleisli` | 9 | 0 | `Lean/DIBKleisli.lean` — monad laws; `dibArtifactGateCheck_eq_true` |
| `UMST.FormalFoundations` | 1 | 0 | `Lean/FormalFoundations.lean` — corpus witness |
| `UMST.LandauerEinsteinBridge` | 7 | 5 | `Lean/LandauerEinsteinBridge.lean` |
| `UMST.GraphProperties` | 10 | 0 | `Lean/GraphProperties.lean` |
| `UMST.Powers` | 3 | 5 | `Lean/Powers.lean` |
| `UMST.Convergence` | 8 | 0 | `Lean/Convergence.lean` |
| `UMST.GaloisGate` | 6 | 0 | `Lean/GaloisGate.lean` — Galois connection on gate conditions |
| `UMST.EnrichedAdmissibility` | 12 | 0 | `Lean/EnrichedAdmissibility.lean` |
| `UMST.LandauerLaw` | 9 | 3 | `Lean/LandauerLaw.lean` (1 Lean `axiom`: `physicalSecondLaw`) |
| `UMST.InfoTheory` | 4 | 0 | `Lean/InfoTheory.lean` |
| `UMST.EndConditions` | 3 | 0 | `Lean/EndConditions.lean` — stream end-state constraints |
| `UMST.MeasurementCost` | 1 | 0 | `Lean/MeasurementCost.lean` — observation cost vs Landauer |
| `UMST.LandauerExtension` | 6 | 0 | `Lean/LandauerExtension.lean` — n-bit / temperature scaling |
| `UMST.FiberedActivation` | 8 | 0 | `Lean/FiberedActivation.lean` — `engineFiber`, covering lemmas |
| `UMST.MonoidalState` | 6 | 0 | `Lean/MonoidalState.lean` |
| `UMST.SeparationBound` | 2 | 0 | `Lean/SeparationBound.lean` — **Theorem 2 (real-line core):** `accuracy_safety_separation_real`, `accuracy_safety_separation_real_symm` |
| `UMST.Economic.EconomicDomain` | 0 | 0 | `Lean/Economic/EconomicDomain.lean` — shared parameters / classical surrogate scaffolding (definitions) |
| `UMST.Economic.EconomicTemperature` | 3 | 0 | `Lean/Economic/EconomicTemperature.lean` |
| `UMST.Economic.BurdenRecursionIsAdmissible` | 7 | 0 | `Lean/Economic/BurdenRecursionIsAdmissible.lean` |
| `UMST.Economic.StochasticBurdenExpectation` | 4 | 0 | `Lean/Economic/StochasticBurdenExpectation.lean` |
| `UMST.Economic.DynamicEpsilonCalibration` | 2 | 0 | `Lean/Economic/DynamicEpsilonCalibration.lean` |
| `UMST.Economic.SelfReferentialEconomicTensor` | 2 | 0 | `Lean/Economic/SelfReferentialEconomicTensor.lean` |
| `UMST.Economic.NPVIsSpecialCaseOfThermodynamicBurden` | 2 | 0 | `Lean/Economic/NPVIsSpecialCaseOfThermodynamicBurden.lean` |
| `UMST.Economic.HallucinationDetector` | 1 | 0 | `Lean/Economic/HallucinationDetector.lean` (classical surrogate; `SAFETY-LIMITS.md`) |
| `UMST.Economic.LowEntropyLieDetector` | 1 | 0 | `Lean/Economic/LowEntropyLieDetector.lean` (classical surrogate) |
| `UMST.Economic.CreativityBudget` | 2 | 0 | `Lean/Economic/CreativityBudget.lean` |
| `UMST.Economic.ThermodynamicUncertaintyCertificate` | 1 | 0 | `Lean/Economic/ThermodynamicUncertaintyCertificate.lean` |
| `UMST.Economic.PhysicsConstrainedAI` | 1 | 0 | `Lean/Economic/PhysicsConstrainedAI.lean` |
| `UMST.Economic.EpistemicSensingModule` | 1 | 0 | `Lean/Economic/EpistemicSensingModule.lean` |
| `UMST.Economic.KleisliAdmissibilityComposition` | 2 | 0 | `Lean/Economic/KleisliAdmissibilityComposition.lean` |
| `UMST.Economic.NuanceIsolator` | 2 | 0 | `Lean/Economic/NuanceIsolator.lean` |
| `UMST.Economic.HorizonAwareGrounding` | 1 | 0 | `Lean/Economic/HorizonAwareGrounding.lean` |
| `UMST.Economic.CollectiveCoherenceCost` | 1 | 0 | `Lean/Economic/CollectiveCoherenceCost.lean` |
| `UMST.Economic.CreativeExplorationTolerance` | 1 | 0 | `Lean/Economic/CreativeExplorationTolerance.lean` |
| `UMST.CreditGreedyOptimal` | 7 | 0 | `Lean/CreditGreedyOptimal.lean` — `credit_greedy_optimal`, `greedy_nonneg`, append/singleton lemmas (Case A) |
| `UMST.Formal.Dignity` | 12 | 1 | `Lean/Dignity.lean` — `dignity_step`, monotonicity, sub-Landauer flag, list `sum_nonneg`, RCC identity link |
| `UMST.Formal.EtaCog` | 8 | 1 | `Lean/EtaCog.lean` — `eta_cog`, denom positivity, monotonicity / antitone / freeze / list aggregation |
| `UMST.Formal.RhoEstimator` | 8 | 0 | `Lean/RhoEstimator.lean` — Gaussian ρ-MI in bits, nonnegativity, monotonicity in \|ρ\|, clamp envelope, plug-in variance bound |
| `UMST.Formal.MedianConvergence` | 5 | 1 | `Lean/MedianConvergence.lean` — `N_warmup` ceiling cover, positivity, monotonicity in ε/δ, sqrt-window admissibility, empirical-CDF tail slot |
| `UMST.Formal.OrderStatisticsBand` | 5 | 1 | `Lean/OrderStatisticsBand.lean` — `nQuantile` envelope (ties `N_warmup`), split-sample inequality, classification / flip-rate surrogates, `p25_p75_admissibility`, empirical-CDF tail re-export |
| **Total (47 roots)** | **226** | **17** | Regenerate: `cd umst-formal && python3 scripts/lean_declaration_stats.py`. Methodology: `Docs/COUNT-METHODOLOGY.md`. |

**Kleisli naming:** use `admissibleN_compose` / `kleisliComposeAssoc` as in `Gate.lean` / `Constitutional.lean` (not the removed ungraded transitivity axiom).

**InfoTheory follow-up (not in artifact):** general non-negativity `0 ≤ mutualInformation J` (equivalently subadditivity of Shannon entropy / KL divergence ≥ 0) is stated as a future extension in `InfoTheory.lean`; the product case above already forces `MI = 0` for independent factors.

All Lean 4 theorems/lemmas in these roots are tactic-`sorry`-free (1 Lean `axiom`: `physicalSecondLaw` in `LandauerLaw.lean`).  CI badge: see `.github/workflows/ci.yml`
job `lean`.

---

## Cross-Layer Consistency (Haskell QuickCheck)

The Haskell property tests provide an additional computational layer that
validates the formal proofs against randomly generated states.

| Property | What it checks |
|----------|---------------|
| `prop_gate_deterministic` | Gate is a pure function (same inputs, same output) |
| `prop_mass_conservation_spec` | Gate accepts iff mass condition holds |
| `prop_clausius_spec` | Gate accepts iff Clausius-Duhem holds |
| `prop_hydration_spec` | Gate accepts iff hydration is non-decreasing |
| `prop_strength_spec` | Gate accepts iff strength is non-decreasing |
| `prop_gateSDF_matches_gateCheck` | SDF value ≤ 0 iff all four conditions hold |
| `prop_intersect_is_max` | CSG intersection = pointwise max of SDFs |
| `prop_helmholtz_gradient_const` | Computational check of Helmholtz gradient |
| `prop_helmholtz_antitone` | Computational check of antitone property |
| `prop_offset_admissible_expansion` | Offset preserves admissibility |
| `prop_rUnion_commutative` | R-function union is commutative |
| `prop_offset_distributive` | Offset distributes over intersection |
| `prop_fromMix_helmholtz_model` | `fromMix` constructor satisfies ψ = −Q_hyd · α |
| `prop_mass_not_transitive` | Executable counterexample: two admissible steps need not compose (mirrors `mass_not_transitive`) |
| `prop_info_product_joint_sum_one` | Normalized `p`,`q` ⇒ `jointMassesSum (productJoint p q) ≈ 1` (engineering mirror of `sumOne` for `productJoint`) |
| `prop_info_marginal_first_product` | `marginalFirst (productJoint p q) ≈ p` (mirror of Lean `marginalX_product`) |
| `prop_info_marginal_second_product` | `marginalSecond (productJoint p q) ≈ q` (mirror of Lean `marginalY_product`) |
| `prop_landauer_energy_mono`, `prop_landauer_nBit_scales`, `prop_landauer_300K_pos` | Landauer energy monotonicity, n-bit scaling, 300 K positivity |
| `prop_combine_one`, `prop_combine_zero`, `prop_combine_density_interp`, `prop_combine_freeEnergy_convex` | Monoidal `combine` on ℚ states (mirrors `MonoidalState`) |
| `prop_mc_uniform_joint_zero_mi`, `prop_mc_energy_nonneg` | Measurement-cost helpers |
| `prop_burden_symmetric_expectation`, `prop_burden_recursion_admissible`, `prop_burden_geom_decay` | Stochastic burden / recursion / geometric decay (engineering mirrors of `Economic/*`) |
| `prop_econ_horizon_in_min_max`, `prop_econ_npv_iterate`, `prop_econ_creativity_monotone`, `prop_econ_cost_split_nonneg` | Horizon grounding, NPV iterate, creativity budget, nuance split (mirrors `Lean/Economic/`) |
| `prop_credit_greedy_optimal`, `prop_credit_mass_nonneg`, `prop_credit_mass_append` | Case A credit mass (mirrors `Lean/CreditGreedyOptimal.lean`) |
| `prop_dignity_try_range`, `prop_dignity_step_honest_non_decreasing`, `prop_dignity_step_sub_landauer_fixed`, `prop_dignity_step_monotone_mi`, `prop_dignity_list_sum_nonneg` | Thermodynamic–epistemic dignity step (mirrors `Lean/Dignity.lean`) |
| `prop_eta_cog_nonneg`, `prop_eta_cog_monotone_dignity`, `prop_eta_cog_monotone_mi`, `prop_eta_cog_antitone_energy`, `prop_eta_cog_energy_zero_shape`, `prop_eta_cog_frozen_dignity_path` | MI-per-Joule η_cog (mirrors `Lean/EtaCog.lean`; denominator case **(i)**) |
| `prop_rho_mi_formula_matches_log2`, `prop_rho_mi_nonneg_interior`, `prop_rho_mi_monotone_abs_rho`, `prop_rho_mi_zero_at_zero`, `prop_rho_mi_bounded_by_rho_max` | Gaussian ρ-MI in bits (mirrors `Lean/RhoEstimator.lean`) |

Run with: `cd Haskell && cabal test --test-option=--qc-max-success=1000`
