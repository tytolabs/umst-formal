# Proof Status

This document maps every formal claim about the Unified Material-State
Tensor (UMST) mechanized **in this repository** to its machine-checked proof
artefact. It is the primary index for the `umst-formal` artifact.

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
- “Dignity floor” / “humour modulus” as formal predicates.
- Full autopoietic / cultural-closure semantics beyond the DIB abstract interface.
- End-to-end certification of arbitrary external runtime or narrative claims.

This list is **descriptive** (current coverage), not a forecast of what is true in nature.

**Proof layers:**

| Layer | Tool | Build command | Status |
|-------|------|---------------|--------|
| Agda | Agda 2.8 + bundled stdlib (Homebrew) or 2.6.4+ | `cd Agda && make check` | Physical postulates in `Gate.agda` (see key); `InfoTheory.agda` (definitions + 3 postulates mirroring Lean/Coq product laws; small length lemmas proved); default `make check` is not `--safe` |
| Coq / Rocq | Rocq 9 / Coq 8.18 + QArith | `cd Coq && make` | No `Admitted`; `admissible_trans` REMOVED (refutable); replaced by graded `admissible_N_compose`; `InfoTheory.v` (product joint, `joint_mass_product`, both marginals as `Forall2 Qeq`, incl. `marginal_second_product` / normalized corollary) |
| Lean 4 | Lean 4.14+ + Mathlib4 | `cd Lean && lake build UMST` | No `sorry`; `admissibleTrans` REMOVED; replaced by graded `admissibleN_compose` in 12 modules |
| Haskell | GHC 9.6+ (tested 9.14) + QuickCheck | `cd Haskell && cabal test umst-properties -f -with-ffi` | 17 properties (incl. 3× `InfoTheory`: product joint sums to 1, marginals match `Lean/InfoTheory` product laws); plus `cabal test landauer-einstein-sanity` (Rational check vs Lean tight bracket) |
| Haskell ↔ Rust | same + `libumst_ffi` | `cd ffi-bridge && cargo build --release` then `cd Haskell && cabal test umst-ffi-correspondence -f with-ffi` | Fixed scenarios via `FFI.runCorrespondenceTests` (optional suite) |

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
| Free-energy antitone under hydration | `psi_antitone` (Gate.v) | `ψ-antitone` (Gate.agda) | `psiAntitone` (Gate.lean) | Clausius-Duhem / Helmholtz model |
| Strength monotone under hydration | `fc_monotone` (Gate.v) | `fc-monotone` (Gate.agda) | `fcMonotone` (Gate.lean) | Powers gel-space ratio model |
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

### Lean opaque / axiom declarations (matching Agda postulates)

| Declaration | File | Classification |
|---|---|---|
| `DIBState` (opaque) | DIBKleisli.lean | Abstract state type |
| `Observation`, `Insight`, `Design`, `Artifact` (axiom) | DIBKleisli.lean | Abstract phase types |
| `*.inhabited` (axiom) | DIBKleisli.lean | Inhabitedness witnesses for opaque types |
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

| Module | Theorems proved | Source |
|--------|-----------------|--------|
| `UMST.Gate` | 21 | `Lean/Gate.lean` (adds §10: AdmissibleN, compose, refl, iff) |
| `UMST.Helmholtz` | 5 | `Lean/Helmholtz.lean` |
| `UMST.Constitutional` | 14 | `Lean/Constitutional.lean` (adds WellTypedN, graded compose/fold) |
| `UMST.Naturality` | 7 | `Lean/Naturality.lean` |
| `UMST.Activation` | 14 | `Lean/Activation.lean` |
| `UMST.DIBKleisli` | 7 | `Lean/DIBKleisli.lean` |
| `UMST.LandauerEinsteinBridge` | 14 | `Lean/LandauerEinsteinBridge.lean` |
| `UMST.GraphProperties` | 7 | `Lean/GraphProperties.lean` (counterexample + order props) |
| `UMST.Powers` | 4 | `Lean/Powers.lean` (Powers model, monotone witness) |
| `UMST.Convergence` | 5 | `Lean/Convergence.lean` (Lyapunov, Monotone Convergence) |
| `UMST.GaloisGate` | 4 | `Lean/GaloisGate.lean` (Galois connection, condition lattice) |
| `UMST.EnrichedAdmissibility` | 6 | `Lean/EnrichedAdmissibility.lean` (Lawvere metric, triangle) |
| `UMST.LandauerLaw` | 8+ | `Lean/LandauerLaw.lean` (T_LandauerLaw; 1 axiom: `physicalSecondLaw`; `physicalSecondLawUniformBinary` + `physicalSecondLaw_uniform_binary`; `ProbDist.ext_mass` for extensionality from `mass`) |
| `UMST.InfoTheory` | 4+ | `Lean/InfoTheory.lean` — finite joint law `JointDist`, marginals, `jointEntropy` / `mutualInformation`, product joint; **proved:** `marginalX_product`, `marginalY_product`, `jointEntropy_product`, `mutualInformation_product_zero` |
| **Total** | **121+** | |

**InfoTheory follow-up (not in artifact):** general non-negativity `0 ≤ mutualInformation J` (equivalently subadditivity of Shannon entropy / KL divergence ≥ 0) is stated as a future extension in `InfoTheory.lean`; the product case above already forces `MI = 0` for independent factors.

All Lean 4 theorems/lemmas in these roots are sorry-free (1 axiom: `physicalSecondLaw` in `LandauerLaw.lean`).  CI badge: see `.github/workflows/ci.yml`
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

Run with: `cd Haskell && cabal test --test-option=--qc-max-success=1000`
