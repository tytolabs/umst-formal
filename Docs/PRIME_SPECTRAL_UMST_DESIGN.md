# Prime-Spectral UMST — Design Document (Increment 1)

**Date:** 2026-06-15  
**Scope:** Formal foundations for prime-statistics-inspired **guidance** on auxiliary multiplicative channels.  
**Status:** Increment 1 formal + Inc 1.5–4 manifold wiring; Inc 3 empirical **`inconclusive`** (see Increment 3 section).

---

## Honest milestone statement

**Increment 1 milestone:** Categorical semantics and gate-preservation proofs for prime-statistics-inspired **guidance** on auxiliary multiplicative channels. This is **novel research scaffolding** — not evidence that prime numbers govern thermodynamic admissibility. Measurable performance improvements require Increment 3 benchmarks against existing Helmholtz/topology baselines.

There is **zero direct evidence** linking primes or Riemann zeta zero spectra to any existing TYTO repository. All mappings below are **productive analogies** for algorithm design, explicitly labeled as such.

---

## Non-claims (mandatory)

We do **not** claim:

1. Prime numbers or zeta zeros emerge from Clausius–Duhem or second-law dynamics.
2. The thermodynamic gate should gain a fifth conjunct based on number theory.
3. von Mangoldt weights alter admissibility verdicts on `ThermodynamicState`.
4. Infinite zeta-zero filter sums converge (open in Increment 1).
5. Any measurable speedup over Helmholtz/topology baselines (deferred to Increment 3).

---

## Architectural split

```
Proposer → SpectralFilter (auxiliary channel) → gateCheck (unchanged 4-conjunct gate) → Kleisli
```

Prime/spectral structures act on **`MultiplicativeChannel`** (topology density indices, mix lattice, graph edge weights). The hard gate on **`ThermodynamicState`** is **unchanged**. See `Lean/PrimeSpectralGuidance.lean` and `Lean/PrimeSpectralCategory.lean`.

This matches the W9 agnostic-kernel pattern: modulation in cartridge/spatial layer; gate sees only transition scalars.

---

## Analogy map

| Analogy (labeled) | Concrete UMST extension | Increment 1 status |
|-------------------|---------------------------|-------------------|
| Prime statistics / multiplicative indivisibility | Sparse update lattice on `Fin n`; prime-period indices | **Defined** (`PrimePeriod`, `MultiplicativeChannel`) |
| von Mangoldt Λ(n) | Impulse train weights on channel (`vonMangoldtWeight`) | **Defined** (ℚ surrogate; Mathlib `IsPrimePow` / `minFac`) |
| Riemann zeta zero spectra | Oscillatory basis `cos(γ·log n)` as filter bank | **Def only** (`zetaOscillator`); convergence **OPEN** |
| Explicit formula (Weil) | Finite truncation `mangoldtWeightedSum` | **Proved** (linearity, zero at Λ=0 indices) |
| Spectral filtering | Endofunctor `spectralFilter` on `MultiplicativeChannel` | **Proved** (`spectralFilter_id`, perturbation bounds) |
| Topological protection | Coprime prime periods → lcm = product | **Proved** (`coprime_primes_lcm_eq_mul`) |
| Gate preservation | Channel filters do not alter `gateCheck` on thermo scalars | **Proved** (`gate_naturality`, `applyChannelFilter_admissible`) |
| Kleisli compatibility | Graded `AdmissibleN` unchanged when thermo fixed | **Proved** (`kleisli_guidance_commute`) |

---

## Proven vs open (Increment 1 ledger)

### Proven (Lean 4, sorry-free, zero new axioms)

| Result | Module |
|--------|--------|
| `gateProjection` leaves `ThermodynamicState` unchanged | `PrimeSpectralGuidance` |
| `applyChannelFilter_admissible` | `PrimeSpectralGuidance` |
| `spectralFilter_id`, `spectralFilter_perturb` | `PrimeSpectralGuidance` |
| `mangoldtWeightedSum` linearity | `PrimeSpectralGuidance` |
| `coprime_primes_lcm_eq_mul` | `PrimeSpectralGuidance` |
| `kleisli_guidance_commute` | `PrimeSpectralGuidance` |
| `gate_naturality`, `GuidanceF_id_map` | `PrimeSpectralCategory` |

### Open (explicitly deferred)

| Item | Target increment |
|------|------------------|
| Infinite zeta-zero sum convergence | Research / later formal |
| Agda / Coq port | 1.5 |
| Manifold Rust witness (`PrimeSpectralFilter`) | 2 |
| Benchmark vs `HelmholtzFilter` | 3 |
| Catalog lock bump in `umst-manifold` | 2 (after Rust witness) |
| Empirical speedup quantification | 3 |
| Link `physicalSecondLaw → prime distribution` | **Not planned** (non-claim) |

---

## No new axioms

Increment 1 adds **zero** Lean axioms. The sole project axiom remains `LandauerLaw.physicalSecondLaw` per `FORMAL_FOUNDATIONS.md`.

The rational von Mangoldt surrogate `vonMangoldtWeight` uses `IsPrimePow` and `minFac` from Mathlib; it is **not** identified with the real-valued `Λ n = log p` in the ℚ layer (log lives in `ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ`).

---

## Glossary (disambiguation)

| Term in this doc | Meaning |
|------------------|---------|
| **PrimeSpectral** | Analytic number theory analogies on auxiliary channels |
| **Spectral (double-slit)** | von Neumann / Klein operator eigenvalue entropy (`KleinInequality.lean`) — **different namespace** |
| **Guidance** | Pre/post filter on auxiliary data; not a gate conjunct |
| **Gate projection** | `GuidedState.thermo` field |

---

## Catalog export (prep only)

Provisional `catalog_id`: **`umst.guidance.prime_spectral`** (distinct from `umst.gate.cd_transition`).

**Do not** bump `umst-manifold/artifacts/catalog.lock.json` until Layer 2 Rust witness exists.

Modules register via `umst-formal-double-slit/tools/lean_export/export_catalog.py` `--also-lean-root ../umst-formal/Lean` on next export wave.

---

## Citations

1. H. Davenport, *Multiplicative Number Theory* (3rd ed.) — von Mangoldt, explicit formula.
2. H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I* — prime distribution statistics.
3. TYTO `umst-formal/FORMAL_FOUNDATIONS.md` — single-axiom policy, DIB Kleisli semantics.
4. TYTO `umst-formal/Lean/Gate.lean` — four-conjunct admissibility, graded `AdmissibleN`.
5. TYTO `umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md` — proof library vs gate law split.

---

## Layered roadmap

| Increment | Deliverable |
|-----------|-------------|
| **1** (this doc) | Lean formal + design |
| 1.5 | Agda/Coq/Haskell full crosswalk |
| 2 | `umst-manifold` `PrimeSpectralFilter` + topology hook |
| 3 | Benchmarks vs Helmholtz; admissibility regression suite |
| 4 | Adversarial tests + catalog lock + `claims-vs-proofs` row |

---

## Increment 3 empirical result (2026-06-15)

**Protocol:** `umst-manifold/docs/PRIME_SPECTRAL_BENCHMARK_PROTOCOL.md`  
**SSOT JSON:** `outputs/prime_spectral_inc3_latest.json`

Tier 1 (32×32 `TopologySolver` diffusion, modes A–D): **no mode** reached ‖ρ−ρ\*‖ < 0.05 within 40 iterations; **verdict `inconclusive`**. Elementwise modes B/D ran faster in wall time but did not improve convergence vs Helmholtz baseline at equal tolerance.

Tier 2 Striatus quick-path regression harness is wired (`UMST_SHELL_PRIME_SPECTRAL=1` in `shell_topology_rib_pattern.rs`) but not executed in this session — `umst-concrete-cartridge` requires API resync with local `umst-manifold`.

**Decision:** Retain Lean gate-preservation layer; **do not** open Inc 5 zeta/coprime R&D until a pre-registered Tier 1 win at equal tolerance is demonstrated. Inc 4 catalog/traceability promotion proceeded independently (guidance slug `umst.guidance.prime_spectral`, not in `GATE_REGISTRY`).

---

## Manifold integration hook (Layer 2 preview)

```text
TopologySolver::step_density_diffusion_filtered(pre_filter, post_filter)
  → pre_filter = PrimeSpectralFilter::apply (bounded ε)
  → gate unchanged on TransitionScalars
```

Not implemented in Increment 1.
