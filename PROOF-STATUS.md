# Proof Status

This document maps every formal claim about the Unified Material-State
Tensor (UMST) to its machine-checked proof artefact.  It is the primary
entry point for reviewers and formal-methods evaluators.

**Proof layers:**

| Layer | Tool | Build command | Status |
|-------|------|---------------|--------|
| Agda | Agda 2.6.4 + agda-stdlib 2.0 | `cd Agda && make check` | Zero postulates that are logical gaps (see key below) |
| Coq | Coq 8.18 + QArith | `cd Coq && make` | Zero `Admitted` |
| Lean 4 | Lean 4.14.0 + Mathlib4 | `cd Lean && lake build UMST` | Zero `sorry` |
| Haskell | GHC 9.6 + QuickCheck | `cd Haskell && cabal test` | 13 properties, 500 tests each |

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
concrete witness for Helmholtz-consistent states is in `Lean/Helmholtz.lean`
(ψAntitoneHelmholtz).

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
| ConstitutionalSeq (well-typed list) | `DIB-Kleisli.agda` | `ConstitutionalSeq` | `ConstitutionalSeq` | -- |
| Subject Reduction Lemma | structural | `subject_reduction` | `subjectReduction` | -- |
| Kleisli Admissibility Theorem (N-step) | `dib-assoc` (via monad laws) | `kleisli_admissibility` + `kleisli_fold_well_typed` | `kleisliAdmissibility` + `kleisliFoldWellTyped` | -- |
| Sequential composition safe | structural | `sequential_composition_safe` | `sequentialCompositionSafe` | -- |
| Gate arrow is well-typed | -- | `gate_arrow_well_typed` | `gateArrowWellTyped` | -- |
| Kleisli compose preserves well-typedness | -- | `kleisli_compose_well_typed` | `kleisliComposeWellTyped` | -- |
| Kleisli left unit | `kleisli-left-unit` | -- | `kleisliLeftUnit` | -- |
| Kleisli right unit | `kleisli-right-unit` | -- | `kleisliRightUnit` | -- |
| Kleisli associativity | `kleisli-assoc` | -- | `kleisliComposeAssoc` | -- |
| State monad left unit | `left-unit` | -- | `leftUnit` | -- |
| State monad right unit | `right-unit` | -- | `rightUnit` | -- |
| State monad associativity | `assoc` | -- | `assocM` | -- |
| DIB pipeline associativity | `dib-assoc` | -- | `dibAssoc` | -- |
| Admissible reflexivity | structural | `admissible_refl` | `admissibleRefl` | -- |

---

## SDF / FRep Interpretation

| Theorem | Agda | Coq | Lean 4 | Haskell QC |
|---------|------|-----|--------|------------|
| CSG decomposition (gate = ∩ of 4 half-spaces) | `admissible-to-csg` + `csg-to-admissible` | -- | `admissibleIffCSG` | `prop_gateSDF_matches_gateCheck` |
| Helmholtz antitone (gradient direction) | `helmholtz-antitone` (postulate) | `helmholtz_antitone` (proved) | `helmholtzAntitone` (proved) | `prop_helmholtz_antitone` |
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

The Lean 4 layer provides full parity with Agda and Coq.  Summary:

| Module | Theorems proved | Source |
|--------|-----------------|--------|
| `UMST.Gate` | 17 | `Lean/Gate.lean` |
| `UMST.Helmholtz` | 5 | `Lean/Helmholtz.lean` |
| `UMST.Constitutional` | 9 | `Lean/Constitutional.lean` |
| `UMST.Naturality` | 7 | `Lean/Naturality.lean` |
| `UMST.Activation` | 14 | `Lean/Activation.lean` |
| `UMST.DIBKleisli` | 7 | `Lean/DIBKleisli.lean` |
| **Total** | **59** | |

All 59 Lean 4 theorems are sorry-free.  CI badge: see `.github/workflows/ci.yml`
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

Run with: `cd Haskell && cabal test --test-option=--qc-max-success=1000`
