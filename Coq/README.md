# Coq Layer — Verified Extraction of Gate Logic

Verified formalisation of the UMST thermodynamic gate with extraction to OCaml.
This layer mirrors the Agda proofs in `../Agda/Gate.agda` and produces a
standalone OCaml reference implementation that is **correct by construction**.

## Purpose

The Coq layer serves two roles:

1. **Theorem proving over rationals (QArith)** — the same four invariants
   proved in Agda are re-proved here using Coq's tactic-based proof engine,
   providing an independent verification.

2. **Verified extraction to OCaml** — Coq's extraction mechanism (Letouzey 2002)
   generates an OCaml module from the proved `gate_check` function.  Because
   extraction preserves computational content, the OCaml code inherits the
   correctness guarantees of the Coq proofs.  This gives us a reference
   implementation to validate the Rust kernel against.

## Prerequisites

| Tool    | Version | Notes                              |
|---------|---------|-------------------------------------|
| Coq     | 8.18+   | `opam install coq`                 |
| OCaml   | 4.14+   | Required by Coq; also runs extracted code |

Optional (for compiling extracted OCaml separately):

| Tool       | Version | Notes                           |
|------------|---------|----------------------------------|
| ocamlfind  | 1.9+    | `opam install ocamlfind`         |
| zarith     | 1.13+   | Only if you remap Z to native ints |

## Building

```bash
# Compile Coq proofs (type-checks all theorems)
coqc Gate.v

# Extract OCaml from verified proofs (depends on Gate.vo)
coqc Extraction.v

# Or use the Makefile:
make all
```

After `Extraction.v` compiles, two files appear:

- `gate_extracted.ml` — OCaml implementation of `gate_check`
- `gate_extracted.mli` — OCaml interface

To compile the extracted OCaml:

```bash
# Bytecode (quick, for testing)
ocamlfind ocamlc gate_extracted.ml -o gate_test

# Native (optimised)
ocamlfind ocamlopt gate_extracted.ml -o gate_test
```

## What Gets Extracted

| Coq definition         | OCaml output           | Role                    |
|------------------------|------------------------|--------------------------|
| `ThermodynamicState`   | Record type            | State representation     |
| `gate_check`           | `bool` function        | Decision procedure       |
| `delta_mass`, `Q_hyd`  | Rational constants     | Physical parameters      |
| `Qle_bool`, `Qminus`  | Arithmetic helpers     | Rational comparison      |

**Erased** (zero runtime cost): `admissible` (Prop), all theorems, all proofs.
Only computational content survives extraction.

## Comparing Extracted OCaml with Rust Kernel

The validation workflow:

1. **Generate test vectors** — random pairs of `ThermodynamicState` values
   (use QuickCheck from the Haskell layer, Python scripts, or Rust's proptest)

2. **Run each vector through three implementations:**

   | Implementation      | Source           | Trust level            |
   |---------------------|------------------|-------------------------|
   | Extracted OCaml     | Coq proof        | Correct by construction |
   | Haskell pure gate   | `UMST.hs`        | Property-tested         |
   | Rust kernel         | `umst-core`      | Production code         |

3. **Assert identical decisions** — any discrepancy between the extracted
   OCaml and Rust indicates a bug in Rust (not in the reference).

The Haskell layer already automates this via FFI + QuickCheck.  The
extracted OCaml provides a *third* independent implementation.

## File Structure

```
Coq/
├── Gate.v              Theorems: admissible predicate, gate_check,
│                       clausius_duhem_forward, strength_monotone_powers,
│                       forward_hydration_admissible, gate_check_correct
├── Extraction.v        Extraction configuration + commands
├── gate_extracted.ml   (generated) OCaml implementation
├── gate_extracted.mli  (generated) OCaml interface
└── README.md           This file
```

## Theorems Proved

| Theorem                          | Statement                                         |
|----------------------------------|----------------------------------------------------|
| `clausius_duhem_forward`         | α advances ⟹ dissipation ≥ 0                     |
| `strength_monotone_powers`       | α advances ⟹ strength non-decreasing             |
| `forward_hydration_admissible`   | Forward hydration always passes the gate           |
| `gate_check_correct`            | `gate_check = true ↔ admissible` (sound+complete) |
| `gate_accepts_forward_hydration` | Physical transitions ⟹ `gate_check = true`       |

**Axioms** (physical model assumptions, not proved):
- `psi_antitone` — Helmholtz free energy is antitone in hydration
- `fc_monotone` — Powers model strength is monotone in hydration

**Admitted** (provable but deferred):
- `helmholtz_antitone` — concrete arithmetic for −Q·α₂ ≤ −Q·α₁

## Best Practices for Verified Extraction

1. **Separate Prop from Set/Type** — proofs in `Prop` are erased during
   extraction, keeping the output lean.  Computational content lives in `Set`.

2. **Use exact arithmetic** — QArith (rationals) avoids floating-point
   rounding issues entirely.  The Rust kernel uses `f64` with epsilon
   tolerances; the Coq proofs establish the exact mathematical properties
   that the toleranced version approximates.

3. **Axioms must be documented** — every `Axiom` in the file corresponds to
   a physical law with empirical backing.  The axioms are consistent and
   do not extend Coq's logic unsoundly.

4. **Three-way validation** — for safety-critical systems, compare at least
   three independent implementations (here: Coq/OCaml, Haskell, Rust).
   Agreement across all three provides high confidence.

5. **Keep the extracted interface small** — extract only the decision
   function and its types.  The smaller the trusted interface, the easier
   it is to audit and integrate.
