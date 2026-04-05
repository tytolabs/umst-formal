# Contributing to umst-formal

Thank you for considering a contribution. This repository is a formal
verification and categorical-semantics layer over a production Rust kernel.
Correctness is the primary goal; every change must preserve the four core
invariants.

## Lean declaration counts

After edits under `Lean/` that add/remove roots or change `theorem`/`lemma` totals:

1. `python3 scripts/lean_declaration_stats.py`
2. Align `PROOF-STATUS.md` and `FORMAL_FOUNDATIONS.md` with the output.
3. Update `scripts/expected_lean_declaration_snapshot.json` in the **same** PR if totals or root count change (CI compares against it).

See `Docs/COUNT-METHODOLOGY.md`. Axiom invariant: `python3 scripts/check_lean_axioms.py`. After editing linked Markdown in the curated corpus, run `bash scripts/check-markdown-links.sh` (same as CI).

## Ground Rules

1. **Do not modify the upstream kernel.** The Rust crate at
   `umst-prototype-2a/prototype/src/rust/core` is read-only from this
   repository's perspective. The FFI bridge (`ffi-bridge/`) is the only
   translation layer you may change.

2. **Every new proof obligation must be discharged.** Agda holes (`{!!}`),
   Coq `Admitted` lemmas, and Lean `sorry` are technical debt, not
   acceptable contributions. Open a discussion issue first if a proof is
   genuinely hard.

3. **Tests must pass.** Run `cabal test` (Haskell) and `cargo test`
   (Rust) before opening a PR. CI will enforce this automatically.

4. **Follow the comment style.** All non-trivial definitions must carry a
   plain-English explanation of their physical meaning and their
   relationship to the Agda/Coq counterpart.

## Workflow

```text
main ← (merge only via PR)
  └─ feature/<short-name>
  └─ fix/<issue-number>-<short-name>
  └─ proof/<layer>/<theorem-name>
```

Branch from `main`, open a Pull Request, request review from at least one
person familiar with the relevant layer (Agda, Coq, Lean 4, Haskell, or Rust).

## Commit Messages

Follow [Conventional Commits](https://www.conventionalcommits.org/):

```
feat(agda): add monoidal structure proof for Activation layer
fix(ffi):   guard dt against zero in umst_dissipation
proof(coq): discharge helmholtz_antitone via nia
docs(readme): clarify build order for Haskell FFI
test(haskell): add prop_tolerance_boundary QuickCheck property
```

Types: `feat`, `fix`, `proof`, `docs`, `test`, `refactor`, `chore`.

## Adding a New Invariant

1. Update `Docs/Architecture-Invariants.md` with the empirical motivation.
2. Add the invariant to `Agda/Gate.agda` and prove it.
3. Mirror the proof in `Coq/Gate.v`.
4. Port the proof to `Lean/Gate.lean`.
5. Add the check to `Haskell/UMST.hs::gateCheck` and `AdmissibilityResult`.
6. Expose a C function in `ffi-bridge/src/lib.rs` if the Rust kernel
   needs to be queried.
7. Add a QuickCheck property in `Haskell/test/Test.hs`.

## Layer-Specific Notes

### Agda

- Default `make check` does **not** pass `--safe` because `Gate.agda`
  contains physical-model postulates. A `--safe`-only slice would need a
  separate Makefile target restricted to postulate-free modules.
- Every `postulate` must be accompanied by a comment explaining what
  physical assumption it encodes and a reference to the experimental
  literature.
- Test: `cd Agda && make check`.

### Coq

- All non-trivial lemmas must have a proof sketch in a comment before
  the `Proof.` line.
- Extraction output (`ocaml/`) is generated, not hand-edited.
- Test: `cd Coq && make`.

### Haskell

- The library (`UMST`, `KleisliDIB`) must have zero QuickCheck failures.
- `FFI.hs` must compile even without the Rust library present (use
  `-fno-ffi` or a stub during pure Haskell CI).
- Test: `cd Haskell && cabal test`.

### Lean 4

- All theorems must be `sorry`-free. The `--wfail` flag in CI treats
  warnings (including sorry) as errors.
- Each Lean module mirrors one Agda module 1:1. Maintain this
  correspondence when adding new definitions.
- `axiom` is acceptable only for physical model assumptions (matching
  Coq `Axiom` and Agda `postulate`). Document the physical basis.
- `opaque` is acceptable for abstract types in the DIB monad (matching
  Agda `postulate` for phase types).
- Test: `cd Lean && lake build UMST`.

### Rust (ffi-bridge only)

- All `extern "C"` functions must be `#[no_mangle]` with `/// Safety`
  documentation.
- Integration tests live in `ffi-bridge/tests/integration.rs`.
- Test: `cd ffi-bridge && cargo test`.

## Reporting Issues

Open a GitHub issue with:
- Which layer (Agda / Coq / Lean 4 / Haskell / Rust) is affected.
- The minimal reproducer.
- Which invariant is (potentially) violated.
