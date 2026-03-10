# Video Demo — Recording Instructions

Target: 2-minute screencast demonstrating the full verification pipeline.

## Segments

### 1. Build FFI Bridge (~20s)

```bash
cd ffi-bridge
cargo build --release
```

Show successful compilation of `libumst_ffi`. Highlight that the Rust kernel (`umst-core`) is linked as an unmodified path dependency.

### 2. Agda Type-Checking (~30s)

```bash
cd ../Agda
make check
```

Show each `.agda` file type-checking successfully. Emphasise: **type-checking IS the proof** — if it compiles, the invariants hold.

### 3. Coq Extraction (~30s)

```bash
cd ../Coq
make extract
```

Show `Gate.v` compiling, then `Extraction.v` producing OCaml code. Briefly open the generated `.ml` to show extracted decision procedure.

### 4. Haskell Property Tests (~30s)

```bash
cd ../Haskell
cabal build
cabal test
```

Show QuickCheck running gate-correspondence tests: random states evaluated by both the pure Haskell gate and the Rust gate via FFI, asserting identical verdicts.

### 5. Wrap-Up (~10s)

Summarise the pipeline: field observations → formal invariants → dependent-type proofs → verified extraction → property-tested FFI bridge → production Rust kernel.

## Recording Notes

- Terminal font ≥ 16pt for readability
- Use a clean shell with minimal prompt
- Pre-build dependencies so the demo focuses on verification, not compilation
- If Agda type-checking is slow, consider pre-recording that segment
