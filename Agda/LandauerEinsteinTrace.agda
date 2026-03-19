{-|
  Traceability stub (Agda): Landauer–Einstein mass-equivalent certificate.

  Machine-checked real analysis and SI numeric brackets live in:
  * `Lean/LandauerEinsteinBridge.lean` — exact SI `k_B`, `c`, `Real.log 2`, intervals at 300 K
  * `Coq/LandauerEinsteinBridge.v` — algebraic fragment with parameters `kB_SI`, `c_SI`, `ln2`

  This repository’s Agda layer does not duplicate Mathlib-style bounds on `ln 2`.
  The empty module keeps the dependency graph explicit under `make check`.

  See: `PROOF-STATUS.md`, `Docs/FORMAL-PHYSICS-ROADMAP.md`.
-}

{-# OPTIONS --without-K --exact-split --safe #-}

module LandauerEinsteinTrace where
