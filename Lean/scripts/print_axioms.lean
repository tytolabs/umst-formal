/-
  SPDX-License-Identifier: Apache-2.0

  UMST-Formal: scripts/print_axioms.lean

  Usage (from `umst-formal/Lean/`):

    lake env lean --run scripts/print_axioms.lean <shortTheoremName>

  Prints one axiom name per line for `UMST.<shortTheoremName>` (axiom dependency closure).

  CI / batch regression: `bash scripts/check_print_axioms.sh` (from repo root, after `lake build`).
-/
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.SearchPath
import Lean.Environment

open Lean System

/-- Axiom dependency closure for `nm` in a fully-built `env` (no `MonadEnv` plumbing). -/
def axiomClosure (env : Environment) (nm : Name) : Array Name :=
  let (_, s) := ((CollectAxioms.collect nm).run env).run {}
  s.axioms

unsafe def main (args : List String) : IO Unit := do
  let thm ← match args with
    | thm :: _ => pure thm
    | [] =>
      throw (IO.userError "usage: lake env lean --run scripts/print_axioms.lean <TheoremName>")
  let nm : Name := .str `UMST thm
  searchPathRef.set compile_time_search_path%
  let imports :=
    #[`DEC, `Adjoint, `RegimeSoundness, `JenningsGelSpace].map fun m =>
      { module := m, runtimeOnly := false }
  withImportModules imports {} 1024 fun env => do
    for a in axiomClosure env nm do
      IO.println a.toString
