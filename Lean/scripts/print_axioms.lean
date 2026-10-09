-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  SPDX-License-Identifier: Apache-2.0

  UMST-Formal: scripts/print_axioms.lean

  Usage (from `umst-formal/Lean/`):

    lake env lean --run scripts/print_axioms.lean <shortTheoremName> [Module ...]

  Prints one axiom name per line for `UMST.<shortTheoremName>` (axiom dependency closure), importing the
  default modules and any extra modules named after the theorem; an unknown name exits non-zero.

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
  let (thm, mods) ← match args with
    | thm :: mods => pure (thm, mods)
    | [] =>
      throw (IO.userError "usage: lake env lean --run scripts/print_axioms.lean <TheoremName> [Module ...]")
  -- `UMST.` prefix with every dotted component, so `Composition.x` names `UMST.Composition.x`.
  let nm : Name := thm.splitOn "." |>.foldl (fun n c => .str n c) `UMST
  searchPathRef.set compile_time_search_path%
  let imports :=
    (#[`DEC, `Adjoint, `RegimeSoundness, `JenningsGelSpace] ++ (mods.toArray.map String.toName)).map fun m =>
      { module := m, runtimeOnly := false }
  withImportModules imports {} 1024 fun env => do
    -- An unknown name has an empty closure; refuse it, so a renamed or unimported theorem cannot pass vacuously.
    unless env.contains nm do
      throw (IO.userError s!"print_axioms: unknown constant {nm} (import its module as an extra argument)")
    for a in axiomClosure env nm do
      IO.println a.toString
