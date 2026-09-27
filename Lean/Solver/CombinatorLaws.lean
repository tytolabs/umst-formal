-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Solver/CombinatorLaws.lean

  Toy `OrElse` on a two-constructor `SolverTerm` with `fail` as the monoid unit.
  Fully proved left/right identity and associativity (no `sorry`, no `axiom`).

  `lean4checker` is not installed in this workspace slice — this file is not
  kernel-checked yet; elaboration is expected once the module is wired into Lake.
-/

namespace UMST.Solver

/-- Minimal solver syntax: failure or a successful witness tag. -/
inductive SolverTerm where
  | fail : SolverTerm
  | ok (n : Nat) : SolverTerm

/-- Backtracking choice: try the left branch; on `fail`, fall through to the right. -/
def OrElse (a b : SolverTerm) : SolverTerm :=
  match a with
  | .fail => b
  | t => t

/-- Optional outcome of running a term (prelude-only semantics). -/
def eval (t : SolverTerm) : Option Nat :=
  match t with
  | .fail => none
  | .ok n => some n

namespace CombinatorLaws

theorem OrElse_fail_left (t : SolverTerm) : OrElse SolverTerm.fail t = t :=
  rfl

theorem OrElse_fail_right (t : SolverTerm) : OrElse t SolverTerm.fail = t := by
  cases t <;> rfl

theorem OrElse_assoc (a b c : SolverTerm) :
    OrElse (OrElse a b) c = OrElse a (OrElse b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem eval_OrElse (a b : SolverTerm) :
    eval (OrElse a b) = (eval a).orElse (fun _ => eval b) := by
  cases a <;> cases b <;> simp [OrElse, eval]

end CombinatorLaws

end UMST.Solver
