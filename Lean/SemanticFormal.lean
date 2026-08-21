-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: SemanticFormal.lean

  **HCOM-005 — Semantic formal extension anchor** (Human Communication Blueprint §5).

  Theorems and derived witnesses remain in `MeaningState`, `SemanticSecondLaw`, and
  `SemanticEconomicModules`.  This module is the canonical home for the semantic-formal
  extension anchor in `umst-formal`; `umst-semantics/formal` is a retired husk.

  Single-axiom discipline: zero new Lean `axiom` declarations.
-/

import MeaningState
import SemanticSecondLaw

namespace UMST.SemanticFormal

/-- Canonical module anchor string for HCOM-005 extension wiring. -/
def anchorModule : String := "UMST.SemanticFormal"

/-- Re-export: degenerate P0 meaning state (canonical fixture lives in `MeaningState`). -/
noncomputable def consistentP0 := UMST.MeaningState.consistentP0Meaning

end UMST.SemanticFormal
