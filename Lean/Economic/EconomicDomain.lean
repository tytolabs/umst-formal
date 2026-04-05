/-
  UMST-Formal: Economic/EconomicDomain.lean

  Wave 6.5.2 — classical scaffolding for the meso-scale Economic layer.
  Thresholds here are **user-scoped parameters**, not physical constants.
  “RCC / hallucination” language in sibling modules refers to **Shannon-based
  surrogates** only (see SAFETY-LIMITS.md); quantum RCC lives in umst-formal-double-slit.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs

namespace UMST.Economics

/-- Alarm threshold on information-theoretic quantities (nats), user-supplied. -/
structure InfoThreshold where
  θ : ℝ

/-- Creative / exploration slack in the same units as burden bookkeeping (`ℚ` macroscopic axis). -/
abbrev CreativeSlack := ℚ

/-- Local vs global tradeoff weight in `[0,1]` (hypothesis-driven each use). -/
abbrev HorizonWeight := ℝ

end UMST.Economics
