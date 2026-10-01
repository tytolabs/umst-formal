-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: MaterialClass.lean

  The five binder families the cartridges model. The thermodynamic gate takes two states and no material, so a
  verdict never depends on the binder: `gateCheck` decides `Admissible` on the states alone (`gateCheckSound`,
  `gateCheckComplete` in `Concrete.Gate`). `Concrete.Activation` indexes its engines by this type.
-/

import Compat.Gate

namespace UMST

/-- Five binder families in the UMST system. -/
inductive MaterialClass where
  | OPC        -- Ordinary Portland Cement
  | RAC        -- Recycled-Aggregate Concrete
  | Geopolymer -- Alkali-activated alumino-silicate
  | Lime       -- Air lime or hydraulic lime
  | Earth      -- Raw or stabilised earth
  deriving DecidableEq, Repr

end UMST
