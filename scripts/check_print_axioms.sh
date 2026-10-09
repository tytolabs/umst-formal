#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
# CI / local: axiom dependency closure for headline cartridge + DEC theorems must
# stay within the usual Mathlib baseline (+ optional project physicalSecondLaw).
#
# Requires: prior `lake build` (or CI `lean-action`) so `lake env lean --run` resolves imports.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/Lean"

export CHECK_PRINT_AXIOMS_ALLOW='^(propext|Quot\.sound|Classical\.choice|LandauerLaw\.physicalSecondLaw)$'

THEOREMS=(
  hodge_laplacian_symmetric
  laplacian_row_sum_zero
  discrete_stokes
  adjoint_recovers_gradient
  warnings_empty_iff_in_regime
  jennings_strength_monotone
  jennings_strength_nonneg
  # Entries may name extra modules to import after the theorem (C-GLUE-ZERO composition law, W-44).
  "Composition.combination_secondLaw Composition.GsmMonoid"
  "Composition.composite_passive_secondLaw Composition.GsmMonoid"
  "Composition.convexGlue_secondLaw Composition.GsmMonoid"
  "Composition.arbitrary_glue_not_closed Composition.GsmMonoid"
)

for entry in "${THEOREMS[@]}"; do
  read -r -a parts <<< "$entry"
  t="${parts[0]}"
  echo "check_print_axioms: UMST.$t"
  export CHECK_PRINT_AXIOMS_THM="$t"
  # shellcheck disable=SC2016
  lake env lean --run scripts/print_axioms.lean "${parts[@]}" 2>&1 | python3 -c '
import os, re, sys
allow = re.compile(os.environ["CHECK_PRINT_AXIOMS_ALLOW"])
thm = os.environ["CHECK_PRINT_AXIOMS_THM"]
bad = []
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    if not allow.match(line):
        bad.append(line)
if bad:
    print(f"check_print_axioms: {thm}: disallowed axioms {bad!r}", file=sys.stderr)
    sys.exit(1)
'
done

echo "check_print_axioms: OK (all closures ⊆ Mathlib baseline + optional physicalSecondLaw)"
