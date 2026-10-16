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
  # The passive route (FORMAL-PASSIVE-ROUTE-4LANG): the one statement every dissipative bound and composite uses.
  "Convex.PassiveRoute.passive_secondLaw_iff Convex.PassiveRoute"
  "Convex.PassiveRoute.dissipation_nonneg_of_secondLaw Convex.PassiveRoute"
  "Convex.PassiveRoute.passive_inequality_secondLaw Convex.PassiveRoute"
  "Convex.PassiveRoute.passive_refused_of_neg Convex.PassiveRoute"
  "ConvexPhiDissipation.gsmCartridge_passive_secondLaw ConvexPhiDissipation"
  "Constants.SecondLawDissipation.viscosity_nonneg Constants.SecondLawDissipation"
  "Constants.SecondLawElastic.orthotropic_poisson_sq_le Constants.SecondLawElastic"
  "ConvexPhiChannels.restitution_le_one ConvexPhiChannels"
  "Convex.PhiGrammar.phiExpr_gsmCartridge_secondLaw Convex.PhiGrammar"
  # Gluing of agents (FORMAL-AGENT-COLIMIT).
  "Coordination.knows_glue_iff Coordination.AgentColimit"
  "Coordination.ker_glue Coordination.AgentColimit"
  # The learning-loop laws (FORMAL-LEARNING-LOOP-LAWS).
  "LearningLoop.fold_perm LearningLoopLaws"
  "LearningLoop.barrier_floor_tendsto_zero LearningLoopLaws"
  "LearningLoop.ppoStep_simplex LearningLoopLaws"
  "LearningLoop.verified_bit_costs_landauer LearningLoopLaws"
  # A prediction-then-observation turn as measureFeedback (FORMAL-PREDICTION-AS-MEASURE-FEEDBACK).
  "PredictionFeedback.turn_pair_work_le PredictionFeedback"
  "PredictionFeedback.summary_admitted_receipts PredictionFeedback"
  "PredictionFeedback.gated_error_sum_le PredictionFeedback"
  # The classical data-processing inequality (FORMAL-CLASSICAL-DPI-DETERMINISTIC-SUMMARY).
  "ClassicalDPI.mutualInformation_summary_le ClassicalDPI"
  "PredictionFeedback.summary_admitted_receipts_of_summary PredictionFeedback"
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
