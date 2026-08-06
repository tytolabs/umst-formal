#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
"""Export coordination-cost witness grid for Rust↔Lean differential fixture.

Mirrors Lean SI constants from ``LandauerEinsteinBridge.lean``:
  kBoltzmannSI = 1380649 / 10^29
  coordinationSavingJoules miBits T = kBoltzmannSI * T * ln(2) * miBits

Tier: **witnessed-not-proved** — formula alignment only, NOT proof transfer.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SCHEMA_VERSION = "lean_bridge_coordination_cost_v1"
K_BOLTZMANN_SI = 1380649 / (10**29)

# Round-1 rows — same physical-MI grid as ``umst-arcs/tests/coordination_cost_identity.rs``.
PHYSICAL_MI_FIXTURES_R1: list[tuple[float, float, float, float]] = [
    (4.0, 4.0, 0.0, 300.0),
    (4.0, 4.0, 0.5, 300.0),
    (8.0, 6.0, 2.0, 300.0),
    (1.0, 1.0, 1.0, 300.0),
    (4.0, 4.0, 1.0, 400.0),
]

# Round-2 expansion — temperature scaling + intermediate MI (witnessed-not-proved).
PHYSICAL_MI_FIXTURES_R2: list[tuple[float, float, float, float]] = [
    (2.0, 2.0, 0.25, 273.15),
    (4.0, 4.0, 0.0, 500.0),
    (6.0, 6.0, 1.5, 77.0),
    (3.0, 3.0, 0.75, 300.0),
    (2.0, 2.0, 2.0, 400.0),
]

PHYSICAL_MI_FIXTURES: list[tuple[float, float, float, float]] = (
    PHYSICAL_MI_FIXTURES_R1 + PHYSICAL_MI_FIXTURES_R2
)

# n-ary vs pairwise soundness — documented in LEAN_BRIDGE_RDI; not proof transfer.
SOUNDNESS_TABLE: list[dict[str, object]] = [
    {
        "id": "n2_global_eq_pairwise",
        "n_agents": 2,
        "verdict": "equivalent_at_n2",
        "lean_anchor": "UMST.CoordinationCost.coordinationSavingGlobal_eq_pairwise",
        "rust_anchor": "umst_arcs::coordination_saving_global_joules",
        "tier": "witnessed-not-proved",
        "note": "At n=2, global floor reduces to pairwise SSOT on declared MI scalar.",
    },
    {
        "id": "n_ary_not_pairwise_sum",
        "n_agents": 3,
        "verdict": "non_equivalent",
        "lean_anchor": "UMST.CoordinationCost.multiInformationBits",
        "rust_anchor": "umst_arcs::multi_information_bits",
        "tier": "documented_only",
        "note": "Total correlation I_n ≠ sum of pairwise MI — floor projections differ.",
    },
]


def coordination_saving_joules(mi_bits: float, temperature_k: float) -> float:
    return K_BOLTZMANN_SI * temperature_k * math.log(2.0) * mi_bits


def build_document() -> dict[str, Any]:
    rows = []
    for h_a, h_b, mi_bits, temperature_k in PHYSICAL_MI_FIXTURES:
        rows.append(
            {
                "h_a": h_a,
                "h_b": h_b,
                "mi_bits": mi_bits,
                "temperature_k": temperature_k,
                "coordination_saving_joules": coordination_saving_joules(
                    mi_bits, temperature_k
                ),
            }
        )
    return {
        "schema_version": SCHEMA_VERSION,
        "round": 2,
        "tier": "witnessed-not-proved",
        "expected_proved_count": 0,
        "lean_anchor": "UMST.CoordinationCost.coordinationSavingJoules",
        "rust_anchor": "umst_arcs::coordination_saving_joules",
        "fixture_rounds": {
            "r1_rows": len(PHYSICAL_MI_FIXTURES_R1),
            "r2_rows": len(PHYSICAL_MI_FIXTURES_R2),
            "total_rows": len(PHYSICAL_MI_FIXTURES),
        },
        "soundness_table": SOUNDNESS_TABLE,
        "si_constants": {
            "k_boltzmann_si_rational": "1380649/10^29",
            "k_boltzmann_si_float": K_BOLTZMANN_SI,
            "ln_2_source": "math.log(2) — Lean Mathlib Real.log 2",
        },
        "non_claims": [
            "42 Lean theorems ≠ runtime Proved",
            "fixture GREEN ≠ cert Proved",
            "Landauer floor ≠ wall-clock energy",
        ],
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write",
        metavar="PATH",
        help="Write fixture JSON to PATH (default: stdout only)",
    )
    args = parser.parse_args()
    doc = build_document()
    payload = json.dumps(doc, indent=2) + "\n"
    if args.write:
        path = Path(args.write)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(payload, encoding="utf-8")
        print(f"Wrote {path} ({len(doc['rows'])} rows)")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
