#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
#
# CI hook — Rust↔Lean differential fixture (coordination cost witness grid).
# Track 7 / LEAN-BRIDGE-RDI round-2 · tier: witnessed-not-proved · EXPECTED_PROVED_COUNT=0
#
# Default path (no lake required):
#   bash egoff/umst-formal/scripts/lean_bridge_coordination_cost_ci.sh
#
# Regenerate fixture from Lean SI constants (optional):
#   LEAN_BRIDGE_REGEN_FIXTURE=1 bash egoff/umst-formal/scripts/lean_bridge_coordination_cost_ci.sh
#
# Witness receipt (optional):
#   LEAN_BRIDGE_WRITE_RECEIPT=1 bash egoff/umst-formal/scripts/lean_bridge_coordination_cost_ci.sh
#
# Non-claims: fixture GREEN ≠ cert Proved · 42 thm ≠ runtime Proved · INV4 stays 3/4

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FORMAL_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
WORKSPACE_ROOT="$(cd "$FORMAL_ROOT/../.." && pwd)"
FIXTURE="$WORKSPACE_ROOT/crates/umst-bench/fixtures/lean_bridge_coordination_cost_grid.json"
EXPORT_PY="$SCRIPT_DIR/export_coordination_cost_witness_grid.py"
RECEIPT_DIR="$WORKSPACE_ROOT/outputs/.tmp/grok75_jobs"
RECEIPT_FILE="$RECEIPT_DIR/lean_bridge_ci_witness_r2.md"

if [[ ! -f "$EXPORT_PY" ]]; then
  echo "FAIL: missing export script at $EXPORT_PY" >&2
  exit 1
fi

if [[ "${LEAN_BRIDGE_REGEN_FIXTURE:-0}" == "1" ]]; then
  echo "== lean_bridge: regenerating fixture from Lean SI constants (round-2) =="
  python3 "$EXPORT_PY" --write "$FIXTURE"
  if command -v lake >/dev/null 2>&1 && [[ -d "$FORMAL_ROOT/Lean" ]]; then
    echo "== lean_bridge: optional lake build CoordinationCost + CoordinationCostP6 (docs witness) =="
    (cd "$FORMAL_ROOT/Lean" && lake build CoordinationCost CoordinationCostP6) \
      || echo "WARN: lake build skipped (non-blocking for Rust conformance)"
  fi
fi

if [[ ! -f "$FIXTURE" ]]; then
  echo "FAIL: fixture missing at $FIXTURE (set LEAN_BRIDGE_REGEN_FIXTURE=1 to generate)" >&2
  exit 1
fi

ROW_COUNT="$(python3 -c "import json; print(len(json.load(open('$FIXTURE'))['rows']))")"
SCHEMA="$(python3 -c "import json; print(json.load(open('$FIXTURE'))['schema_version'])")"
ROUND="$(python3 -c "import json; d=json.load(open('$FIXTURE')); print(d.get('round', 1))")"
echo "== lean_bridge: fixture $SCHEMA round=$ROUND rows=$ROW_COUNT =="

echo "== lean_bridge: Rust conformance test (umst-bench) =="
cd "$WORKSPACE_ROOT/crates/umst-bench"
TEST_LOG="$(mktemp)"
cargo test --test lean_bridge_coordination_cost -- --nocapture 2>&1 | tee "$TEST_LOG"
TEST_COUNT="$(rg -c '^test ' "$TEST_LOG" || true)"
PASS_COUNT="$(rg -c '\.\.\. ok$' "$TEST_LOG" || true)"

if [[ "${LEAN_BRIDGE_WRITE_RECEIPT:-0}" == "1" ]]; then
  mkdir -p "$RECEIPT_DIR"
  cat >"$RECEIPT_FILE" <<EOF
# lean_bridge CI witness (round-2)

| Field | Value |
|-------|-------|
| **Schema** | \`$SCHEMA\` |
| **Round** | $ROUND |
| **Rows** | $ROW_COUNT |
| **Tier** | witnessed-not-proved |
| **EXPECTED_PROVED_COUNT** | 0 |
| **Tests** | $PASS_COUNT passed |

\`\`\`
$(tail -n 8 "$TEST_LOG")
\`\`\`
EOF
  echo "Wrote CI witness receipt: $RECEIPT_FILE"
fi

rm -f "$TEST_LOG"

echo "PASS: lean_bridge_coordination_cost_ci (witnessed-not-proved · EXPECTED_PROVED_COUNT=0 · round=$ROUND · rows=$ROW_COUNT)"
