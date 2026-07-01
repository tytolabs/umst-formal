#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# One-shot local gate for science-cartridge branch (mirrors umst-formal lean.yml + drift).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

echo "== lake build UMST =="
(cd Lean && lake build UMST)

echo "== check_lean_sorry =="
bash scripts/check_lean_sorry.sh

echo "== check_lean_axioms =="
python3 scripts/check_lean_axioms.py

echo "== lean_declaration_stats snapshot =="
python3 scripts/lean_declaration_stats.py --verify-snapshot scripts/expected_lean_declaration_snapshot.json

echo "== check_print_axioms =="
bash scripts/check_print_axioms.sh

echo "== Agda Core/Concrete/Compat =="
make -C Agda check

echo "== Coq Core/Concrete/Compat =="
make -C Coq all

echo "== Haskell Compat shim + QuickCheck =="
(cd Haskell && cabal test umst-properties --test-show-details=streaming)

if [[ -d "${UMST_FORMAL_SIBLING_DIR:-$ROOT/../umst-formal-double-slit}/Lean" ]]; then
  echo "== check_shared_lean_drift =="
  UMST_FORMAL_SIBLING_DIR="${UMST_FORMAL_SIBLING_DIR:-$ROOT/../umst-formal-double-slit}" \
    bash scripts/check_shared_lean_drift.sh
else
  echo "SKIP: sibling umst-formal-double-slit not found"
fi

WORKSPACE_ROOT="$(cd "$ROOT/.." && pwd)"
if [[ -f "$WORKSPACE_ROOT/scripts/check_formal_anchor_resolve.py" ]]; then
  echo "== check_formal_anchor_resolve (workspace) =="
  (cd "$WORKSPACE_ROOT" && python3 scripts/check_formal_anchor_resolve.py)
fi
if [[ -f "$WORKSPACE_ROOT/scripts/check_invariant_manifest.py" ]]; then
  echo "== check_invariant_manifest =="
  (cd "$WORKSPACE_ROOT" && python3 scripts/check_invariant_manifest.py)
fi

echo "verify_science_cartridge: OK"
