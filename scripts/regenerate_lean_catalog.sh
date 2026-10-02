#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
# Regenerate artifacts/catalog.json (+ lock) from Lean/ tree.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
EXPORT="${UMST_LEAN_EXPORT_SCRIPT:-$ROOT/../umst-formal-double-slit/tools/lean_export/export_catalog.py}"

if [[ ! -f "$EXPORT" ]]; then
  echo "FAIL: export_catalog.py not found at $EXPORT" >&2
  exit 1
fi

python3 "$EXPORT" --lean-root "$ROOT/Lean" --out "$ROOT/artifacts/catalog.json"
