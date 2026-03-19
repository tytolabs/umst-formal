#!/usr/bin/env bash
# check-formal-environment.sh — evidence-grade toolchain probe for umst-formal
#
# Usage:
#   ./scripts/check-formal-environment.sh           # print matrix, exit 0
#   ./scripts/check-formal-environment.sh --strict  # exit 1 if any required tool missing
#
# Does not run proof assistants; only reports PATH-resolved binaries and
# optional Rust sibling-path sanity.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
STRICT=0
[[ "${1:-}" == "--strict" ]] && STRICT=1

have() { command -v "$1" >/dev/null 2>&1; }

row() {
  local name="$1" bin="$2" min_note="$3"
  if have "$bin"; then
    ver="$("$bin" --version 2>/dev/null | head -1 || echo "(no --version)")"
    printf '%-14s PASS  %s\n' "$name" "$ver"
    return 0
  else
    printf '%-14s FAIL  %s not in PATH (%s)\n' "$name" "$bin" "$min_note"
    return 1
  fi
}

echo "umst-formal environment check (repo: $ROOT)"
echo "─────────────────────────────────────────────"

missing=0
row "Rust (cargo)" cargo "1.75+" || missing=1
row "Agda" agda "2.6.4+; stdlib via Agda/umst-formal.agda-lib" || missing=1
row "Coq (coqc)" coqc "8.18–8.20 per docs/CI; see PROOF-REPLAY.md for macOS" || missing=1
row "Lean (elan)" elan "recommended; then lake uses Lean/lean-toolchain" || missing=1
row "Lean (lake)" lake "from elan, or standalone" || missing=1
row "GHC" ghc "9.6+" || missing=1
row "cabal" cabal "3.10+" || missing=1
row "nix-shell" nix-shell "optional; shell.nix" || true

echo "─────────────────────────────────────────────"
proto="$ROOT/../umst-prototype-2a/prototype/src/rust/core/Cargo.toml"
if [[ -f "$proto" ]]; then
  echo "Sibling umst-core path: PASS  ($proto)"
else
  echo "Sibling umst-core path: FAIL  expected $proto (clone umst-prototype-2a next to umst-formal)"
  missing=1
fi

if [[ "$STRICT" -eq 1 && "$missing" -ne 0 ]]; then
  echo "Strict mode: one or more requirements missing."
  exit 1
fi
exit 0
