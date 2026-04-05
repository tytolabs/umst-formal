#!/usr/bin/env bash
# Fail if tactic sorry/admit appears in versioned Lean sources under Lean/ (excludes .lake).
# Portable: find + grep (no ripgrep required).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
found=0
while IFS= read -r f; do
  [[ -z "$f" ]] && continue
  if grep -qE '^[[:space:]]*(sorry|admit)\b' "$f" 2>/dev/null; then
    grep -nE '^[[:space:]]*(sorry|admit)\b' "$f" || true
    found=1
  fi
done < <(find Lean -name '*.lean' ! -path '*/.lake/*' 2>/dev/null)
if [[ "$found" -ne 0 ]]; then
  echo "check_lean_sorry: found sorry/admit in Lean/" >&2
  exit 1
fi
echo "check_lean_sorry: OK (no line-start sorry/admit in Lean/*.lean)"
