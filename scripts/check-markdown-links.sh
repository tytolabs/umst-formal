#!/usr/bin/env bash
# Verify Markdown links (internal + HTTP) for curated docs. Config: scripts/markdown-link-check.json
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
CONFIG="$ROOT/scripts/markdown-link-check.json"
MLC_VERSION="3.12.2"

# Curated list: canonical entrypoints + Docs hub (extend when adding stable prose).
FILES=(
  README.md
  CONTRIBUTING.md
  CHANGELOG.md
  FORMAL_FOUNDATIONS.md
  PROOF-STATUS.md
  SAFETY-LIMITS.md
  Agda/README.md
  Coq/README.md
  Haskell/README.md
  Docs/Architecture-Invariants.md
  Docs/COUNT-METHODOLOGY.md
  Docs/DOCUMENTATION-COVERAGE-PLAN.md
  Docs/FALSIFIABILITY_DASHBOARD.md
  Docs/PROOF-REPLAY.md
  Docs/COMPREHENSIVE-FORMAL-PLAN.md
)

fail=0
for f in "${FILES[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "check-markdown-links: skip missing $f" >&2
    continue
  fi
  if ! npx --yes "markdown-link-check@${MLC_VERSION}" -c "$CONFIG" -q "$f"; then
    echo "check-markdown-links: FAILED $f" >&2
    fail=1
  fi
done

if [[ "$fail" -ne 0 ]]; then
  echo "check-markdown-links: one or more files failed" >&2
  exit 1
fi
echo "check-markdown-links: OK (${#FILES[@]} files)"
