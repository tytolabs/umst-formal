#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Statement-level drift gate for the 8 cross-repo shared Lean modules.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
case "$(basename "$ROOT")" in
  umst-formal-double-slit) DEFAULT_SIBLING=umst-formal ;;
  *) DEFAULT_SIBLING=umst-formal-double-slit ;;
esac
SIBLING_NAME="${UMST_FORMAL_SIBLING:-$DEFAULT_SIBLING}"
SIBLING="${UMST_FORMAL_SIBLING_DIR:-$ROOT/../$SIBLING_NAME}"

# Shared modules with identical statement contracts in both formal repos.
MODULES=(
  Gate LandauerLaw Naturality Activation FiberedActivation
  LandauerEinsteinBridge LandauerExtension MonoidalState
)

# EXCLUDED (by design — not compared here):
# - MeasurementCost / ClassicalMeasurementCost: name collision resolved by umst-formal rename.
# - FormalFoundations: per-repo completion witness (`umst_formal_complete` vs `umst_double_slit_formal_complete`).

if [[ ! -d "$SIBLING/Lean" ]]; then
  echo "FAIL: sibling Lean tree not found at $SIBLING/Lean" >&2
  exit 1
fi

STATS_A="$ROOT/scripts/lean_declaration_stats.py"
STATS_B="$SIBLING/scripts/lean_declaration_stats.py"
if [[ ! -f "$STATS_A" || ! -f "$STATS_B" ]]; then
  echo "FAIL: lean_declaration_stats.py missing" >&2
  exit 1
fi
if ! cmp -s "$STATS_A" "$STATS_B"; then
  echo "FAIL: lean_declaration_stats.py differs from sibling (sync double-slit → formal)" >&2
  exit 1
fi

python3 - "$ROOT" "$SIBLING" "${MODULES[@]}" << 'PY'
import re, sys
from pathlib import Path

def extract_statements(path: Path) -> list[str]:
    out: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if re.match(r"^(axiom|theorem|lemma|def)\s", s):
            if ":=" in s:
                s = s.split(":=", 1)[0].rstrip() + " :="
            out.append(s)
    return out

root, sibling, *modules = sys.argv[1:]
root_p, sib_p = Path(root), Path(sibling)
fail = 0
for mod in modules:
    a = root_p / "Lean" / f"{mod}.lean"
    b = sib_p / "Lean" / f"{mod}.lean"
    if not a.is_file() or not b.is_file():
        print(f"FAIL {mod}: missing file (a={a.is_file()} b={b.is_file()})")
        fail = 1
        continue
    sa, sb = extract_statements(a), extract_statements(b)
    if sa != sb:
        print(f"FAIL {mod}: statement divergence ({len(sa)} vs {len(sb)})")
        fail = 1
    else:
        print(f"OK {mod}: {len(sa)} statements")
sys.exit(1 if fail else 0)
PY
