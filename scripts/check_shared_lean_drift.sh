#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Statement-level drift gate for cross-repo shared Lean modules.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
case "$(basename "$ROOT")" in
  umst-formal-double-slit) DEFAULT_SIBLING=umst-formal ;;
  *) DEFAULT_SIBLING=umst-formal-double-slit ;;
esac
SIBLING_NAME="${UMST_FORMAL_SIBLING:-$DEFAULT_SIBLING}"
SIBLING="${UMST_FORMAL_SIBLING_DIR:-$ROOT/../$SIBLING_NAME}"

# Shared modules with identical statement contracts in both formal repos.
# Science-cartridge relocations (formal side only):
#   Gate      → Core/Gate + Concrete/Gate + Compat/Gate (name-subset vs flat sibling)
#   Activation → Concrete/Activation
MODULES=(
  Gate LandauerLaw Naturality Activation FiberedActivation
  LandauerEinsteinBridge LandauerExtension MonoidalState
)

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

def decl_names(stmts: list[str]) -> set[tuple[str, str]]:
    names: set[tuple[str, str]] = set()
    for s in stmts:
        m = re.match(r"^(theorem|lemma|def|axiom)\s+([^\s:(]+)", s)
        if m:
            names.add((m.group(1), m.group(2)))
    return names

# formal path(s) relative to Lean/, sibling path relative to Lean/
SPECIAL_FORMAL: dict[str, list[str]] = {
    "Gate": ["Core/Gate.lean", "Concrete/Gate.lean", "Compat/Gate.lean"],
    "Activation": ["Concrete/Activation.lean"],
}
NAME_SUBSET_MODULES = {"Gate"}

root, sibling, *modules = sys.argv[1:]
root_p, sib_p = Path(root), Path(sibling)
fail = 0
for mod in modules:
    sib_file = sib_p / "Lean" / f"{mod}.lean"
    if not sib_file.is_file():
        print(f"FAIL {mod}: missing sibling file")
        fail = 1
        continue
    formal_rels = SPECIAL_FORMAL.get(mod, [f"{mod}.lean"])
    formal_files = [root_p / "Lean" / rel for rel in formal_rels]
    missing_local = [str(p) for p in formal_files if not p.is_file()]
    if missing_local:
        print(f"FAIL {mod}: missing formal file(s) {missing_local}")
        fail = 1
        continue
    sa: list[str] = []
    for p in formal_files:
        sa.extend(extract_statements(p))
    sb = extract_statements(sib_file)
    if mod in NAME_SUBSET_MODULES:
        na, nb = decl_names(sa), decl_names(sb)
        if not nb <= na:
            print(f"FAIL {mod}: sibling declarations not covered ({len(nb - na)} missing)")
            fail = 1
        else:
            print(f"OK {mod}: {len(nb)} sibling decls ⊆ {len(na)} formal decls")
    elif sa != sb:
        print(f"FAIL {mod}: statement divergence ({len(sa)} vs {len(sb)})")
        fail = 1
    else:
        print(f"OK {mod}: {len(sa)} statements")
sys.exit(1 if fail else 0)
PY
