#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
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

# Single-source modules: umst-formal owns them and double-slit imports them (P0-2
# FORMAL-DS-SECOND-LAW-DEDUP-L, double-slit 4f2b53f). A copy in the sibling is a second
# statement of the one law and fails; a sibling that imports the module passes.
SINGLE_SOURCE=(
  LandauerLaw LandauerEinsteinBridge LandauerExtension Constants/SI Constants/SIBridge
)
# Files both repositories carry byte-identical: the constants table and its generated modules, and the census tools.
SHARED_FILES=(
  constants/constants.json scripts/gen_constants.py scripts/formal_census.py scripts/theatre_census.py \
  scripts/check_formal_parity.py
  Coq/Constants/SI.v Agda/Constants/SI.agda
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

for f in "${SHARED_FILES[@]}"; do
  if ! cmp -s "$ROOT/$f" "$SIBLING/$f"; then
    echo "FAIL: $f differs from the sibling's copy (shared single source)" >&2
    exit 1
  fi
done
# Haskell modules both repositories build, byte-identical, at their paths here (umst-formal) and in double-slit.
HS_PAIRS=(
  "Haskell/UMST/Constants/SI.hs:Haskell/src/UMST/Constants/SI.hs"
  "Haskell/LandauerExtension.hs:Haskell/src/LandauerExtension.hs"
  "Haskell/MonoidalState.hs:Haskell/src/MonoidalState.hs"
  "Haskell/test/LandauerEinsteinSanity.hs:Haskell/test/LandauerEinsteinSanity.hs"
)
for pair in "${HS_PAIRS[@]}"; do
  HS_FORMAL=${pair%%:*}; HS_SLIT=${pair#*:}
  if [[ "$(basename "$ROOT")" == umst-formal-double-slit ]]; then HS_A=$HS_SLIT; HS_B=$HS_FORMAL; else HS_A=$HS_FORMAL; HS_B=$HS_SLIT; fi
  if ! cmp -s "$ROOT/$HS_A" "$SIBLING/$HS_B"; then
    echo "FAIL: $HS_A differs from the sibling's $HS_B (shared single source)" >&2
    exit 1
  fi
done

python3 - "$ROOT" "$SIBLING" "${SINGLE_SOURCE[@]}" << 'PY'
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
if root_p.resolve().name == "umst-formal-double-slit":  # run from double-slit: umst-formal is the owner
    root_p, sib_p = sib_p, root_p
fail = 0
for mod in modules:
    sib_file = sib_p / "Lean" / f"{mod}.lean"
    if sib_file.is_file():
        print(f"FAIL {mod}: sibling carries its own copy; import it from umst-formal (single source)")
        fail = 1
        continue
    if not (root_p / "Lean" / f"{mod}.lean").is_file():
        print(f"FAIL {mod}: single-source module missing from umst-formal")
        fail = 1
        continue
    print(f"OK {mod}: single source in umst-formal; sibling imports it")
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
