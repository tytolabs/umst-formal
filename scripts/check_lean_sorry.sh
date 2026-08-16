#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
# Multi-repo sorry gate. Excludes sorry_detector_fixture by PURPOSE marker.
# Matches line-start sorry/admit AND inline `by sorry` / `by admit` (UCRS stubs).
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WS="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$WS"
python3 - "$WS" <<'PY'
import re, sys
from pathlib import Path
ws = Path(sys.argv[1])
skip = {".lake", "node_modules", "old", "archived", "scratch", "target", ".git"}
LINE_START = re.compile(r"^[ \t]*(sorry|admit)\b")
BY_SORRY = re.compile(r"\bby\s+(sorry|admit)\b")
PURPOSE = "sorry_detector_fixture"
COMMENT = re.compile(r"--.*$")

def discover():
    roots = []
    skip2 = skip | {"fixtures"}
    search = ws / "umst"
    if not search.is_dir():
        return []
    for lean_dir in search.rglob("Lean"):
        if not lean_dir.is_dir():
            continue
        if any(p in skip2 for p in lean_dir.parts) or "packages" in lean_dir.parts:
            continue
        if any(p.suffix == ".lean" and p.name != "lakefile.lean" for p in lean_dir.rglob("*.lean") if ".lake" not in p.parts):
            roots.append(lean_dir)
    return sorted(set(roots))

found = 0
fixture_skipped = 0
hits = []
for lean in discover():
    for p in sorted(lean.rglob("*.lean")):
        if p.name == "lakefile.lean" or ".lake" in p.parts:
            continue
        text = p.read_text(encoding="utf-8", errors="replace")
        if PURPOSE in text:
            fixture_skipped += 1
            continue
        for i, line in enumerate(text.splitlines(), 1):
            code = COMMENT.sub("", line)
            if LINE_START.match(code) or BY_SORRY.search(code):
                hits.append(f"{p}:{i}:{line.strip()}")
                found = 1
for h in hits:
    print(h)
if found:
    print(f"check_lean_sorry: found {len(hits)} sorry/admit in discovered Lean trees", file=sys.stderr)
    sys.exit(1)
print(f"check_lean_sorry: OK (no production sorry/admit; fixtures_skipped={fixture_skipped})")
PY
