#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""Fail when artifacts/catalog.json no longer describes the tracked Lean sources.

Rust and document pins (content_sha256 + declaration) are checked against this catalog, so a stale catalog lets
every pin agree with it while disagreeing with the proofs. Each tracked Lean file must appear with its current
SHA-256 and declarations; each catalog module must be a tracked file. Regenerate with
scripts/regenerate_lean_catalog.sh.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
# The exporter's declaration grammar (umst-formal-double-slit tools/lean_export/export_catalog.py), plus abbrev.
DECL_RE = re.compile(r"^\s*(theorem|lemma|axiom|def|instance|inductive|structure|class)\s+([^\s:]+)", re.MULTILINE)
ABBREV_RE = re.compile(r"^\s*abbrev\s+([^\s:]+)", re.MULTILINE)


def main() -> int:
    catalog = json.loads((ROOT / "artifacts/catalog.json").read_text(encoding="utf-8"))
    tracked = {
        p[len("Lean/"):]
        for p in subprocess.run(["git", "ls-files", "Lean"], cwd=ROOT, capture_output=True, text=True, check=True).stdout.split()
        if p.endswith(".lean")
    }
    modules = {m["path"]: m for m in catalog["modules"]}
    problems = []
    for rel in sorted(tracked - set(modules)):
        problems.append(f"missing from catalog: Lean/{rel}")
    for rel in sorted(set(modules) - tracked):
        problems.append(f"catalog lists an untracked or retired file: Lean/{rel}")
    for rel in sorted(tracked & set(modules)):
        raw = (ROOT / "Lean" / rel).read_bytes()
        m = modules[rel]
        if hashlib.sha256(raw).hexdigest() != m["content_sha256"]:
            problems.append(f"content_sha256 stale: Lean/{rel}")
            continue
        text = raw.decode("utf-8", errors="replace")
        want = {n for _, n in DECL_RE.findall(text)} | set(ABBREV_RE.findall(text))
        have = {n for names in (m.get("declarations") or {}).values() for n in names}
        if want != have:
            problems.append(f"declarations stale: Lean/{rel}")
    for p in problems:
        print(p)
    print(f"catalog freshness: {len(tracked)} tracked Lean files, {len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
