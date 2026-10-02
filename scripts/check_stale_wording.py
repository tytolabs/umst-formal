#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""Fail on wording that contradicts the formal state in tracked sources and living documents.

The second law is the predicate `UMST.ProcessFamily.SecondLaw`, a hypothesis of every physical result, and no
repository declares a Lean `axiom`; `physicalSecondLaw` names the predicate's erase instance. Dated records keep
the wording of their date: the changelog, retirement ledgers, published preprints and the improvements log.
Shared byte-identical by umst-formal and umst-formal-double-slit.
"""
from __future__ import annotations

import re
import subprocess
import sys

STALE = [
    (re.compile(r"\b(sole|single|only)\s+(explicit\s+)?(physic(s|al)\s+|project\s+)?[`*]*axiom\b", re.I),
     "the law is the predicate SecondLaw; no repository declares an axiom"),
    (re.compile(r"\bone\s+(explicit\s+)?(physic(s|al)|project)\s+[`*]*axiom\b", re.I),
     "the law is the predicate SecondLaw; no repository declares an axiom"),
    (re.compile(r"\bthe\s+only\s+axiom\b", re.I), "no repository declares an axiom"),
    (re.compile(r"\*\*1\*\*\s+(physical\s+)?(project\s+)?[`*]*axiom", re.I), "no repository declares an axiom"),
    (re.compile(r"\*\*Axiom\*\*\s+`physicalSecondLaw`"), "physicalSecondLaw is the erase instance of SecondLaw"),
    (re.compile(r"`?physicalSecondLaw`?\*{0,2}\s+\(axiom\)"), "physicalSecondLaw is the erase instance of SecondLaw"),
    (re.compile(r"\b[Ss]hared\s+`physicalSecondLaw`\s+axiom"), "physicalSecondLaw is the erase instance of SecondLaw"),
    (re.compile(r"\bespinosito", re.I), "renamed espositoConditions"),
    (re.compile(r"\bphysicalSecondLaw_uniform_binary\b"), "retired; the negative probe alone names it"),
]

DATED = re.compile(r"^(CHANGELOG\.md|retirements/|Docs/Preprint/|Docs/IMPROVEMENTS-SINCE-ORIGIN\.md)")
# The negative regression probe and the workflow steps that check it name the retired theorem by design.
PROBE = re.compile(r"^(Lean/tests/AxiomProbe\.lean|\.github/workflows/)")
SELF = "scripts/check_stale_wording.py"
TEXT = re.compile(r"\.(md|lean|v|agda|hs|rs|py|sh|toml|tex|txt|yml|yaml)$")


def main() -> int:
    files = subprocess.run(["git", "ls-files"], capture_output=True, text=True, check=True).stdout.split()
    hits = []
    for f in files:
        if f == SELF or DATED.match(f) or not TEXT.search(f):
            continue
        try:
            lines = open(f, encoding="utf-8").read().splitlines()
        except (UnicodeDecodeError, FileNotFoundError, IsADirectoryError):
            continue
        for n, line in enumerate(lines, 1):
            for rx, why in STALE:
                if rx.search(line) and not (PROBE.match(f) and "uniform_binary" in rx.pattern):
                    hits.append(f"{f}:{n}: {why}: {line.strip()[:160]}")
    for h in hits:
        print(h)
    print(f"stale wording: {len(hits)} line(s)")
    return 1 if hits else 0


if __name__ == "__main__":
    sys.exit(main())
