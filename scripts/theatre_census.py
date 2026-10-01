#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""Theatre in the Lean tree: proved statements that restate their own file's literals.

A statement is theatre when every identifier it compares unfolds, inside its own file, to a literal (a bool, a
string, a numeral, `True`/`False`, a bare constructor) or to a conjunction, disjunction or negation of such: proving
it checks that the file says what it says. Evaluating a function that computes over data (a decision procedure on an
element's configuration, a fold, a product) is a computed fact and is not theatre; neither is any statement over
variables or hypotheses.

Byte-identical in umst-formal and umst-formal-double-slit. `--json` lists every theatre declaration with its file and
line; `--summary` prints counts per directory; `--check N` fails when the count exceeds N (a ratchet that only falls).
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from collections import Counter

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from formal_census import strip_comments  # noqa: E402

DECL = re.compile(r"^(?:private\s+|protected\s+)?(?:@\[[^\]]*\]\s*)?(theorem|lemma)\s+(\S+)", re.M)
DEF = re.compile(r"^(?:private\s+|protected\s+)?(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z_][\w.']*)"
                 r"\s*(?::\s*([^:=]+?))?\s*:=\s*(.+?)(?=^\S|\Z)", re.M | re.S)
BOUNDARY = re.compile(r"^(?:@\[|private\s|protected\s|noncomputable\s|theorem\s|lemma\s|def\s|abbrev\s|structure\s|"
                      r"inductive\s|class\s|instance\b|example\b|namespace\s|end\b|section\b|open\s|variable\b|"
                      r"set_option\s|#|attribute\s|macro\b|syntax\b|notation\b|universe\s)", re.M)
LITERAL = re.compile(r'^\(?\s*(true|false|True|False|"[^"]*"|-?\d[\d_]*(\s*:\s*\w+)?|\.\w+|\w+\.\w+|\[\]|none|\(\))\s*\)?$')
CONNECTIVES = re.compile(r"\s*(&&|\|\||∧|∨|¬|!|=|≠|\(|\))\s*")
KEYWORDS = {"true", "false", "True", "False", "none", "some", "if", "then", "else", "Nat", "String", "Bool", "Prop",
            "Int", "decide", "rfl", "by", "fun", "let", "in"}


def literal_defs(text: str) -> dict[str, str]:
    """Definitions of this file whose body is a literal or a boolean combination of this file's literal definitions."""
    raw = {m.group(1).split(".")[-1]: " ".join(m.group(3).split()) for m in DEF.finditer(text)}
    lit: dict[str, str] = {}
    changed = True
    while changed:
        changed = False
        for name, body in raw.items():
            if name in lit:
                continue
            if LITERAL.match(body):
                lit[name] = body
                changed = True
                continue
            atoms = [a for a in CONNECTIVES.split(body) if a and not CONNECTIVES.fullmatch(a)]
            if atoms and all(LITERAL.match(a) or a in lit for a in atoms) and any(a in lit for a in atoms):
                lit[name] = body
                changed = True
    return lit


def theatre(text: str) -> list[tuple[str, int, str]]:
    """(name, line, statement) for each theatre declaration of one Lean file."""
    lit = literal_defs(text)
    out = []
    for m in DECL.finditer(text):
        nxt = BOUNDARY.search(text, m.end())
        body = text[m.start():nxt.start() if nxt else len(text)]
        head, _, _ = body.partition(":=")
        stmt = head[m.end() - m.start():]
        if re.match(r"\s*[({\[⦃]", stmt) or re.search(r"[∀∃→↔]|\bfun\b", stmt):
            continue  # a statement over variables or hypotheses
        stmt = stmt.strip().lstrip(":").strip()
        names = [n.split(".")[-1] for n in re.findall(r"[A-Za-z_][\w.']*", stmt) if n not in KEYWORDS]
        if names and all(n in lit for n in names):
            out.append((m.group(2), text.count("\n", 0, m.start()) + 1, " ".join(stmt.split())))
    return out


def census() -> dict[str, list[tuple[str, int, str]]]:
    files = subprocess.run(["git", "-C", ROOT, "ls-files", "Lean/*.lean", "Lean/**/*.lean"], capture_output=True,
                           text=True).stdout.split()
    out = {}
    for f in sorted(set(files)):
        if "/.lake/" in f:
            continue
        with open(os.path.join(ROOT, f), encoding="utf-8", errors="replace") as fh:
            hits = theatre(strip_comments(fh.read(), "--", ("/-", "-/")))
        if hits:
            out[f] = hits
    return out


def main() -> int:
    c = census()
    total = sum(len(v) for v in c.values())
    if "--json" in sys.argv:
        print(json.dumps({f: [{"name": n, "line": ln, "statement": s} for n, ln, s in v] for f, v in c.items()},
                         indent=1, ensure_ascii=False))
    elif "--check" in sys.argv:
        bound = int(sys.argv[sys.argv.index("--check") + 1])
        if total > bound:
            print(f"FAIL: {total} theatre declarations (bound {bound}); scripts/theatre_census.py --json lists them",
                  file=sys.stderr)
            return 1
        print(f"OK: {total} theatre declarations (bound {bound})")
    else:
        by = Counter()
        for f, v in c.items():
            by["/".join(f.split("/")[1:-1]) or "."] += len(v)
        for d, n in by.most_common():
            print(f"{n:6d}  {d}")
        print(f"{total:6d}  total")
    return 0


if __name__ == "__main__":
    sys.exit(main())
