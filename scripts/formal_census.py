#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""Machine-checked content of this repository, per language, measured on tracked files.

Byte-identical in umst-formal and umst-formal-double-slit (scripts/check_shared_lean_drift.sh compares them).

For each of Lean, Coq, Agda and Haskell it counts:

  proved       declarations stated and proved (Lean theorem/lemma, Coq Theorem/Lemma/Corollary/Proposition/Fact/
               Remark/Example ... Qed/Defined, Agda top-level signatures whose type is a proposition, Haskell
               QuickCheck properties)
  closed       the proved declarations that are closed computations: a statement with no variables and no
               hypotheses, proved by evaluation alone (`rfl`, `decide`, `trivial`, `norm_num`, `reflexivity`,
               `refl`). It checks a value, not a law; counted apart so it never inflates the theorem count
  laws         proved − closed: statements over variables or hypotheses
  open         `sorry`, `admit`, `Admitted`, `postulate`, and `axiom`/`Axiom`/`Parameter` declarations

`--json` prints the census; `--markdown` prints the README table; `--check README.md` fails when the README's
census block (between `<!-- census:begin -->` and `<!-- census:end -->`) differs from the measurement, and
`--write README.md` regenerates that block.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
CLOSED = re.compile(r"^\s*(:=\s*)?(by\s+)?(rfl|decide|trivial|native_decide|norm_num|simp|reflexivity|refl|easy)\s*\.?\s*$")
LITERAL_COMPARE = re.compile(r'(=|≠|<|≤|>|≥)\s*("[^"]*"|-?\d[\d_./]*|true|false|True|False)\s*(:=|$)')


def tracked(*patterns: str) -> list[str]:
    out = subprocess.run(["git", "-C", ROOT, "ls-files", *patterns], capture_output=True, text=True).stdout.split()
    return sorted(set(out))


def read(rel: str) -> str:
    try:
        with open(os.path.join(ROOT, rel), encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


def strip_comments(text: str, line: str, block: tuple[str, str]) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith(block[0], i):
            depth += 1
            i += len(block[0])
        elif depth and text.startswith(block[1], i):
            depth -= 1
            i += len(block[1])
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith(line, i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def lean(files: list[str]) -> dict:
    proved = definitional = open_ = 0
    decl = re.compile(r"^(?:private\s+|protected\s+)?(?:@\[[^\]]*\]\s*)?(theorem|lemma)\s+(\S+)(.*)$", re.M)
    for f in files:
        text = strip_comments(read(f), "--", ("/-", "-/"))
        open_ += len(re.findall(r"\bsorry\b", text)) + len(re.findall(r"^\s*axiom\s", text, re.M))
        own = set(re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z_][\w.']*)", text, re.M))
        # a declaration ends at the next top-level command (a column-0 keyword), not only at the next theorem
        boundary = re.compile(r"^(?:@\[|private\s|protected\s|noncomputable\s|theorem\s|lemma\s|def\s|abbrev\s|"
                              r"structure\s|inductive\s|class\s|instance\b|example\b|namespace\s|end\b|section\b|"
                              r"open\s|variable\b|set_option\s|#|attribute\s|macro\b|syntax\b|notation\b|universe\s)",
                              re.M)
        for m in decl.finditer(text):
            proved += 1
            nxt = boundary.search(text, m.end())
            body = text[m.start():nxt.start() if nxt else len(text)]
            stmt, _, proof = body.partition(":=")
            proof = proof.strip()
            one_step = bool(CLOSED.match(":= " + proof)) and "\n" not in proof
            head = stmt[len(m.group(1)) + 1 + len(m.group(2)) + 1:]
            binders = re.match(r"\s*[({\[⦃]", head) is not None or re.search(r"[∀∃→↔]|\bfun\b|Π|Σ", head)
            if one_step and not binders:
                definitional += 1
    return {"files": len(files), "proved": proved, "definitional": definitional,
            "substantive": proved - definitional, "open": open_}


def coq(files: list[str]) -> dict:
    proved = definitional = open_ = 0
    head = re.compile(r"^\s*(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example)\s+([\w']+)(.*?)Proof\.(.*?)(Qed|Defined|Admitted)\.",
                      re.M | re.S)
    for f in files:
        text = strip_comments(read(f), "\x00", ("(*", "*)"))
        open_ += len(re.findall(r"\bAdmitted\.|\badmit\s*\.", text))
        open_ += len(re.findall(r"^\s*(Axiom|Parameter|Conjecture)\s", text, re.M))
        own = set(re.findall(r"^\s*Definition\s+([\w']+)", text, re.M))
        for m in head.finditer(text):
            if m.group(5) == "Admitted":
                continue
            proved += 1
            stmt, proof = m.group(3), m.group(4).strip()
            binders = re.match(r"\s*\(", stmt) is not None or re.search(r"\bforall\b|\bexists\b|->|<->", stmt)
            evaluation = re.fullmatch(r"((vm_compute|compute|simpl|cbv|unfold\s[\w' ]+)\s*\.\s*)*"
                                      r"(reflexivity|trivial|easy|auto|lia|lra|now\s+\w+)\s*\.?", proof)
            if evaluation and not binders:
                definitional += 1
    return {"files": len(files), "proved": proved, "definitional": definitional,
            "substantive": proved - definitional, "open": open_}


PROP = re.compile(r"≡|≤|<|≥|>|×|⊎|¬|∀|Σ|∃|→|Dec\b|All\b|Any\b|Admits|Physical|Law")


def agda(files: list[str]) -> dict:
    proved = definitional = open_ = 0
    for f in files:
        text = strip_comments(read(f), "--", ("{-", "-}"))
        open_ += len(re.findall(r"^\s*postulate\b", text, re.M))
        lines = text.split("\n")
        own = set()
        for i, ln in enumerate(lines):
            m = re.match(r"^([^\s:()][^\s:]*)\s+:\s+(.+)$", ln)
            if not m or m.group(1) in ("module", "open", "import", "record", "data", "field", "constructor"):
                continue
            name, typ = m.group(1), m.group(2)
            j = i + 1
            while j < len(lines) and lines[j].startswith((" ", "\t")) and not lines[j].strip().startswith(name):
                typ += " " + lines[j].strip()
                j += 1
            if not PROP.search(typ) or re.search(r"\bSet\b\s*$", typ):
                own.add(name)
                continue
            proved += 1
            defn = next((lines[k] for k in range(j, min(j + 4, len(lines))) if lines[k].startswith(name)), "")
            if re.search(r"=\s*refl\s*$", defn) and "≡" in typ and not re.search(r"[∀→]|\{|\(", typ):
                definitional += 1
    return {"files": len(files), "proved": proved, "definitional": definitional,
            "substantive": proved - definitional, "open": open_}


def haskell(files: list[str]) -> dict:
    """QuickCheck properties, plus the entries of the generated statement lists (`checks`, `derivations`) that the
    test suite evaluates: each entry is one statement the proof languages prove, checked by evaluation."""
    props = 0
    for f in files:
        text = read(f)
        props += len(re.findall(r"^prop_\w+\s*::", text, re.M))
        for m in re.finditer(r"^(checks|derivations)\s*::.*?\n\1\s*=\n(.*?)\n\s*\]", text, re.M | re.S):
            props += len(re.findall(r"^\s*[\[,]\s*\(\"", m.group(2), re.M))
    return {"files": len(files), "proved": props, "definitional": 0, "substantive": props, "open": 0,
            "note": "QuickCheck properties and checked statements: tested, not proved"}


def census() -> dict:
    lean_files = [f for f in tracked("*.lean") if "/.lake/" not in f and f.startswith("Lean/")]
    unchecked = set()
    if os.path.exists(os.path.join(ROOT, "Lean/lean-unchecked.txt")):
        unchecked = {("Lean/" + ln.split()[0]) for ln in read("Lean/lean-unchecked.txt").splitlines()
                     if ln.strip() and not ln.startswith("#")}
    return {
        "Lean": lean([f for f in lean_files if f not in unchecked]),
        "Coq": coq([f for f in tracked("*.v") if f.startswith("Coq/")]),
        "Agda": agda([f for f in tracked("*.agda") if f.startswith("Agda/")]),
        "Haskell": haskell(tracked("*.hs")),
    }


def markdown(c: dict) -> str:
    rows = ["| Language | Files | Proved | Laws (over variables or hypotheses) | Closed computations | Open (sorry, admit, axiom, postulate) |",
            "|---|---:|---:|---:|---:|---:|"]
    for lang, v in c.items():
        proved = f"{v['proved']} checked" if lang == "Haskell" else str(v["proved"])
        rows.append(f"| {lang} | {v['files']} | {proved} | {v['substantive']} | {v['definitional']} | {v['open']} |")
    return "\n".join(rows)


def main() -> int:
    c = census()
    if "--json" in sys.argv:
        print(json.dumps(c, indent=2))
        return 0
    if "--write" in sys.argv:
        readme = sys.argv[sys.argv.index("--write") + 1]
        text = read(readme)
        new, n = re.subn(r"<!-- census:begin -->\n.*?\n<!-- census:end -->",
                         lambda _: "<!-- census:begin -->\n" + markdown(c) + "\n<!-- census:end -->", text, flags=re.S)
        if not n:
            print(f"FAIL: {readme} has no census block", file=sys.stderr)
            return 1
        with open(os.path.join(ROOT, readme), "w", encoding="utf-8") as fh:
            fh.write(new)
        print(f"wrote the census block of {readme}")
        return 0
    if "--check" in sys.argv:
        readme = sys.argv[sys.argv.index("--check") + 1]
        text = read(readme)
        m = re.search(r"<!-- census:begin -->\n(.*?)\n<!-- census:end -->", text, re.S)
        if not m:
            print(f"FAIL: {readme} has no census block", file=sys.stderr)
            return 1
        if m.group(1).strip() != markdown(c).strip():
            print(f"FAIL: {readme} census block is stale; regenerate with scripts/formal_census.py --markdown",
                  file=sys.stderr)
            print(markdown(c), file=sys.stderr)
            return 1
        print(f"OK: {readme} census matches the measurement")
        return 0
    print(markdown(c))
    return 0


if __name__ == "__main__":
    sys.exit(main())
