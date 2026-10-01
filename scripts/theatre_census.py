#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""Theatre in the Lean tree: proved statements that add nothing to what the file already says.

Four kinds, each decided from the text of one file:

  literal    an equation, disequation or boolean combination (no order, no arithmetic) whose every identifier
             unfolds, inside its file, to a literal (a bool, a string, a
             numeral, `True`/`False`, a bare constructor), possibly through definitions with ignored parameters
             (`def f (x : A) : Prop := False`), or to a conjunction, disjunction or negation of such: proving it
             checks that the file says what it says;
  reflexive  the statement is `a = a` or `a ↔ a`;
  alias      the proof applies another declaration of the tree to the statement's own binders in order and nothing
             else, and that declaration states the same proposition over the same binders: a second name for it;
  duplicate  the statement, binders included, repeats an earlier declaration of the same file;
  definitional the statement is `f a₁ … aₙ = e` (or `↔`), proved by `rfl`, where `f` is defined in the same file with
             body `e` after its parameters are replaced by `a₁ … aₙ`: the theorem restates the definition;
  trivial    the statement is `True`;
  table      the statement is `f c = v` for a constructor `c` and a literal `v`, proved by `rfl` or `decide`, where `f`
             is defined in the same file by cases whose every result is a literal: it reads back a row of the table;
  unused-literal an order or arithmetic fact about this file's literals (`0 < marker`) that no other declaration of
             the tree uses: a helper such as `0 < c ^ 2` that proofs cite is a computed fact and stays;
  bundle     the statement is a conjunction and the proof only pairs declarations of the tree applied to the
             statement's own binders (`⟨a x, (b x).symm, c x⟩`): the conjuncts are already theorems.

Evaluating a function that computes over data (a decision procedure on an element's configuration, a fold, a
product) is a computed fact and is not theatre; neither is any other statement over variables or hypotheses.

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
                 r"((?:\s*[({\[][^()]*?[)}\]])*)\s*(?::\s*([^:=]+?))?\s*:=\s*(.+?)(?=^\S|\Z)", re.M | re.S)
BOUNDARY = re.compile(r"^(?:@\[|private\s|protected\s|noncomputable\s|theorem\s|lemma\s|def\s|abbrev\s|structure\s|"
                      r"inductive\s|class\s|instance\b|example\b|namespace\s|end\b|section\b|open\s|variable\b|"
                      r"set_option\s|#|attribute\s|macro\b|syntax\b|notation\b|universe\s)", re.M)
LITERAL = re.compile(r'^\(?\s*(true|false|True|False|"[^"]*"|-?\d[\d_]*(\s*:\s*\w+)?|\.\w+|\w+\.\w+|\[\]|none|\(\))\s*\)?$')
CONNECTIVES = re.compile(r"\s*(&&|\|\||∧|∨|¬|!|=|≠|\(|\))\s*")
STRING_OPS = {"length", "toList", "isEmpty", "size", "data", "utf8ByteSize", "startsWith", "endsWith", "isPrefixOf"}
KEYWORDS = {"true", "false", "True", "False", "none", "some", "if", "then", "else", "Nat", "String", "Bool", "Prop",
            "Int", "decide", "rfl", "by", "fun", "let", "in"}


def literal_defs(text: str) -> dict[str, str]:
    """Definitions of this file whose body is a literal or a boolean combination of this file's literal definitions."""
    raw = {m.group(1).split(".")[-1]: " ".join(m.group(4).split()) for m in DEF.finditer(text)}
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


BINDER = re.compile(r"[({\[⦃]\s*([^:(){}\[\]⦃⦄]+?)\s*:")


def split_statement(decl: str) -> tuple[str, str, str]:
    """(binders, statement, proof) of a declaration's text after its name, split at the top-level `:` and `:=`."""
    depth, colon = 0, None
    for i, ch in enumerate(decl):
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            depth -= 1
        elif depth == 0 and decl.startswith(":=", i):
            if colon is None:
                return "", decl[:i], decl[i + 2:]
            return decl[:colon], decl[colon + 1:i], decl[i + 2:]
        elif depth == 0 and ch == ":" and colon is None:
            colon = i
    return decl, "", ""


def split_top(s: str) -> list[str]:
    """Split at commas outside brackets."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    return out + [cur]


def declarations(text: str):
    """(match, binders, statement, proof) for each theorem or lemma of one file, whitespace-normalised."""
    for m in DECL.finditer(text):
        nxt = BOUNDARY.search(text, m.end())
        binders, stmt, proof = split_statement(text[m.end():nxt.start() if nxt else len(text)])
        yield (m, *(" ".join(x.split()) for x in (binders, stmt, proof)))


USES: dict[str, int] = {}


def theatre(text: str, index: dict[str, set[tuple[str, str]]] | None = None) -> list[tuple[str, int, str]]:
    """(name, line, kind: statement) for each theatre declaration of one Lean file; `index` maps each declaration
    name of the tree (last component) to its (binders, statement) forms."""
    lit = literal_defs(text)
    index = index if index is not None else {}
    tables = set()  # definitions by cases whose every result is a literal
    for m in DEF.finditer(text):
        rhs = re.findall(r"=>\s*(.+?)(?=\s*\||\s*$)", " ".join(m.group(4).split()))
        if rhs and all(LITERAL.match(r.strip()) for r in rhs):
            tables.add(m.group(1).split(".")[-1])
    defs = {}  # name -> (explicit parameter names, body)
    for m in DEF.finditer(text):
        params = [v for grp in re.findall(r"\(\s*([^:()]+?)\s*:", m.group(2) or "") for v in grp.split()]
        defs[m.group(1).split(".")[-1]] = (params, " ".join(m.group(4).split()))
    out, seen = [], {}
    for m, binders_n, stmt_n, proof_n in declarations(text):
        line = text.count("\n", 0, m.start()) + 1
        kind = None
        if not binders_n and not re.search(r"[∀∃→↔<>≤≥^*/+]|\bfun\b| - ", stmt_n):
            idents = [n.split(".")[-1] for n in re.findall(r"[A-Za-z_][\w.']*", stmt_n) if n not in KEYWORDS]
            if idents and all(n in lit for n in idents):
                kind = "literal"
        if kind is None and not binders_n and USES.get(m.group(2).split(".")[-1], 0) <= 1:
            idents = [n.split(".")[-1] for n in re.findall(r"[A-Za-z_][\w.']*", stmt_n) if n not in KEYWORDS]
            if idents and all(n in lit for n in idents) and re.search(r"[<>≤≥]", stmt_n):
                kind = "unused-literal"
        if kind is None and not binders_n and '"' in stmt_n:
            bare = re.sub(r'"(?:[^"\\]|\\.)*"', "", stmt_n)
            rest = {n for n in re.findall(r"[A-Za-z_][\w']*", bare)} - KEYWORDS - STRING_OPS
            if not rest:
                kind = "literal"  # a property of string literals alone (a length, an emptiness)
        sides = re.fullmatch(r"\(?(.+?)\)?\s*(=|↔)\s*\(?(.+?)\)?", stmt_n)
        if kind is None and sides and sides.group(1).strip() == sides.group(3).strip():
            kind = "reflexive"
        if kind is None and proof_n:
            bound = [v for grp in BINDER.findall(binders_n) for v in grp.split()]
            parts = re.sub(r"^by\s+exact\s+", "", proof_n).split()
            if parts and parts[0] != m.group(2) and parts[1:] == bound and re.fullmatch(r"[A-Za-z_][\w.']*", parts[0]) \
                    and (binders_n, stmt_n) in index.get(parts[0].split(".")[-1], set()):
                kind = "alias"
        if kind is None and "∧" in stmt_n and re.fullmatch(r"⟨.*⟩", proof_n):
            bound = set(v for grp in BINDER.findall(binders_n) for v in grp.split())
            comps = [c.strip() for c in split_top(proof_n[1:-1])]
            def plain(c: str) -> bool:
                c = re.sub(r"(\.symm|\.le|\.1|\.2|\.mp|\.mpr)+$", "", c.strip())
                c = c[1:-1].strip() if c.startswith("(") and c.endswith(")") else c
                c = re.sub(r"(\.symm|\.le|\.1|\.2|\.mp|\.mpr)+$", "", c)
                toks = c.split()
                return bool(toks) and toks[0].split(".")[-1] in index and all(t in bound for t in toks[1:])
            if comps and all(plain(c) for c in comps):
                kind = "bundle"
        if kind is None and re.fullmatch(r"(by\s+)?(rfl|Iff\.rfl|exact\s+rfl)", proof_n):
            eq = re.fullmatch(r"(.+?)\s+(?:=|↔)\s+(.+)", stmt_n)
            if eq:
                head, *args = eq.group(1).strip().strip("()").split()
                d = defs.get(head.split(".")[-1])
                if d and len(d[0]) == len(args):
                    body = d[1]
                    for v, a in zip(d[0], args):
                        body = re.sub(r"(?<![\w.'])" + re.escape(v) + r"(?![\w'])", a, body)
                    if " ".join(body.split()) == " ".join(eq.group(2).split()):
                        kind = "definitional"
        if kind is None and stmt_n == "True":
            kind = "trivial"
        if kind is None and re.fullmatch(r"(by\s+)?(rfl|decide|exact\s+rfl)", proof_n):
            row = re.fullmatch(r"\(?([\w.']+)\s+(\.[\w']+|[A-Z][\w']*\.[\w']+)\)?\s*=\s*(.+)", stmt_n)
            if row and LITERAL.match(row.group(3).strip()) and row.group(1).split(".")[-1] in tables:
                kind = "table"
        key = (binders_n, stmt_n)
        if kind is None and stmt_n and key in seen:
            kind = "duplicate"
        seen.setdefault(key, m.group(2))
        if kind:
            out.append((m.group(2), line, f"{kind}: {stmt_n}"))
    return out


def census() -> dict[str, list[tuple[str, int, str]]]:
    files = subprocess.run(["git", "-C", ROOT, "ls-files", "Lean/*.lean", "Lean/**/*.lean"], capture_output=True,
                           text=True).stdout.split()
    texts = {}
    for f in sorted(set(files)):
        if "/.lake/" in f:
            continue
        with open(os.path.join(ROOT, f), encoding="utf-8", errors="replace") as fh:
            texts[f] = strip_comments(fh.read(), "--", ("/-", "-/"))
    index: dict[str, set[tuple[str, str]]] = {}
    alltext = "\n".join(texts.values())
    USES.clear()
    for word in re.findall(r"[A-Za-z_][\w']*", alltext):
        USES[word] = USES.get(word, 0) + 1
    for text in texts.values():
        for m, binders_n, stmt_n, _ in declarations(text):
            index.setdefault(m.group(2).split(".")[-1], set()).add((binders_n, stmt_n))
    out = {}
    for f, text in texts.items():
        hits = theatre(text, index)
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
