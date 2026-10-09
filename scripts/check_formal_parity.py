#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""The four-language parity of the contract: every statement of formal_parity.json is stated in each language.

formal_parity.json lists statements by one id. For each of Lean, Coq, Agda and Haskell an entry names the
declaration (theorem, definition, type, or Haskell QuickCheck property) and its file, or gives the reason the
language cannot state it ("absent"). A Haskell name in double quotes names an entry of a checked list
(`("label", value)`, such as a generated module's `checks`) that the test suite runs. This check fails when

- a named declaration is not declared in its file;
- a theorem or definition of a contract module (`contract_modules`) is in no statement, so a Lean-only result
  cannot enter the contract unnoticed;
- the number of absent entries exceeds `max_absent` (a ratchet that only falls).

The Rust runtime reads the same file: it may rely only on statements whose Lean, Coq and Agda entries are present.
Usage: python3 scripts/check_formal_parity.py [--summary]
"""
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DECL = {
    "lean": r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+(?:[\w.]*\.)?{n}(?![\w'])",
    "coq": r"(?m)^\s*(?:Theorem|Lemma|Corollary|Definition|Fixpoint|Record|Inductive|Class)\s+{n}(?![\w'])",
    # declarations inside a parameterised module are indented; a record or data type may take parameters
    "agda": r"(?m)^[ \t]*(?:(?:record|data)\s+{n}(?:\s+[({][^)}]*[)}])*|{n})\s+:",
    "haskell": r"(?m)^(?:{n}\s+::|(?:data|newtype|type)\s+{n}\b)",
}


def declared(lang: str, name: str, path: str) -> bool:
    full = os.path.join(ROOT, path)
    if not os.path.exists(full):
        return False
    text = open(full, encoding="utf-8").read()
    if lang == "haskell" and name.startswith('"') and name.endswith('"'):
        return re.search(r'\(\s*"' + re.escape(name[1:-1]) + r'"\s*,', text) is not None
    short = name.split(".")[-1]
    return re.search(DECL[lang].replace("{n}", re.escape(short)), text) is not None


def main() -> int:
    doc = json.load(open(os.path.join(ROOT, "formal_parity.json"), encoding="utf-8"))
    errors, absent, named = [], 0, {}
    for st in doc["statements"]:
        for lang in ("lean", "coq", "agda", "haskell"):
            e = st.get(lang)
            if e is None:
                errors.append(f"{st['id']}: no {lang} entry (name it, or give the reason it is absent)")
            elif "absent" in e:
                absent += 1
            elif not declared(lang, e["name"], e["file"]):
                errors.append(f"{st['id']}: {lang} {e['name']} is not declared in {e['file']}")
            else:
                named.setdefault((lang, e["file"]), set()).add(e["name"].split(".")[-1])
    for mod in doc["contract_modules"]:
        text = open(os.path.join(ROOT, mod), encoding="utf-8").read()
        for m in re.finditer(DECL["lean"].replace("(?:[\\w.]*\\.)?{n}(?![\\w'])", "(?:[\\w.]*\\.)?([\\w']+)"), text):
            if m.group(1) not in named.get(("lean", mod), set()):
                errors.append(f"{mod}: {m.group(1)} is in no statement of formal_parity.json")
    if absent > doc["max_absent"]:
        errors.append(f"{absent} absent entries exceed max_absent {doc['max_absent']}")
    if "--summary" in sys.argv or not errors:
        total = 4 * len(doc["statements"])
        print(f"formal parity: {len(doc['statements'])} statements, {total - absent} of {total} language entries "
              f"present, {absent} absent (bound {doc['max_absent']})")
    for e in errors:
        print("FAIL: " + e, file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
