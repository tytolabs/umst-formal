#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""Every tracked Lean file is machine-checked by CI, or listed as unchecked with a reason.

CI builds the lakefile's default targets (`lake build`). This check computes, from Lean/lakefile.lean, the modules
those targets compile (roots and globs of every @[default_target] lean_lib, closed under project imports) and
compares them with the tracked .lean files:

- a tracked file outside the closure and not in Lean/lean-unchecked.txt fails (it would pass CI unchecked);
- a lean_lib without @[default_target] fails (plain `lake build` would skip it);
- an entry of lean-unchecked.txt that the build does compile, or that does not exist, fails (the list only shrinks).

Cause: until 2026-10-01 no lean_lib here was a default target, so CI's `lake build` compiled nothing and stayed
green while ten modules did not compile. Usage: python3 scripts/check_lean_ci_closure.py (from the repository root).
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, "Lean")
ALLOW = os.path.join(LEAN, "lean-unchecked.txt")


def libraries(lakefile_text):
    code = re.sub(r"/-.*?-/", "", lakefile_text, flags=re.S)
    code = re.sub(r"--[^\n]*", "", code)
    libs = {}
    heads = list(re.finditer(r"(@\[default_target\]\s*)?lean_lib\s+(«[^»]+»|[A-Za-z0-9_.]+)\s+where", code))
    for i, m in enumerate(heads):
        end = heads[i + 1].start() if i + 1 < len(heads) else len(code)
        m = re.match(r"(@\[default_target\]\s*)?lean_lib\s+(«[^»]+»|[A-Za-z0-9_.]+)\s+where(.*)",
                     code[m.start():end], re.S)
        name = m.group(2).strip("«»")
        body = re.split(r"\n(?=lean_exe|require|package|@\[)", m.group(3))[0]
        rm = re.search(r"roots\s*:=\s*#\[(.*?)\]", body, re.S)
        roots = [r.strip("«»") for r in re.findall(r"`(«[^»]+»|[A-Za-z0-9_.]+)", rm.group(1))] if rm else [name]
        globs = []
        gm = re.search(r"globs\s*:=\s*#\[(.*?)\]", body, re.S)
        if gm:
            for g in re.finditer(r"(\.submodules|\.andSubmodules|\.one)?\s*`([A-Za-z0-9_.]+?)(\.\+|\.\*)?(?=[\s,\]]|$)",
                                 gm.group(1)):
                kind, base, suffix = g.group(1) or "", g.group(2), g.group(3) or ""
                if kind == ".submodules" or suffix == ".*":
                    globs.append((base, "strict"))
                elif kind == ".andSubmodules" or suffix == ".+":
                    globs.append((base, "and"))
                else:
                    globs.append((base, "one"))
        libs[name] = {"default": bool(m.group(1)), "roots": roots, "globs": globs}
    return libs


def main():
    tracked = subprocess.run(["git", "-C", ROOT, "ls-files", "Lean"], capture_output=True, text=True).stdout.split()
    files = [p for p in tracked if p.endswith(".lean") and not p.endswith("lakefile.lean") and "/.lake/" not in p]
    mods = {p[len("Lean/"):-len(".lean")].replace("/", "."): p for p in files}
    libs = libraries(open(os.path.join(LEAN, "lakefile.lean")).read())
    problems = [f"lean_lib {n} is not @[default_target]; `lake build` skips it" for n, l in libs.items() if not l["default"]]
    start = set()
    for lib in libs.values():
        start |= set(lib["roots"])
        for base, kind in lib["globs"]:
            start |= {m for m in mods if m.startswith(base + ".") or (kind in ("and", "one") and m == base)}
    seen, stack = set(), [m for m in start if m in mods]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        for line in re.findall(r"^import\s+(.+)$", open(os.path.join(ROOT, mods[m])).read(), re.M):
            stack += [d for d in line.split() if d in mods and d not in seen]
    allowed = {}
    if os.path.exists(ALLOW):
        for line in open(ALLOW):
            line = line.split("#", 1)
            path = line[0].strip()
            if path:
                allowed[path] = line[1].strip() if len(line) > 1 else ""
    built = {mods[m] for m in seen}
    for p in sorted(set(files) - built):
        if p not in allowed:
            problems.append(f"{p} is tracked but no CI target compiles it (add it to a lean_lib, or list it with a reason)")
    for p, why in sorted(allowed.items()):
        if p not in files:
            problems.append(f"lean-unchecked.txt lists {p}, which is not tracked")
        elif p in built:
            problems.append(f"lean-unchecked.txt lists {p}, which CI compiles: remove the entry")
        elif not why:
            problems.append(f"lean-unchecked.txt lists {p} without a reason")
    print(f"check_lean_ci_closure: {len(built)} of {len(files)} tracked Lean files compiled by CI; "
          f"{len(set(files) - built)} listed unchecked")
    for p in problems:
        print("FAIL:", p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
