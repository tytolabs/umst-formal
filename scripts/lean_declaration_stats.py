#!/usr/bin/env python3
"""
Lean declaration statistics for this repository.

Parses `Lean/lakefile.lean` `lean_lib` roots (only), counts line-start
`theorem` / `lemma` in each root module and in all `Lean/*.lean`, and lists
`^axiom ` declarations.

Usage (from repository root):
  python3 scripts/lean_declaration_stats.py
  python3 scripts/lean_declaration_stats.py --json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def parse_lake_roots(lakefile_text: str) -> list[str]:
    """Extract root module names from the first `lean_lib` … `roots := #[…]` block.

    Lake allows `` `Name, `` between roots and the last entry may be `` `Name] `` without
    a closing backtick before `]`; we match each `` `Identifier`` with a regex.
    """
    i = lakefile_text.find("lean_lib")
    if i < 0:
        raise ValueError("lean_lib not found in lakefile.lean")
    sub = lakefile_text[i:]
    key = "roots := #["
    j = sub.find(key)
    if j < 0:
        raise ValueError("roots := #[ not found after lean_lib")
    start = j + len(key) - 1  # '[' of #[
    depth = 0
    k = start
    while k < len(sub):
        c = sub[k]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                body = sub[start + 1 : k]
                names = re.findall(r"`([A-Za-z][A-Za-z0-9_.]*)", body)
                return names
        k += 1
    raise ValueError("unclosed roots array")


def count_declarations(lean_path: Path) -> tuple[int, int]:
    t = l = 0
    text = lean_path.read_text(encoding="utf-8", errors="replace")
    for line in text.splitlines():
        if line.startswith("theorem "):
            t += 1
        elif line.startswith("lemma "):
            l += 1
    return t, l


def find_axioms(lean_dir: Path) -> list[tuple[str, int, str]]:
    out: list[tuple[str, int, str]] = []
    for p in sorted(lean_dir.rglob("*.lean")):
        if p.name == "lakefile.lean" or ".lake" in p.parts:
            continue
        for lineno, line in enumerate(p.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            if line.startswith("axiom "):
                m = re.match(r"axiom\s+(\S+)", line)
                name = m.group(1) if m else line
                out.append((p.name, lineno, name))
    return out


def collect_stats(root: Path) -> dict:
    lean = root / "Lean"
    lakefile = lean / "lakefile.lean"
    if not lakefile.is_file():
        raise FileNotFoundError(f"missing {lakefile}")

    roots = parse_lake_roots(lakefile.read_text(encoding="utf-8"))
    per_root: dict[str, dict[str, int]] = {}
    rt = rl = 0
    missing: list[str] = []
    for name in roots:
        rel = Path(*name.split(".")).with_suffix(".lean")
        f = lean / rel
        if not f.is_file():
            missing.append(name)
            continue
        t, l = count_declarations(f)
        per_root[name] = {"theorem": t, "lemma": l}
        rt += t
        rl += l

    all_t = all_l = 0
    for p in lean.rglob("*.lean"):
        if p.name == "lakefile.lean" or ".lake" in p.parts:
            continue
        t, l = count_declarations(p)
        all_t += t
        all_l += l

    axioms = find_axioms(lean)
    return {
        "repo": root.name,
        "lake_roots_count": len(roots),
        "lake_roots": roots,
        "roots_only": {"theorem": rt, "lemma": rl, "total": rt + rl},
        "all_lean_glob": {"theorem": all_t, "lemma": all_l, "total": all_t + all_l},
        "per_root": per_root,
        "missing_root_files": missing,
        "axioms": [{"file": a[0], "line": a[1], "name": a[2]} for a in axioms],
    }


def verify_snapshot(expected_path: Path, got: dict) -> list[str]:
    expected = json.loads(expected_path.read_text(encoding="utf-8"))
    errors: list[str] = []
    for key in ("lake_roots_count", "lake_roots", "roots_only", "all_lean_glob", "per_root"):
        if expected.get(key) != got.get(key):
            errors.append(f"drift in {key}")
    if got.get("missing_root_files"):
        errors.append(f"missing root files: {got['missing_root_files']}")
    return errors


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true", help="print JSON only")
    ap.add_argument(
        "--verify-snapshot",
        metavar="PATH",
        help="exit 1 if committed JSON snapshot does not match current Lean tree",
    )
    args = ap.parse_args()

    root = repo_root()
    try:
        data = collect_stats(root)
    except FileNotFoundError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    if args.verify_snapshot:
        snap = Path(args.verify_snapshot)
        if not snap.is_file():
            print(f"error: missing snapshot {snap}", file=sys.stderr)
            return 1
        errors = verify_snapshot(snap, data)
        if errors:
            for err in errors:
                print(f"FAIL: {err}", file=sys.stderr)
            return 1
        print(f"OK: snapshot matches ({data['all_lean_glob']['total']} all-Lean declarations)")
        return 0

    missing = data["missing_root_files"]
    roots = data["lake_roots"]
    per_root = data["per_root"]
    rt = data["roots_only"]["theorem"]
    rl = data["roots_only"]["lemma"]
    all_t = data["all_lean_glob"]["theorem"]
    all_l = data["all_lean_glob"]["lemma"]
    axioms = [(a["file"], a["line"], a["name"]) for a in data["axioms"]]

    if args.json:
        print(json.dumps(data, indent=2))
        return 1 if missing else 0

    print(f"Repository: {root.name}")
    print(f"Lake roots: {len(roots)} modules")
    if missing:
        print(f"WARNING missing .lean files for roots: {missing}")
    print(f"Roots-only:  {rt} theorem, {rl} lemma, total {rt + rl}")
    print(f"All Lean/*:  {all_t} theorem, {all_l} lemma, total {all_t + all_l}")
    print("Axioms (^axiom ):")
    for a in axioms:
        print(f"  {a[0]}:{a[1]}  {a[2]}")
    print("\nPer-root (theorem / lemma):")
    for name in roots:
        if name in per_root:
            pr = per_root[name]
            print(f"  {name}: {pr['theorem']} / {pr['lemma']}")
        else:
            print(f"  {name}: MISSING FILE")
    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
