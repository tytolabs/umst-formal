#!/usr/bin/env python3
"""
Lean declaration statistics for this repository.

Parses `Lean/lakefile.lean` `lean_lib` roots (only), counts line-start
`theorem` / `lemma` in each root module and in all `Lean/*.lean`, and lists
`^axiom ` declarations.

Usage (from repository root):
  python3 scripts/lean_declaration_stats.py
  python3 scripts/lean_declaration_stats.py --json
  python3 scripts/lean_declaration_stats.py --verify-snapshot scripts/expected_lean_declaration_snapshot.json
  python3 scripts/lean_declaration_stats.py --theorem-names
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

_THEOREM_LEMMA = re.compile(r"^(theorem|lemma)\s+([^\s(:]+)")


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


def declaration_names_in_file(lean_path: Path) -> list[tuple[str, str]]:
    """Return (kind, name) for each line-start `theorem` / `lemma` in file."""
    out: list[tuple[str, str]] = []
    text = lean_path.read_text(encoding="utf-8", errors="replace")
    for line in text.splitlines():
        m = _THEOREM_LEMMA.match(line)
        if m:
            out.append((m.group(1), m.group(2)))
    return out


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


def gather_declaration_data() -> tuple[dict, list[str]]:
    root = repo_root()
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

    data: dict = {
        "repo": root.name,
        "lake_roots_count": len(roots),
        "lake_roots": roots,
        "roots_only": {"theorem": rt, "lemma": rl, "total": rt + rl},
        "all_lean_glob": {"theorem": all_t, "lemma": all_l, "total": all_t + all_l},
        "per_root": per_root,
        "missing_root_files": missing,
        "axioms": [{"file": a[0], "line": a[1], "name": a[2]} for a in axioms],
    }
    return data, missing


def verify_snapshot(data: dict, snapshot_path: Path) -> list[str]:
    raw = json.loads(snapshot_path.read_text(encoding="utf-8"))
    exp = {k: v for k, v in raw.items() if not k.startswith("_")}
    errors: list[str] = []
    if data["lake_roots_count"] != exp["lake_roots_count"]:
        errors.append(
            f"lake_roots_count: got {data['lake_roots_count']}, expected {exp['lake_roots_count']}"
        )
    for key in ("roots_only", "all_lean_glob"):
        got, want = data[key], exp[key]
        for sub in ("theorem", "lemma", "total"):
            if got[sub] != want[sub]:
                errors.append(f"{key}.{sub}: got {got[sub]}, expected {want[sub]}")
    ax_got = {(a["file"], a["name"]) for a in data["axioms"]}
    ax_want = {(a["file"], a["name"]) for a in exp["axioms"]}
    if ax_got != ax_want:
        errors.append(f"axioms: got {sorted(ax_got)!r}, expected {sorted(ax_want)!r}")
    return errors


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true", help="print JSON only")
    ap.add_argument(
        "--verify-snapshot",
        type=Path,
        metavar="PATH",
        help="exit 1 if counts differ from committed snapshot (CI drift gate)",
    )
    ap.add_argument(
        "--theorem-names",
        action="store_true",
        help="print JSON map of lake root module name -> ordered list of theorem/lemma identifiers",
    )
    args = ap.parse_args()

    try:
        data, missing = gather_declaration_data()
    except FileNotFoundError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    root = repo_root()
    lean = root / "Lean"

    if args.verify_snapshot:
        errs = verify_snapshot(data, args.verify_snapshot)
        if errs:
            print("verify-snapshot: mismatch with", args.verify_snapshot, file=sys.stderr)
            for e in errs:
                print(f"  {e}", file=sys.stderr)
            return 1
        print("verify-snapshot: OK")
        return 1 if missing else 0

    if args.theorem_names:
        roots = data["lake_roots"]
        names_out: dict[str, list[str]] = {}
        for name in roots:
            rel = Path(*name.split(".")).with_suffix(".lean")
            f = lean / rel
            if not f.is_file():
                continue
            entries = declaration_names_in_file(f)
            names_out[name] = [f"{kind}:{n}" for kind, n in entries]
        print(json.dumps(names_out, indent=2))
        return 1 if missing else 0

    if args.json:
        print(json.dumps(data, indent=2))
        return 1 if missing else 0

    print(f"Repository: {data['repo']}")
    print(f"Lake roots: {data['lake_roots_count']} modules")
    if missing:
        print(f"WARNING missing .lean files for roots: {missing}")
    ro = data["roots_only"]
    print(f"Roots-only:  {ro['theorem']} theorem, {ro['lemma']} lemma, total {ro['total']}")
    ag = data["all_lean_glob"]
    print(f"All Lean/*:  {ag['theorem']} theorem, {ag['lemma']} lemma, total {ag['total']}")
    print("Axioms (^axiom ):")
    for a in data["axioms"]:
        print(f"  {a['file']}:{a['line']}  {a['name']}")
    print("\nPer-root (theorem / lemma):")
    for name in data["lake_roots"]:
        if name in data["per_root"]:
            pr = data["per_root"][name]
            print(f"  {name}: {pr['theorem']} / {pr['lemma']}")
        else:
            print(f"  {name}: MISSING FILE")
    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
