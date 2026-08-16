#!/usr/bin/env python3
"""Multi-repo Lean axiom gate with Tier 0/1/2 and U1_AXIOM_CENSUS.json."""
from __future__ import annotations
import argparse, json, re, sys
from datetime import datetime, timezone
from pathlib import Path

AXIOM_RE = re.compile(r"^axiom\s+(\S+)")

def repo_root() -> Path:
    """This repository's root — scripts/ lives directly under it."""
    return Path(__file__).resolve().parents[1]

def workspace_root() -> Path:
    """The monorepo root when this repo is checked out inside it.

    Walk upward looking for `workspace/ops`. A standalone clone — which is what
    CI checks out — has no such ancestor, so fall back to this repository. The
    gate then scans this repo's own Lean tree and writes its census locally,
    instead of walking above the checkout and failing on an unwritable path.
    """
    here = Path(__file__).resolve()
    for cand in here.parents:
        if (cand / "workspace" / "ops").is_dir():
            return cand
    return repo_root()

def census_dir(ws: Path) -> Path:
    """Where the census is written: monorepo ops directory, else repo-local."""
    ops = ws / "workspace" / "ops"
    return ops if ops.is_dir() else (ws / "artifacts")

def discover_lean_roots(ws: Path) -> list[Path]:
    """Discover Lean roots under umst/ (UMST fibers), not a hardcoded list.
    Skips .lake/packages, fixtures, and non-umst trees (e.g. private docs)."""
    skip = {".lake", "node_modules", "old", "archived", "scratch", "target", ".git", "fixtures"}
    roots = []
    search = ws / "umst"
    if not search.is_dir():
        # Standalone checkout: this repository is itself the fiber to scan.
        own = ws / "Lean"
        return [own] if own.is_dir() else []
    for lean_dir in search.rglob("Lean"):
        if not lean_dir.is_dir():
            continue
        if any(part in skip for part in lean_dir.parts):
            continue
        if "packages" in lean_dir.parts:
            continue
        has = any(
            p.suffix == ".lean" and p.name != "lakefile.lean" and ".lake" not in p.parts
            for p in lean_dir.rglob("*.lean")
        )
        if has:
            roots.append(lean_dir)
    return sorted(set(roots), key=lambda p: str(p))

def lean_files(lean_root: Path) -> list[Path]:
    return [
        p for p in sorted(lean_root.rglob("*.lean"))
        if p.name != "lakefile.lean" and ".lake" not in p.parts
    ]

def find_axioms(lean_root: Path) -> list[dict]:
    rows = []
    for p in lean_files(lean_root):
        for lineno, line in enumerate(p.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            m = AXIOM_RE.match(line)
            if not m:
                continue
            name = m.group(1)
            if name == "physicalSecondLaw":
                tier, justification = 0, "physical root (Landauer / second law)"
            elif "Crypto" in p.parts:
                tier, justification = 1, "cryptographic hardness / opaque interface"
            else:
                tier, justification = 2, "UNEXPECTED — must be theorem or operator-approved Tier-2"
            rows.append({
                "repo_lean_root": str(lean_root),
                "file": str(p.relative_to(lean_root)),
                "line": lineno,
                "name": name,
                "tier": tier,
                "justification": justification,
            })
    return rows

def classify_repo(lean_root: Path, axioms: list[dict]) -> list[str]:
    errs = []
    physics = [a for a in axioms if a["tier"] == 0]
    has_landauer = any(p.name == "LandauerLaw.lean" for p in lean_files(lean_root))
    if has_landauer and len(physics) != 1:
        errs.append(f"{lean_root}: Tier-0 expected exactly 1 physicalSecondLaw, got {len(physics)}")
    if len(physics) > 1:
        errs.append(f"{lean_root}: Tier-0 must be unique, got {len(physics)}")
    for a in axioms:
        if a["tier"] == 2:
            errs.append(f"Tier-2 axiom {a['file']}:{a['line']} {a['name']}")
    return errs

def write_census(ws, all_axioms, roots):
    out = {
        "schema": "u1_axiom_census_v1",
        "observed_at_wall": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "workspace_root": str(ws),
        "lean_roots": [str(r) for r in roots],
        "axiom_count": len(all_axioms),
        "tier_counts": {
            "0": sum(1 for a in all_axioms if a["tier"] == 0),
            "1": sum(1 for a in all_axioms if a["tier"] == 1),
            "2": sum(1 for a in all_axioms if a["tier"] == 2),
        },
        "axioms": all_axioms,
    }
    target = census_dir(ws)
    target.mkdir(parents=True, exist_ok=True)
    path = target / "U1_AXIOM_CENSUS.json"
    path.write_text(json.dumps(out, indent=2) + "\n")
    return path

def run_synthetic_tier2_fail(ws: Path) -> None:
    scratch = census_dir(ws) / ".tmp_u1_tier2_scratch/Lean"
    scratch.mkdir(parents=True, exist_ok=True)
    bad = scratch / "SyntheticTier2.lean"
    bad.write_text("axiom synthetic_tier2_must_fail : True\n")
    try:
        errs = classify_repo(scratch, find_axioms(scratch))
        if not any("Tier-2" in e for e in errs):
            raise SystemExit("synthetic Tier-2 test FAILED to detect planted axiom")
        print("check_lean_axioms: synthetic Tier-2 detection OK")
    finally:
        bad.unlink(missing_ok=True)
        try:
            scratch.rmdir(); scratch.parent.rmdir()
        except OSError:
            pass

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-synthetic", action="store_true")
    args = ap.parse_args()
    ws = workspace_root()
    roots = discover_lean_roots(ws)
    if not roots:
        print("check_lean_axioms: no Lean roots discovered", file=sys.stderr)
        return 2
    all_axioms, errs = [], []
    for lean_root in roots:
        ax = find_axioms(lean_root)
        try:
            label = str(lean_root.relative_to(ws))
        except ValueError:
            label = str(lean_root)
        for a in ax:
            a["repo"] = label
        all_axioms.extend(ax)
        errs.extend(classify_repo(lean_root, ax))
    census_path = write_census(ws, all_axioms, roots)
    print(
        f"check_lean_axioms: census {census_path} axioms={len(all_axioms)} "
        f"tier0={sum(1 for a in all_axioms if a['tier']==0)} "
        f"tier1={sum(1 for a in all_axioms if a['tier']==1)} "
        f"tier2={sum(1 for a in all_axioms if a['tier']==2)} roots={len(roots)}"
    )
    if not args.skip_synthetic:
        run_synthetic_tier2_fail(ws)
    if errs:
        print("check_lean_axioms: FAIL", file=sys.stderr)
        for e in errs:
            print(f"  {e}", file=sys.stderr)
        return 1
    print("check_lean_axioms: OK — Tier-0/1/2 hygiene holds")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
