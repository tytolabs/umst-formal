#!/usr/bin/env python3
"""Fail unless exactly one project `axiom` exists: LandauerLaw.physicalSecondLaw."""
from __future__ import annotations

import sys
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from lean_declaration_stats import find_axioms, repo_root  # noqa: E402


def main() -> int:
    lean = repo_root() / "Lean"
    axioms = find_axioms(lean)
    if len(axioms) != 1:
        print(
            f"check_lean_axioms: expected exactly 1 `axiom` in Lean/ (excl. .lake), got {len(axioms)}:",
            file=sys.stderr,
        )
        for a in axioms:
            print(f"  {a[0]}:{a[1]}  {a[2]}", file=sys.stderr)
        return 1
    file, _line, name = axioms[0]
    if file != "LandauerLaw.lean" or name != "physicalSecondLaw":
        print(
            f"check_lean_axioms: unexpected axiom {file!r} {name!r} (want LandauerLaw.lean / physicalSecondLaw)",
            file=sys.stderr,
        )
        return 1
    print("check_lean_axioms: OK (single physicalSecondLaw in LandauerLaw.lean)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
