#!/usr/bin/env python3
"""Fail unless physics axiom is unique and crypto axioms stay in Lean/Crypto/."""
from __future__ import annotations

import sys
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from lean_declaration_stats import find_axioms, repo_root  # noqa: E402


def _axiom_paths(lean: Path) -> list[tuple[Path, int, str]]:
    out: list[tuple[Path, int, str]] = []
    for p in sorted(lean.rglob("*.lean")):
        if p.name == "lakefile.lean" or ".lake" in p.parts:
            continue
        for lineno, line in enumerate(
            p.read_text(encoding="utf-8", errors="replace").splitlines(), 1
        ):
            if line.startswith("axiom "):
                import re

                m = re.match(r"axiom\s+(\S+)", line)
                name = m.group(1) if m else line.strip()
                out.append((p, lineno, name))
    return out


def main() -> int:
    lean = repo_root() / "Lean"
    axioms = _axiom_paths(lean)
    physics = [
        a for a in axioms if a[0].name == "LandauerLaw.lean" and a[2] == "physicalSecondLaw"
    ]
    crypto = [a for a in axioms if "Crypto" in a[0].parts]
    other = [a for a in axioms if a not in physics and a not in crypto]

    if len(physics) != 1:
        print(
            f"check_lean_axioms: expected exactly 1 physics axiom "
            f"(LandauerLaw.physicalSecondLaw), got {len(physics)}",
            file=sys.stderr,
        )
        for a in physics:
            print(f"  {a[0].relative_to(lean)}:{a[1]}  {a[2]}", file=sys.stderr)
        return 1

    if other:
        print(
            "check_lean_axioms: unexpected axiom(s) outside Lean/Crypto/ and LandauerLaw.lean:",
            file=sys.stderr,
        )
        for a in other:
            print(f"  {a[0].relative_to(lean)}:{a[1]}  {a[2]}", file=sys.stderr)
        return 1

    print(
        f"check_lean_axioms: OK — 1 physics axiom + {len(crypto)} tier-tagged crypto axiom(s) in Crypto/"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
