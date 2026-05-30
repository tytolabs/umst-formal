#!/usr/bin/env python3
"""CI axiom policy: one physics axiom + tier-tagged crypto/behavior axioms (no sorry)."""
from __future__ import annotations

import sys
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from lean_declaration_stats import find_axioms, repo_root  # noqa: E402

# Meso fence: explicit axioms only in these Lean files (§14bis.h-ZERO-SORRY-1 / S-0).
_ALLOWED_AXIOM_FILES = frozenset(
    {
        "SDFCanonical.lean",
        "Collision.lean",
        "Composability.lean",
        "EUF_CMA.lean",
        "LWE.lean",
        "SanitizePatternCoverage.lean",
        "SideChannel.lean",
        "LandauerLaw.lean",
    }
)


def main() -> int:
    lean = repo_root() / "Lean"
    axioms = find_axioms(lean)
    by_file: dict[str, list[str]] = {}
    for file, _line, name in axioms:
        by_file.setdefault(file, []).append(name)

    unexpected_files = set(by_file) - _ALLOWED_AXIOM_FILES
    if unexpected_files:
        print(
            "check_lean_axioms: axiom in unexpected file(s):",
            ", ".join(sorted(unexpected_files)),
            file=sys.stderr,
        )
        return 1

    landauer = by_file.get("LandauerLaw.lean", [])
    if landauer != ["physicalSecondLaw"]:
        print(
            f"check_lean_axioms: LandauerLaw.lean must declare only physicalSecondLaw, got {landauer!r}",
            file=sys.stderr,
        )
        return 1

    n_tier = sum(len(v) for f, v in by_file.items() if f != "LandauerLaw.lean")
    print(
        f"check_lean_axioms: OK (physicalSecondLaw + {n_tier} tier-tagged axioms in allowed files)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
