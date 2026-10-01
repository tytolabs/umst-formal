#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""public_workflow_guard — W-68: path-triggered workflows must run check_tracked_build_artefacts.sh."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

WORKFLOWS = (
    ".github/workflows/ci.yml",
    ".github/workflows/formal.yml",
    ".github/workflows/lean.yml",
    ".github/workflows/extract-haskell-from-lean.yml",
)
GUARD = "check_tracked_build_artefacts.sh"
EXTRACT = ".github/workflows/extract-haskell-from-lean.yml"


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def check_workflows(root: Path) -> list[str]:
    errors: list[str] = []
    for wf in WORKFLOWS:
        body = (root / wf).read_text(encoding="utf-8")
        if GUARD not in body:
            errors.append(f"{wf} missing {GUARD}")
    extract = (root / EXTRACT).read_text(encoding="utf-8")
    if "timeout-minutes:" not in extract:
        errors.append(f"{EXTRACT} missing timeout-minutes")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="exit 1 when workflow guard wiring drifts")
    _ = parser.parse_args()
    errors = check_workflows(repo_root())
    if errors:
        for e in errors:
            print(e, file=sys.stderr)
        return 1
    print("public_workflow_guard: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
