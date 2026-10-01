#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
#
# check_tracked_build_artefacts — W-68: refuse tracked Coq/Lean/Agda build products that .gitignore excludes.
# A committed artefact (for example Coq/Core/Gate.vo) is loaded instead of rebuilt and breaks CI
# when it was compiled with another toolchain.
set -euo pipefail
bad=$(git ls-files -ci --exclude-standard)
if [ -n "$bad" ]; then
  echo "FAIL: files matched by .gitignore are tracked:"
  echo "$bad" | head -50
  exit 1
fi
echo "OK: no tracked build artefacts"
