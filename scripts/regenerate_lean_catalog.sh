#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Regenerate artifacts/catalog.json (+ lock) from Lean/ tree.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
EXPORT="${UMST_LEAN_EXPORT_SCRIPT:-$ROOT/../umst-formal-double-slit/tools/lean_export/export_catalog.py}"

if [[ ! -f "$EXPORT" ]]; then
  echo "FAIL: export_catalog.py not found at $EXPORT" >&2
  exit 1
fi

python3 "$EXPORT" --lean-root "$ROOT/Lean" --out "$ROOT/artifacts/catalog.json"

python3 - "$ROOT/artifacts/catalog.json" << 'PY'
"""Merge Lean `abbrev` names into catalog declaration indexes (export_catalog skips abbrevs)."""
import json, re, sys
from pathlib import Path

catalog_path = Path(sys.argv[1])
lean = catalog_path.parent.parent / "Lean"
catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
abbrev_re = re.compile(r"^\s*abbrev\s+([^\s:]+)")

for mod in catalog.get("modules", []):
    rel = mod.get("path", "")
    src = lean / rel
    if not src.is_file():
        continue
    names = []
    for line in src.read_text(encoding="utf-8").splitlines():
        m = abbrev_re.match(line)
        if m:
            names.append(m.group(1))
    if names:
        decls = mod.setdefault("declarations", {})
        bucket = decls.setdefault("abbrev", [])
        for n in names:
            if n not in bucket:
                bucket.append(n)

canon = json.dumps(
    {k: v for k, v in catalog.items() if k != "digest"},
    sort_keys=True,
    separators=(",", ":"),
    ensure_ascii=True,
)
import hashlib

catalog["digest"] = hashlib.sha256(canon.encode("utf-8")).hexdigest()
catalog_path.write_text(json.dumps(catalog, indent=2) + "\n", encoding="utf-8")
lock = catalog_path.parent / "catalog.lock.json"
lock.write_text(
    json.dumps(
        {
            "version": 1,
            "role": "lean_catalog_lock",
            "catalog_path": "artifacts/catalog.json",
            "catalog_digest_hex": catalog["digest"],
            "module_count": len(catalog.get("modules", [])),
            "notes": "Regenerated via scripts/regenerate_lean_catalog.sh",
        },
        indent=2,
    )
    + "\n",
    encoding="utf-8",
)
print(f"patched abbrevs; digest={catalog['digest']} modules={len(catalog['modules'])}")
PY
