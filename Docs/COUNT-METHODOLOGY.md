# Lean declaration counts — methodology

**Authoritative summary:** [FORMAL_FOUNDATIONS.md](../FORMAL_FOUNDATIONS.md) (Wave 6.5.2).

## Rules

- **Lake roots:** Module names come from the first `lean_lib` … `roots := #[…]` block in [`Lean/lakefile.lean`](../Lean/lakefile.lean), parsed by [`scripts/lean_declaration_stats.py`](../scripts/lean_declaration_stats.py) (handles Lake’s `` `Name, `` separators and a final `` `Name] `` without a closing backtick before `]`).
- **`theorem` / `lemma`:** Count lines starting with exactly `theorem ` or `lemma ` in each `Lean/<Root>.lean` file (roots-only total = sum over roots). **All-Lean** total = every `Lean/**/*.lean` **except** `lakefile.lean` and any path under **`.lake/`** (generated Lake/Mathlib tree). [`scripts/lean_declaration_stats.py`](../scripts/lean_declaration_stats.py) implements this via `rglob` with `".lake" in p.parts` skipped.
- **Not counted:** `example`, `def`, `instance` proofs, nested declarations inside sections (only line-start top-level).
- **Project `axiom`:** Lines starting with `axiom ` in `Lean/*.lean` (should be only `physicalSecondLaw` in `LandauerLaw.lean`).

## Regenerate

From the repository root:

```bash
python3 scripts/lean_declaration_stats.py
python3 scripts/lean_declaration_stats.py --json
```

Then align [FORMAL_FOUNDATIONS.md](../FORMAL_FOUNDATIONS.md), [PROOF-STATUS.md](../PROOF-STATUS.md), and [README.md](../README.md) with the script output.

## CI drift gate

After intentional root or count changes, update [`scripts/expected_lean_declaration_snapshot.json`](../scripts/expected_lean_declaration_snapshot.json) to match:

```bash
python3 scripts/lean_declaration_stats.py --verify-snapshot scripts/expected_lean_declaration_snapshot.json
# if mismatch: edit the JSON (totals + axiom row) in the same commit as the Lean change
```

## Theorem / lemma names (audit export)

Machine-readable list per lake root (`theorem:` / `lemma:` prefixes):

```bash
python3 scripts/lean_declaration_stats.py --theorem-names
```

## Axiom invariant

```bash
python3 scripts/check_lean_axioms.py
```

Expect exactly one `axiom`: `LandauerLaw.physicalSecondLaw`.

## Markdown link check (CI)

Curated prose files: `bash scripts/check-markdown-links.sh` (uses `markdown-link-check` via `npx`; config `scripts/markdown-link-check.json`). Same command runs in the **Docs lint + Markdown links** GitHub Actions job.
