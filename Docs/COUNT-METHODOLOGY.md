# Lean declaration counts — methodology

**Authoritative summary:** [FORMAL_FOUNDATIONS.md](../FORMAL_FOUNDATIONS.md) (Wave 6.5.1+).

## Rules

- **Lake roots:** Module names come from the first `lean_lib` … `roots := #[…]` block in [`Lean/lakefile.lean`](../Lean/lakefile.lean), parsed by [`scripts/lean_declaration_stats.py`](../scripts/lean_declaration_stats.py) (handles Lake’s `` `Name, `` separators and a final `` `Name] `` without a closing backtick before `]`).
- **`theorem` / `lemma`:** Count lines starting with exactly `theorem ` or `lemma ` in each `Lean/<Root>.lean` file (roots-only total = sum over roots). **All-Lean** total = every `Lean/*.lean` except `lakefile.lean`.
- **Not counted:** `example`, `def`, `instance` proofs, nested declarations inside sections (only line-start top-level).
- **Project `axiom`:** Lines starting with `axiom ` in `Lean/*.lean` (should be only `physicalSecondLaw` in `LandauerLaw.lean`).

## Regenerate

From the repository root:

```bash
python3 scripts/lean_declaration_stats.py
python3 scripts/lean_declaration_stats.py --json
```

Then align [FORMAL_FOUNDATIONS.md](../FORMAL_FOUNDATIONS.md), [PROOF-STATUS.md](../PROOF-STATUS.md), and [README.md](../README.md) with the script output.
