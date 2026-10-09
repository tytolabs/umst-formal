#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""Tests of scripts/gen_constants.py: the bounds table is refused when malformed, endpoints round into their interval,
and the bounds modules are generated from the table. Run: python3 scripts/test_gen_constants.py"""
from __future__ import annotations

import math
import os
import sys
import tempfile
import unittest
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_constants as g  # noqa: E402

L4 = ["lean", "coq", "agda", "haskell"]
PARITY = {
    "T.pos": {"id": "t.pos", "statement": "s", "lean": {"name": "T.pos", "file": "Lean/T.lean"},
              "coq": {"name": "pos", "file": "Coq/T.v"}, "agda": {"name": "pos", "file": "Agda/T.agda"},
              "haskell": {"name": "prop_pos", "file": "Haskell/test/TProps.hs"}},
    "T.leanOnly": {"id": "t.lean_only", "statement": "s", "lean": {"name": "T.leanOnly", "file": "Lean/T.lean"},
                   "coq": {"absent": "r"}, "agda": {"absent": "r"}, "haskell": {"absent": "r"}},
}


def table(*bounds: dict) -> dict:
    return {"constants": [{"id": "c", "unit": "m s⁻¹", "status": "cited", "num": "3", "den": "1"}],
            "bounds": list(bounds)}


def bound(**kw) -> dict:
    b = {"id": "b", "kind": "bound", "symbol": "x", "quantity": "q", "unit": "Pa",
         "lower": {"num": "0", "den": "1", "strict": False}, "upper": None, "theorem": "T.pos", "languages": L4}
    b.update(kw)
    return b


def problems(*bounds: dict) -> list[str]:
    t = table(*bounds)
    return g.bound_problems(t, {"c": Fraction(3)}, PARITY)


class BoundTable(unittest.TestCase):
    def test_well_formed_bound_passes(self):
        self.assertEqual(problems(bound()), [])

    def test_refusals(self):
        cases = {
            "kind must be": bound(kind="value"),
            "already a row": bound(id="c"),
            "lower or an upper": bound(lower=None),
            "interval is empty": bound(upper={"num": "0", "den": "1", "strict": True}),
            "only have zero endpoints": bound(unit=None, lower={"num": "1", "den": "2", "strict": False}),
            "not a Lean name": bound(theorem="T.missing"),
            "differ from formal_parity.json": bound(theorem="T.leanOnly"),
            "not in the constants table": bound(row="nowhere"),
            "the bound in Pa": bound(row="c"),
            "lies outside the bound": bound(row="c", unit="m s⁻¹", upper={"num": "2", "den": "1", "strict": False}),
        }
        for why, b in cases.items():
            with self.subTest(why=why):
                self.assertTrue(any(why in p for p in problems(b)), problems(b))

    def test_sign_bound_without_unit(self):
        self.assertEqual(problems(bound(unit=None)), [])

    def test_row_inside(self):
        self.assertEqual(problems(bound(row="c", unit="m s⁻¹", lower={"num": "3", "den": "1", "strict": False})), [])
        self.assertTrue(problems(bound(row="c", unit="m s⁻¹", lower={"num": "3", "den": "1", "strict": True})))

    def test_admitted_by_strictness(self):
        b = bound(lower={"num": "-1", "den": "1", "strict": True}, upper={"num": "1", "den": "2", "strict": False})
        self.assertEqual([g.admitted(b, Fraction(v)) for v in ("-1", "-0.999", "1/2", "0.5001")],
                         [False, True, True, False])


class Rendering(unittest.TestCase):
    def test_endpoint_rounds_into_the_interval(self):
        third = (Fraction(1, 3), False)
        lo = float(g.rust_endpoint(third, "lower").split("at: ")[1].split(",")[0])
        hi = float(g.rust_endpoint(third, "upper").split("at: ")[1].split(",")[0])
        self.assertGreaterEqual(Fraction(lo), Fraction(1, 3))
        self.assertLessEqual(Fraction(hi), Fraction(1, 3))
        self.assertEqual(math.nextafter(hi, math.inf), lo)

    def test_coq_negative_literal(self):
        self.assertEqual(g.coq_q(Fraction(-1, 2)), "(Qmake (-1) 2)")
        self.assertEqual(g.coq_q(Fraction(3, 4)), "(Qmake 3 4)")

    def test_interval_text(self):
        self.assertEqual(g.interval(bound(lower=None, upper={"num": "1", "den": "1", "strict": False})), "(−∞, 1]")
        self.assertEqual(g.interval(bound(lower={"num": "0", "den": "1", "strict": True})), "(0, ∞)")

    def test_repo_name_reads_the_lake_package(self):
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, "Lean"))
            with open(os.path.join(d, "Lean/lakefile.lean"), "w", encoding="utf-8") as f:
                f.write("import Lake\npackage «umst-formal» where\n")
            self.assertEqual(g.repo_name(d), "umst-formal")
            os.remove(os.path.join(d, "Lean/lakefile.lean"))
            self.assertEqual(g.repo_name(d), os.path.basename(d))


class Table(unittest.TestCase):
    """The committed table itself: every bound is well formed and proved, and each language's module is written."""

    def test_committed_bounds(self):
        t = g.load()
        self.assertEqual(g.bound_problems(t, g.values(t), g.parity_statements()), [])

    def test_bounds_modules_generated(self):
        out = g.outputs()
        if g.REPO != g.HOME or not g.load().get("bounds"):
            self.skipTest("bounds are generated in umst-formal only")
        for path in ("Lean/Constants/Bounds.lean", "Coq/Constants/Bounds.v", "Agda/Constants/Bounds.agda",
                     "Haskell/UMST/Constants/Bounds.hs", "Haskell/test/ConstantsBoundsProps.hs"):
            self.assertIn(path, out)
        for b in g.load()["bounds"]:
            self.assertIn(f"alias {b['id']}_theorem := {b['theorem']}", out["Lean/Constants/Bounds.lean"])
            self.assertIn(f"pub const {g.rust_name(b['id'])}_BOUND: Bound", out["constants-rs/src/lib.rs"])


if __name__ == "__main__":
    unittest.main()
