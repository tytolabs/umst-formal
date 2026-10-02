// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// Rational witness grid for Lean `Concrete.StiffnessTransition` (L1a): the stiffness scale
// max(α − 1/2, 0) and the M1-negative elastic summand ψ = −c · E₀ · ε² · scale(α), evaluated in
// Rust on the seven grid rows whose values Lean proves (`stiffness_scale_grid_row*`,
// `psi_stiffness_alpha_grid_row*`).

use super::stiffness_scale;

/// v2 rational grid row count.
pub const V2_GRID_ROW_COUNT: usize = 7;

/// Elastic coupling in the ψ summand — mirrors Lean `stiffnessCoupling`.
pub const STIFFNESS_COUPLING: f64 = 0.1;

/// One v2 rational witness row (pinned from cartridge fixture v2 first 7 rows).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct V2GridRow {
    pub alpha: f64,
    pub epsilon: f64,
    pub e0_pa: f64,
    pub expected_scale: f64,
    pub expected_psi: f64,
}

/// Pinned v2 grid rows (7/7 conformance).
pub const V2_GRID_ROWS: [V2GridRow; V2_GRID_ROW_COUNT] = [
    V2GridRow {
        alpha: 0.5,
        epsilon: 0.01,
        e0_pa: 30e9,
        expected_scale: 0.0,
        expected_psi: 0.0,
    },
    V2GridRow {
        alpha: 0.75,
        epsilon: 0.01,
        e0_pa: 30e9,
        expected_scale: 0.25,
        expected_psi: -75_000.0,
    },
    V2GridRow {
        alpha: 1.0,
        epsilon: 0.02,
        e0_pa: 30e9,
        expected_scale: 0.5,
        expected_psi: -600_000.0,
    },
    V2GridRow {
        alpha: 0.6,
        epsilon: 0.015,
        e0_pa: 25e9,
        expected_scale: 0.1,
        expected_psi: -56_250.0,
    },
    V2GridRow {
        alpha: 0.4,
        epsilon: 0.01,
        e0_pa: 30e9,
        expected_scale: 0.0,
        expected_psi: 0.0,
    },
    V2GridRow {
        alpha: 0.8,
        epsilon: 0.0,
        e0_pa: 30e9,
        expected_scale: 0.3,
        expected_psi: 0.0,
    },
    V2GridRow {
        alpha: 0.45,
        epsilon: 0.02,
        e0_pa: 28e9,
        expected_scale: 0.0,
        expected_psi: 0.0,
    },
];

/// Closed-form ψ_stiffness_α on slice-1 scalar path.
#[must_use]
pub fn psi_stiffness_alpha_closed_form(epsilon: f64, e0_pa: f64, alpha: f64) -> f64 {
    -STIFFNESS_COUPLING * e0_pa * epsilon * epsilon * stiffness_scale(alpha)
}

/// v2 grid conformance — returns first mismatch index or None.
#[must_use]
pub fn v2_grid_conformance_mismatch() -> Option<usize> {
    for (idx, row) in V2_GRID_ROWS.iter().enumerate() {
        let scale = stiffness_scale(row.alpha);
        if (scale - row.expected_scale).abs() >= 1e-12 {
            return Some(idx);
        }
        let psi = psi_stiffness_alpha_closed_form(row.epsilon, row.e0_pa, row.alpha);
        if (psi - row.expected_psi).abs() >= 1e-3 {
            return Some(idx);
        }
    }
    None
}

/// M1-negative ψ ≤ 0 on every v2 grid row (Lean `psi_stiffness_alpha_nonpos`).
#[must_use]
pub fn psi_nonpos_witness_holds() -> bool {
    V2_GRID_ROWS.iter().all(|row| {
        row.expected_psi <= 0.0
            && psi_stiffness_alpha_closed_form(row.epsilon, row.e0_pa, row.alpha) <= 1e-12
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::STIFFNESS_ALPHA_THRESHOLD;
    use std::collections::HashMap;

    /// Lean source of the grid theorems, relative to the `umst-formal/` root.
    const LEAN_SOURCE_RELPATH: &str = "Lean/Concrete/StiffnessTransition.lean";

    fn lean_source() -> String {
        let path = std::path::PathBuf::from(
            std::env::var("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR for tests"),
        )
        .join("..")
        .join(LEAN_SOURCE_RELPATH);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }

    /// A Lean rational literal: `p`, `-p` or `p / q`.
    fn rational(term: &str) -> Option<f64> {
        let term = term.trim();
        match term.split_once('/') {
            Some((p, q)) => Some(p.trim().parse::<f64>().ok()? / q.trim().parse::<f64>().ok()?),
            None => term.parse().ok(),
        }
    }

    /// Values of `def NAME : ℚ := LITERAL` lines.
    fn rational_defs(src: &str) -> HashMap<String, f64> {
        src.lines()
            .filter_map(|line| {
                let rest = line.trim().strip_prefix("def ")?;
                let (name, rhs) = rest.split_once(" : ℚ := ")?;
                Some((name.trim().to_string(), rational(rhs)?))
            })
            .collect()
    }

    /// Arguments of an application: parenthesised groups or bare tokens.
    fn args(s: &str, defs: &HashMap<String, f64>) -> Option<Vec<f64>> {
        let mut out = Vec::new();
        let mut rest = s.trim();
        while !rest.is_empty() {
            let (tok, tail) = if let Some(inner) = rest.strip_prefix('(') {
                let close = inner.find(')')?;
                (&inner[..close], &inner[close + 1..])
            } else {
                rest.split_at(rest.find(' ').unwrap_or(rest.len()))
            };
            out.push(defs.get(tok.trim()).copied().or_else(|| rational(tok))?);
            rest = tail.trim();
        }
        Some(out)
    }

    /// Statements `HEAD args = value := by` in the Lean source, evaluated.
    fn lean_grid_statements(src: &str, head: &str) -> Vec<(Vec<f64>, f64)> {
        let defs = rational_defs(src);
        src.lines()
            .filter_map(|line| {
                let stmt = line.trim().strip_prefix(head)?.strip_suffix(":= by")?;
                let (lhs, rhs) = stmt.rsplit_once(" = ")?;
                Some((args(lhs, &defs)?, rational(rhs)?))
            })
            .collect()
    }

    fn close(a: f64, b: f64) -> bool {
        (a - b).abs() <= 1e-9 * a.abs().max(b.abs()).max(1.0)
    }

    #[test]
    fn v2_grid_7_of_7_conforms() {
        assert!(v2_grid_conformance_mismatch().is_none());
        assert_eq!(V2_GRID_ROWS.len(), V2_GRID_ROW_COUNT);
    }

    #[test]
    fn rust_constants_match_lean_definitions() {
        let defs = rational_defs(&lean_source());
        assert_eq!(defs.get("stiffnessCoupling"), Some(&STIFFNESS_COUPLING));
        assert_eq!(
            defs.get("stiffnessAlphaThreshold"),
            Some(&STIFFNESS_ALPHA_THRESHOLD)
        );
    }

    #[test]
    fn every_lean_psi_grid_theorem_is_a_rust_grid_row() {
        let src = lean_source();
        let stmts = lean_grid_statements(&src, "psi_stiffness_alpha ");
        let theorems = src
            .lines()
            .filter(|l| l.starts_with("theorem psi_stiffness_alpha_grid_row"))
            .count();
        assert!(theorems > 0, "no psi_stiffness_alpha grid theorems in Lean");
        assert_eq!(
            stmts.len(),
            theorems,
            "every Lean psi grid statement parses"
        );
        for (a, value) in &stmts {
            let [eps, e0, alpha] = a[..] else {
                panic!("psi_stiffness_alpha takes three arguments: {a:?}");
            };
            let row = V2_GRID_ROWS
                .iter()
                .find(|r| close(r.epsilon, eps) && close(r.e0_pa, e0) && close(r.alpha, alpha))
                .unwrap_or_else(|| panic!("Lean grid point {a:?} missing from V2_GRID_ROWS"));
            assert!(close(row.expected_psi, *value), "{row:?} vs Lean {value}");
            assert!(close(
                psi_stiffness_alpha_closed_form(eps, e0, alpha),
                *value
            ));
        }
    }

    #[test]
    fn every_lean_scale_grid_theorem_is_a_rust_grid_row() {
        let src = lean_source();
        let stmts = lean_grid_statements(&src, "stiffnessScale ");
        let theorems = src
            .lines()
            .filter(|l| l.starts_with("theorem stiffness_scale_grid_row"))
            .count();
        assert!(theorems > 0, "no stiffness_scale grid theorems in Lean");
        assert_eq!(
            stmts.len(),
            theorems,
            "every Lean scale grid statement parses"
        );
        for (a, value) in &stmts {
            let [alpha] = a[..] else {
                panic!("stiffnessScale takes one argument: {a:?}");
            };
            let row = V2_GRID_ROWS
                .iter()
                .find(|r| close(r.alpha, alpha))
                .unwrap_or_else(|| panic!("Lean grid alpha {alpha} missing from V2_GRID_ROWS"));
            assert!(close(row.expected_scale, *value), "{row:?} vs Lean {value}");
            assert!(close(stiffness_scale(alpha), *value));
        }
    }

    #[test]
    fn psi_is_nonpositive_and_vanishes_at_threshold() {
        assert!(psi_nonpos_witness_holds());
        assert_eq!(stiffness_scale(STIFFNESS_ALPHA_THRESHOLD), 0.0);
    }
}
