// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// Rust witness of Lean `UMST.ψAntitoneHelmholtz` (Concrete/Helmholtz.lean) over the Helmholtz
// free-energy model ψ(α) = −Q_hyd · α of Concrete/Gate.lean, with Q_hyd read from the generated
// constants table.

use super::umst_gate_check;

/// Lean theorem this witness mirrors (`Concrete/Helmholtz.lean`).
pub const LEAN_WITNESS_THEOREM: &str = "UMST.ψAntitoneHelmholtz";

/// Lean module of the witnessed theorem.
pub const LEAN_WITNESS_MODULE: &str = "Concrete.Helmholtz";

/// Heat of complete hydration Q_hyd [J/g]: the row `hydrationHeatDefault` of
/// `constants/constants.json`, the value Lean `Concrete.Gate.Q_hyd` is defined as.
#[must_use]
pub fn q_hyd() -> f64 {
    umst_constants::HYDRATION_HEAT_DEFAULT
}

/// One Helmholtz transition: hydration and free energy before and after.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HelmholtzWitnessScenario {
    pub alpha_old: f64,
    pub alpha_new: f64,
    pub psi_old: f64,
    pub psi_new: f64,
}

/// Helmholtz free energy ψ(α) = −Q_hyd · α (Lean `Concrete.Gate.helmholtz`).
#[must_use]
pub fn helmholtz_psi(alpha: f64) -> f64 {
    -q_hyd() * alpha
}

/// Forward hydration α = 0.5 → 0.7 with ψ on the Helmholtz model.
#[must_use]
pub fn psi_antitone_helmholtz_scenario() -> HelmholtzWitnessScenario {
    let alpha_old = 0.5;
    let alpha_new = 0.7;
    HelmholtzWitnessScenario {
        alpha_old,
        alpha_new,
        psi_old: helmholtz_psi(alpha_old),
        psi_new: helmholtz_psi(alpha_new),
    }
}

/// The conclusion of `ψAntitoneHelmholtz` on a scenario: α advances and ψ does not rise.
#[must_use]
pub fn psi_antitone_helmholtz_holds(s: &HelmholtzWitnessScenario) -> bool {
    s.alpha_old <= s.alpha_new && s.psi_new <= s.psi_old
}

/// Gate decision on a Helmholtz transition at constant density, strength 20 → 30 MPa, dt = 1 h.
fn gate_on(s: &HelmholtzWitnessScenario) -> i32 {
    umst_gate_check(
        2000.0,
        s.psi_old,
        s.alpha_old,
        20.0,
        2000.0,
        s.psi_new,
        s.alpha_new,
        30.0,
        150.0,
        3600.0,
    )
}

/// The Rust gate admits the forward Helmholtz transition and the witness holds on it.
#[must_use]
pub fn helmholtz_gate_correspondence() -> bool {
    let s = psi_antitone_helmholtz_scenario();
    gate_on(&s) == 1 && psi_antitone_helmholtz_holds(&s)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn formal_root() -> std::path::PathBuf {
        std::path::PathBuf::from(
            std::env::var("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR for tests"),
        )
        .join("..")
    }

    #[test]
    fn q_hyd_is_the_generated_hydration_heat_default() {
        let row = umst_constants::ROWS
            .iter()
            .find(|r| r.id == "hydrationHeatDefault")
            .expect("hydrationHeatDefault row in umst-constants");
        assert_eq!(row.symbol, "Q_hyd");
        assert_eq!(row.unit, "J/g");
        assert_eq!(q_hyd(), row.value);
        let num: f64 = row.exact_num.parse().expect("exact numerator");
        let den: f64 = row.exact_den.parse().expect("exact denominator");
        assert!((num / den - q_hyd()).abs() <= f64::EPSILON * q_hyd());
        assert!(q_hyd() > 0.0, "Lean Q_hyd_pos");

        let gate = std::fs::read_to_string(formal_root().join("Lean/Concrete/Gate.lean"))
            .expect("Lean/Concrete/Gate.lean");
        assert!(
            gate.contains("def Q_hyd : ℚ := UMST.Constants.SI.hydrationHeatDefault"),
            "Lean Q_hyd is defined as the row this crate reads"
        );
    }

    #[test]
    fn helmholtz_psi_follows_the_lean_gradient_and_additivity_laws() {
        // helmholtzGradient: ψ(α + ε) − ψ(α) = −Q_hyd · ε.
        let s = psi_antitone_helmholtz_scenario();
        let eps = s.alpha_new - s.alpha_old;
        assert!((s.psi_new - s.psi_old + q_hyd() * eps).abs() < 1e-9);
        // helmholtz_one: ψ(1) = −Q_hyd.
        assert_eq!(helmholtz_psi(1.0), -q_hyd());
        // helmholtzAdditive: ψ(α₁ + α₂) = ψ(α₁) + ψ(α₂).
        assert!(
            (helmholtz_psi(0.3 + 0.4) - (helmholtz_psi(0.3) + helmholtz_psi(0.4))).abs() < 1e-9
        );
        assert!(psi_antitone_helmholtz_holds(&s));
        assert!(s.psi_new < s.psi_old, "Q_hyd > 0 makes the descent strict");
    }

    #[test]
    fn gate_admits_forward_and_rejects_reverse_helmholtz_transition() {
        assert!(helmholtz_gate_correspondence());
        let fwd = psi_antitone_helmholtz_scenario();
        let rev = HelmholtzWitnessScenario {
            alpha_old: fwd.alpha_new,
            alpha_new: fwd.alpha_old,
            psi_old: fwd.psi_new,
            psi_new: fwd.psi_old,
        };
        assert!(!psi_antitone_helmholtz_holds(&rev));
        assert_eq!(
            gate_on(&rev),
            0,
            "reverse hydration raises ψ and is rejected"
        );
    }
}
