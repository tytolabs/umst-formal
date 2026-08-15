// SPDX-License-Identifier: MIT
//
// SWARM-C25-0831-92 — FORMAL-DEEPEN: umst-formal crate one witness (honest PARTIAL).

use super::{umst_gate_check, UMST_FFI_ABI_VERSION};

/// SWARM slot id (0831 morning wave row 92).
pub const JOB_ID: &str = "SWARM-C25-0831-92";

/// Completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "old/residuals/residuals/swarm-0831/COMPLETION_SWARM_SWARM-C25-0831-92_0831.md";

/// Prior AGAP-2350 FORMAL night deepen receipt.
pub const PRIOR_RECEIPT_AGAP_2350: &str = "old/residuals/residuals/misc-outputs-tmp/COMPLETION_AGAP_AGENT_FORMAL_2350.md";

/// Lean theorem this witness cross-links (`Concrete/Helmholtz.lean`).
pub const LEAN_WITNESS_THEOREM: &str = "UMST.ψAntitoneHelmholtz";

/// Lean module authority for the witness.
pub const LEAN_WITNESS_MODULE: &str = "Concrete.Helmholtz";

/// Pinned catalog lock digest @ `egoff/umst-formal/artifacts/catalog.lock.json`.
pub const PINNED_CATALOG_DIGEST_HEX: &str =
    "aea5080d2ba81de9ddfdec1e4ca8f40ca851bd9bbd1a99b0416cea6ef8e85dff";

/// `Q_hyd` SSOT — matches Lean `UMST.Concrete.Q_hyd = 450`.
pub const Q_HYD_J_PER_KG: f64 = 450.0;

/// Honest adoption tier — computational witness only, not Proved export.
pub const POSTURE_TAG: &str = "witnessed-not-proved";

/// One concrete Helmholtz scenario matching Lean `ψAntitoneHelmholtz`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HelmholtzWitnessScenario {
    pub alpha_old: f64,
    pub alpha_new: f64,
    pub psi_old: f64,
    pub psi_new: f64,
}

/// Build Helmhotz ψ values ψ(α) = −Q_hyd · α matching Lean `Concrete.Gate`.
#[must_use]
pub fn helmholtz_psi(alpha: f64) -> f64 {
    -Q_HYD_J_PER_KG * alpha
}

/// Scenario for `ψAntitoneHelmholtz`: α advances ⇒ ψ decreases.
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

/// Computational witness: forward hydration lowers ψ (Lean `ψAntitoneHelmholtz`).
#[must_use]
pub fn psi_antitone_helmholtz_holds(s: &HelmholtzWitnessScenario) -> bool {
    s.alpha_old <= s.alpha_new && s.psi_new <= s.psi_old
}

/// Rust gate accepts the Helmholtz witness transition (integration `test_inv3` family).
#[must_use]
pub fn helmholtz_gate_correspondence() -> bool {
    let s = psi_antitone_helmholtz_scenario();
    let gate = umst_gate_check(
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
    );
    gate == 1 && psi_antitone_helmholtz_holds(&s)
}

/// Machine-checkable formal deepen census for operator / fleet probes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormalSwarmDeepenProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub posture: &'static str,
    pub lean_witness_theorem: &'static str,
    pub lean_witness_module: &'static str,
    pub catalog_digest_hex: &'static str,
    pub ffi_abi_version: u32,
    pub helmholtz_witness_holds: bool,
    pub gate_correspondence: bool,
    pub catalog_export_proved: bool,
    pub lake_build_green: bool,
}

/// SWARM-C25-0831-92 FORMAL deepen — honest partial formal posture.
#[must_use]
pub fn formal_swarm_deepen_probe() -> FormalSwarmDeepenProbe {
    FormalSwarmDeepenProbe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        posture: POSTURE_TAG,
        lean_witness_theorem: LEAN_WITNESS_THEOREM,
        lean_witness_module: LEAN_WITNESS_MODULE,
        catalog_digest_hex: PINNED_CATALOG_DIGEST_HEX,
        ffi_abi_version: UMST_FFI_ABI_VERSION,
        helmholtz_witness_holds: psi_antitone_helmholtz_holds(&psi_antitone_helmholtz_scenario()),
        gate_correspondence: helmholtz_gate_correspondence(),
        catalog_export_proved: false,
        lake_build_green: false,
    }
}

/// Honesty gate for operator receipts — one witness wired, no fake GREEN.
#[must_use]
pub fn formal_swarm_deepen_honest(probe: &FormalSwarmDeepenProbe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path.contains("SWARM-C25-0831-92")
        && probe.posture == POSTURE_TAG
        && probe.lean_witness_theorem.contains("ψAntitoneHelmholtz")
        && probe.helmholtz_witness_holds
        && probe.gate_correspondence
        && !probe.catalog_export_proved
        && !probe.lake_build_green
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn swarm_0831_92_metadata() {
        assert_eq!(JOB_ID, "SWARM-C25-0831-92");
        assert!(RECEIPT_PATH.contains("COMPLETION_SWARM_SWARM-C25-0831-92"));
        assert_eq!(PINNED_CATALOG_DIGEST_HEX.len(), 64);
    }

    #[test]
    fn psi_antitone_helmholtz_scenario_matches_lean_q_hyd() {
        let s = psi_antitone_helmholtz_scenario();
        assert!((s.psi_old - -225.0).abs() < 1e-9);
        assert!((s.psi_new - -315.0).abs() < 1e-9);
        assert!(psi_antitone_helmholtz_holds(&s));
    }

    #[test]
    fn formal_swarm_deepen_one_witness_honest_partial() {
        let probe = formal_swarm_deepen_probe();
        assert!(formal_swarm_deepen_honest(&probe));
        assert!(probe.helmholtz_witness_holds);
        assert!(probe.gate_correspondence);
        assert!(!probe.catalog_export_proved);
        assert!(!probe.lake_build_green);
    }
}
