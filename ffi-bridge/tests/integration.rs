// integration.rs — Black-box tests for the material-agnostic umst-ffi-bridge C ABI

use umst_ffi::*;

#[test]
fn test_inv1_mass_conservation_accepted() {
    let result = umst_gate_check(
        2000.0, -225.0, 0.5, 20.0, 2050.0, -315.0, 0.7, 30.0, 100.0, 3600.0,
    );
    assert_eq!(result, 1, "50 kg/m³ density change should be accepted");
}

#[test]
fn test_inv1_mass_conservation_rejected() {
    let result = umst_gate_check(
        2000.0, -225.0, 0.5, 20.0, 2200.0, -225.0, 0.5, 20.0, 150.0, 3600.0,
    );
    assert_eq!(result, 0, "200 kg/m³ density jump should be rejected");
}

#[test]
fn test_inv2_forward_dissipation_nonneg() {
    let d_int = umst_dissipation(2000.0, 2000.0, -225.0, -315.0, 3600.0);
    assert!(
        d_int >= 0.0,
        "D_int must be non-negative for forward hydration, got {d_int}"
    );
}

#[test]
fn test_inv2_reverse_dissipation_neg() {
    let d_int = umst_dissipation(2000.0, 2000.0, -315.0, -225.0, 3600.0);
    assert!(
        d_int < 0.0,
        "D_int must be negative for reverse hydration, got {d_int}"
    );
}

#[test]
fn test_inv2_energy_violation_rejected() {
    let result = umst_gate_check(
        2000.0, -315.0, 0.7, 30.0, 2000.0, -200.0, 0.7, 30.0, 150.0, 3600.0,
    );
    assert_eq!(result, 0, "Free-energy increase should be rejected");
}

#[test]
fn test_inv3_forward_hydration_accepted() {
    let result = umst_gate_check(
        2000.0, -225.0, 0.5, 20.0, 2000.0, -315.0, 0.7, 30.0, 150.0, 3600.0,
    );
    assert_eq!(
        result, 1,
        "Forward hydration (α: 0.5→0.7) should be accepted"
    );
}

#[test]
fn test_inv3_reverse_hydration_rejected() {
    let result = umst_gate_check(
        2000.0, -315.0, 0.7, 30.0, 2000.0, -225.0, 0.5, 20.0, 150.0, 3600.0,
    );
    assert_eq!(
        result, 0,
        "Reverse hydration (α: 0.7→0.5) should be rejected"
    );
}

#[test]
fn test_inv4_strength_increases_accepted() {
    let result = umst_gate_check(
        2000.0, -225.0, 0.5, 20.0, 2000.0, -315.0, 0.7, 35.0, 150.0, 3600.0,
    );
    assert_eq!(result, 1, "Strength increase should be accepted");
}

#[test]
fn test_identity_always_accepted() {
    let result = umst_gate_check(
        2000.0, -315.0, 0.7, 30.0, 2000.0, -315.0, 0.7, 30.0, 150.0, 3600.0,
    );
    assert_eq!(result, 1, "Identity transition must always be accepted");
}

#[test]
fn test_dissipation_zero_dt_guard() {
    let d = umst_dissipation(2000.0, 2000.0, -225.0, -315.0, 0.0);
    assert!(d.is_finite(), "D_int must be finite for dt=0");
    assert!(d >= 0.0, "D_int must be non-negative for forward hydration at dt=0");
}

#[test]
fn test_umst_n_warmup_reference_triple() {
    assert_eq!(umst_n_warmup(1.0, 0.5, 1.0), 3);
}

#[test]
fn test_umst_n_quantile_reference_triple() {
    assert_eq!(umst_n_quantile(1.0, 0.5, 1.0, 0.25), 3);
    assert_eq!(umst_n_quantile(1.0, 0.5, 1.0, 0.75), 3);
}

#[test]
fn test_abi_version_tags() {
    assert_eq!(umst_ffi_abi_version(), 9);
    assert_eq!(umst_ffi_abi_version_expected(), 9);
}
