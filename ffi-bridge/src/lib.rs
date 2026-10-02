// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// umst-ffi-bridge — material-agnostic C-ABI thermodynamic gate
//
// Pure morphisms only: scalars in → scalars out. Cement chemistry lives in
// `umst-concrete-ffi` (cartridge fiber).

mod agap_2350_l1_inventory;
mod agap_2350_l2_attestation;
mod agap_2350_l6_attestation;
mod extract_runtime;
mod helmholtz_witness;
mod lcert;
mod lcert_capstone;
mod lean_l1_bridge_prep;
mod lean_l1_stiffness_adopt;
mod theorem_crosswalk_shim;

pub use agap_2350_l1_inventory::{
    agap_2350_l1_honest, agap_2350_l1_probe, l1_cluster_inventory as agap_l1_cluster_inventory,
    l1_qc_bisim_cluster_count as agap_l1_qc_bisim_cluster_count, Agap2350L1Probe, L1InventoryRow,
    JOB_ID as AGAP_2350_L1_JOB_ID, L1_EXPECTED_CLUSTER_COUNT as AGAP_L1_EXPECTED_CLUSTER_COUNT,
    PRIOR_H24_RECEIPT_PATH as AGAP_L1_PRIOR_H24_RECEIPT, RECEIPT_PATH as AGAP_2350_L1_RECEIPT_PATH,
};

pub use agap_2350_l2_attestation::{
    agap_2350_l2_honest, agap_2350_l2_probe, l2_attestation_wired as agap_l2_attestation_wired,
    l2_inline_proof_populators_wired, l2_nested_populator_schema_wired, l2_registry_bound_count,
    registry_has_theorem as l2_registry_has_theorem, Agap2350L2Probe,
    JOB_ID as AGAP_2350_L2_JOB_ID, L2_METRIC_THEOREM_BINDINGS, L2_SNAPSHOT_BOUND_FIELDS,
    PRIOR_SWARM_RECEIPT_PATH as AGAP_L2_PRIOR_SWARM_RECEIPT,
    RECEIPT_PATH as AGAP_2350_L2_RECEIPT_PATH,
};

pub use agap_2350_l6_attestation::{
    agap_2350_l6_honest, agap_2350_l6_probe, l6_crosswalk_fully_wired,
    l6_crosswalk_wired as agap_l6_crosswalk_wired, l6_probe_detail, Agap2350L6Probe,
    JOB_ID as AGAP_2350_L6_JOB_ID, L6_DUMP_SCRIPT_REL, L6_EXPECTED_GATE_EXIT, L6_GATE_SCRIPT_REL,
    L6_MIN_MAP_ROWS, POSTURE_TAG as L6_POSTURE_TAG,
    PRIOR_Y_RECEIPT_PATH as AGAP_L6_PRIOR_Y_RECEIPT, RECEIPT_PATH as AGAP_2350_L6_RECEIPT_PATH,
};

pub use lean_l1_bridge_prep::{
    e_eff_mt_at_zero_holds, effective_modulus_mt, l1_bridge_witness_rows,
    lean_l1_bridge_j31_honest, lean_l1_bridge_j31_probe, lean_l1_bridge_prep_honest,
    lean_l1_bridge_prep_probe, psi_elastic_base, psi_elastic_base_nonpos_holds,
    psi_softening_micro_mechanics_holds, stiffness_scale, stiffness_scale_mono_holds,
    L1BridgeWitnessRow, LeanL1BridgeJ31Probe, LeanL1BridgePrepProbe, COMPOSER_J31_JOB_ID,
    COMPOSER_J31_RECEIPT_PATH, DAMAGE_D_MAX as L1_DAMAGE_D_MAX, JOB_ID as LEAN_L1_BRIDGE_JOB_ID,
    L1A_LEAN_MODULE, L1A_WITNESS_THEOREM, L1B_LEAN_MODULE, L1B_WITNESS_THEOREM,
    POSTURE_TAG as LEAN_L1_BRIDGE_POSTURE, PRIOR_G_SLOT as LEAN_L1_PRIOR_G_SLOT,
    RECEIPT_PATH as LEAN_L1_BRIDGE_RECEIPT_PATH, STIFFNESS_ALPHA_THRESHOLD,
};

pub use lean_l1_stiffness_adopt::{
    psi_nonpos_witness_holds, psi_stiffness_alpha_closed_form, v2_grid_conformance_mismatch,
    V2GridRow, STIFFNESS_COUPLING, V2_GRID_ROWS, V2_GRID_ROW_COUNT as L1_V2_GRID_ROW_COUNT,
};

pub use helmholtz_witness::{
    helmholtz_gate_correspondence, helmholtz_psi, psi_antitone_helmholtz_holds,
    psi_antitone_helmholtz_scenario, q_hyd, HelmholtzWitnessScenario, LEAN_WITNESS_MODULE,
    LEAN_WITNESS_THEOREM,
};

pub use extract_runtime::{
    haskell_module_inventory, l5_extract_runtime_honest, l5_extract_runtime_probe,
    l5_extraction_wired, l5_probe_detail, l5_receipt_status_label, l5_runtime_inventory,
    l5_workflow_path, L5ExtractRuntimeProbe, L5RuntimeInventory, JOB_ID as L5_EXTRACT_JOB_ID,
    L5_EXPECTED_GATE_EXIT, L5_GATE_SCRIPT_REL, L5_WORKFLOW_REL, POSTURE_TAG as L5_EXTRACT_POSTURE,
    PRIOR_SWARM_RECEIPT_PATH as L5_PRIOR_SWARM_RECEIPT, RECEIPT_PATH as L5_EXTRACT_RECEIPT_PATH,
};

pub use lcert::{
    l5_lcert_factor_closed, l5_lcert_honest, l5_lcert_probe, L5LcertProbe,
    JOB_ID as L5_LCERT_JOB_ID, POSTURE_TAG as L5_LCERT_POSTURE,
    PRIOR_Y78_RECEIPT_PATH as L5_LCERT_PRIOR_Y78_RECEIPT, RECEIPT_PATH as L5_LCERT_RECEIPT_PATH,
    Z121_JOB_ID as L5_LCERT_Z121_JOB_ID, Z121_WAVE_SLOT as L5_LCERT_Z121_WAVE_SLOT,
};

pub use lcert_capstone::{
    l6_crosswalk_partial, l6_crosswalk_wired, l7_capstone_wired, l7_lcert_capstone_honest,
    l7_lcert_capstone_probe, l_cert_ledger_path, lcert_factor_readiness_matrix,
    lcert_gate_factor_table, lcert_prereq_factor_rows, L7LcertCapstoneProbe, LcertFactorRow,
    JOB_ID as L7_LCERT_JOB_ID, LCERT_EXPECTED_GATE_EXIT, L_CERT_LEDGER_REL,
    POSTURE_TAG as L7_LCERT_POSTURE, PRIOR_RECEIPT_PATH as L7_PRIOR_RECEIPT,
    RECEIPT_PATH as L7_LCERT_RECEIPT_PATH,
};

use umst_manifold::gate::thermodynamic_transition_admissible;

// ---------------------------------------------------------------------------
// ABI versioning (must stay in sync with `include/umst_ffi.h`)
// ---------------------------------------------------------------------------

/// Current C-ABI surface version.
pub const UMST_FFI_ABI_VERSION: u32 = 9;

/// Minimum `.so` ABI version required by current consumer bindings.
/// ABI 9 removed filter handles and cement symbols — ABI-8 consumers cannot link.
pub const UMST_FFI_ABI_VERSION_MIN_COMPATIBLE: u32 = 9;

// ---------------------------------------------------------------------------
// Gate check — pure admissibility decision (no filter handle)
// ---------------------------------------------------------------------------

/// Check whether a state transition (old → new) is thermodynamically admissible.
///
/// Evaluates mass conservation, Clausius–Duhem dissipation, hydration irreversibility,
/// strength monotonicity, and upper strength bound.
///
/// Returns 1 if admissible, 0 if rejected.
#[must_use]
#[no_mangle]
pub extern "C" fn umst_gate_check(
    old_density: f64,
    old_free_energy: f64,
    old_hydration: f64,
    old_strength: f64,
    new_density: f64,
    new_free_energy: f64,
    new_hydration: f64,
    new_strength: f64,
    new_max_strength: f64,
    dt: f64,
) -> i32 {
    if thermodynamic_transition_admissible(
        old_density,
        old_free_energy,
        old_hydration,
        old_strength,
        new_density,
        new_free_energy,
        new_hydration,
        new_strength,
        new_max_strength,
        dt,
    ) {
        1
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// Dissipation value — for quantitative checks
// ---------------------------------------------------------------------------

/// Compute the internal dissipation D_int for a state transition.
///
/// D_int = -rho * (psi_new - psi_old) / dt
#[must_use]
#[no_mangle]
pub extern "C" fn umst_dissipation(
    old_density: f64,
    new_density: f64,
    old_free_energy: f64,
    new_free_energy: f64,
    dt: f64,
) -> f64 {
    let rho = (old_density + new_density) / 2.0;
    let psi_dot = (new_free_energy - old_free_energy) / (dt + 1e-10);
    -rho * psi_dot
}

// ---------------------------------------------------------------------------
// Credit aggregate (Phase M4)
// ---------------------------------------------------------------------------

/// Sum `weights[i]` for each `i` with `admissible[i] != 0`.
///
/// # Safety
/// `weights` and `admissible` must each point to `n` valid elements (when `n > 0`).
#[no_mangle]
pub unsafe extern "C" fn umst_credit_greedy_sum(
    n: usize,
    weights: *const f64,
    admissible: *const u8,
) -> f64 {
    if n == 0 || weights.is_null() || admissible.is_null() {
        return 0.0;
    }
    // SAFETY: the caller guarantees `n` valid, initialised elements behind each non-null pointer.
    let (weights, admissible) = unsafe {
        (
            std::slice::from_raw_parts(weights, n),
            std::slice::from_raw_parts(admissible, n),
        )
    };
    credit_greedy_sum_safe(weights, admissible)
}

/// Sum `weights[i]` for each `i` with `admissible[i] != 0`; 0 when the lengths differ.
#[must_use]
pub fn credit_greedy_sum_safe(weights: &[f64], admissible: &[u8]) -> f64 {
    if weights.len() != admissible.len() {
        return 0.0;
    }
    weights
        .iter()
        .zip(admissible)
        .filter(|(_, &a)| a != 0)
        .map(|(w, _)| w)
        .sum()
}

// ---------------------------------------------------------------------------
// Dignity step (Phase N3-FPD-a)
// ---------------------------------------------------------------------------

const DIGNITY_D_MAX: f64 = 10.0;
const DIGNITY_K_B: f64 = 1.380_649e-23;

#[inline]
fn landauer_joules_per_bit_dignity(temperature_k: f64) -> f64 {
    DIGNITY_K_B * temperature_k.max(0.0) * std::f64::consts::LN_2
}

#[must_use]
#[no_mangle]
pub extern "C" fn umst_dignity_step(
    temperature_k: f64,
    current_dignity: f64,
    delta_mi_bits: f64,
    delta_energy_j: f64,
) -> f64 {
    let floor = landauer_joules_per_bit_dignity(temperature_k) * delta_mi_bits;
    let honest = floor <= delta_energy_j;
    if honest {
        (current_dignity + delta_mi_bits).min(DIGNITY_D_MAX)
    } else {
        current_dignity
    }
}

// ---------------------------------------------------------------------------
// η_cog (Phase N3-FPD-b)
// ---------------------------------------------------------------------------

#[must_use]
#[no_mangle]
pub extern "C" fn umst_eta_cog(
    temperature_k: f64,
    dignity_value: f64,
    delta_mi_bits: f64,
    delta_energy_j: f64,
) -> f64 {
    let lb = landauer_joules_per_bit_dignity(temperature_k);
    let denom = delta_energy_j + lb;
    if !(temperature_k > 0.0
        && delta_mi_bits >= 0.0
        && delta_energy_j >= 0.0
        && dignity_value >= 0.0
        && denom > 0.0)
    {
        return 0.0;
    }
    dignity_value * delta_mi_bits / denom
}

// ---------------------------------------------------------------------------
// ρ-based Gaussian MI in bits (Phase FPD-RhoEstimator)
// ---------------------------------------------------------------------------

#[must_use]
#[no_mangle]
pub extern "C" fn umst_rho_mi_bits(rho: f64) -> f64 {
    umst_math::rho_estimator::rho_mi_bits(rho)
}

// ---------------------------------------------------------------------------
// Median convergence warmup (Phase FPD-MedianConvergence)
// ---------------------------------------------------------------------------

#[must_use]
#[no_mangle]
pub extern "C" fn umst_n_warmup(epsilon: f64, delta: f64, rho_min: f64) -> u64 {
    umst_math::median_convergence::n_warmup(epsilon, delta, rho_min)
}

#[must_use]
#[no_mangle]
pub extern "C" fn umst_n_quantile(epsilon: f64, delta: f64, rho_min: f64, q: f64) -> u64 {
    umst_math::order_statistics_band::n_quantile(epsilon, delta, rho_min, q).unwrap_or(0)
}

#[must_use]
#[no_mangle]
pub extern "C" fn umst_ffi_abi_version() -> u32 {
    UMST_FFI_ABI_VERSION
}

#[must_use]
#[no_mangle]
pub extern "C" fn umst_ffi_abi_version_expected() -> u32 {
    UMST_FFI_ABI_VERSION_MIN_COMPATIBLE
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn credit_greedy_sum_adds_admissible_weights_only() {
        let w = [1.5, 2.0, 4.0];
        let a = [1u8, 0, 1];
        assert_eq!(credit_greedy_sum_safe(&w, &a), 5.5);
        assert_eq!(credit_greedy_sum_safe(&w, &a[..2]), 0.0, "length mismatch");
        // SAFETY: both arrays hold three elements.
        let c = unsafe { umst_credit_greedy_sum(3, w.as_ptr(), a.as_ptr()) };
        assert_eq!(c, 5.5);
        // SAFETY: null pointers are rejected before any read.
        let z = unsafe { umst_credit_greedy_sum(3, std::ptr::null(), a.as_ptr()) };
        assert_eq!(z, 0.0);
    }
}
