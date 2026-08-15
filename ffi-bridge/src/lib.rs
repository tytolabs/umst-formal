// SPDX-License-Identifier: MIT
//
// umst-ffi-bridge — material-agnostic C-ABI thermodynamic gate
//
// Pure morphisms only: scalars in → scalars out. Cement chemistry lives in
// `umst-concrete-ffi` (cartridge fiber).

mod agap_2350_l1_inventory;
mod agap_2350_l2_attestation;
mod agap_2350_l6_attestation;
mod formal_swarm_deepen;
#[path = "extract_runtime.rs"]
mod l5_extract_runtime;
#[path = "lcert.rs"]
mod l5_lcert;
#[path = "lcert_capstone.rs"]
mod l7_lcert_capstone;
mod lean_l1_bridge_prep;
mod lean_l1_stiffness_adopt;
mod lean_rs_cold_path;
mod pbm_007_ws_cert_proved;
mod pbm_009_ws_faithful_all;
mod pbm_010_atoms_scalar;

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

pub use lean_rs_cold_path::{
    formal_root as lean_rs_formal_root, l1_on_disk_sources, lean_rs_cold_path_v2_honest,
    lean_rs_cold_path_v2_probe, lean_rs_cold_path_z65_honest, lean_rs_cold_path_z65_probe,
    lean_source_on_disk, pending_inventory_census, LeanRsColdPathV2Probe, LeanRsColdPathZ65Probe,
    LeanRsPendingRow, LeanRsPendingStatus, H50_RUST_SURFACE, JOB_ID as LEAN_RS_COLD_PATH_JOB_ID,
    L1A_LEAN_SOURCE, L1B_LEAN_SOURCE, PENDING_INVENTORY as LEAN_RS_PENDING_INVENTORY,
    POSTURE_TAG as LEAN_RS_COLD_PATH_POSTURE, PRIOR_H50_RECEIPT_PATH, PRIOR_J31_RECEIPT_PATH,
    PRIOR_X37_RECEIPT_PATH, RECEIPT_PATH as LEAN_RS_COLD_PATH_RECEIPT_PATH, SCHEMA_VERSION,
    WORKSTREAM_ID as LEAN_RS_WORKSTREAM_ID, Z65_JOB_ID as LEAN_RS_Z65_JOB_ID,
    Z65_RECEIPT_PATH as LEAN_RS_Z65_RECEIPT_PATH, Z65_WAVE_SLOT as LEAN_RS_Z65_WAVE_SLOT,
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
    l1a_lean_source_on_disk, l1b_lean_source_on_disk, lean_l1_adopt_audit_closed,
    lean_l1_y41_honest, lean_l1_y41_probe, lean_l1_z37_honest, lean_l1_z37_probe,
    run_l1_adopt_audit, v2_grid_conformance_mismatch, L1AdoptAudit, L1AdoptProbe, LeanL1Y41Probe,
    LeanL1Z37Probe, EXPECTED_LEMMA_COUNT as L1_ADOPT_EXPECTED_LEMMA_COUNT,
    EXPECTED_PROVED_COUNT as L1_ADOPT_EXPECTED_PROVED_COUNT,
    EXPECTED_THEOREM_COUNT as L1_ADOPT_EXPECTED_THEOREM_COUNT, JOB_ID as LEAN_L1_Y41_JOB_ID,
    L1_PROBE_COUNT as L1_ADOPT_PROBE_COUNT, POSTURE_TAG as L1_ADOPT_POSTURE,
    PRIOR_H50_RECEIPT_PATH as L1_ADOPT_PRIOR_H50_RECEIPT, PRIOR_X_SLOT as L1_ADOPT_PRIOR_X_SLOT,
    RECEIPT_PATH as LEAN_L1_Y41_RECEIPT_PATH, V2_GRID_ROW_COUNT as L1_V2_GRID_ROW_COUNT,
    WORKSTREAM_ID as L1_ADOPT_WORKSTREAM_ID, Z37_JOB_ID as LEAN_L1_Z37_JOB_ID,
    Z37_RECEIPT_PATH as LEAN_L1_Z37_RECEIPT_PATH, Z37_WAVE_SLOT as LEAN_L1_Z37_WAVE_SLOT,
};

pub use formal_swarm_deepen::{
    formal_swarm_deepen_honest, formal_swarm_deepen_probe, helmholtz_gate_correspondence,
    helmholtz_psi, psi_antitone_helmholtz_holds, psi_antitone_helmholtz_scenario,
    FormalSwarmDeepenProbe, HelmholtzWitnessScenario, JOB_ID as FORMAL_SWARM_JOB_ID,
    LEAN_WITNESS_MODULE, LEAN_WITNESS_THEOREM, PINNED_CATALOG_DIGEST_HEX,
    POSTURE_TAG as FORMAL_SWARM_POSTURE, PRIOR_RECEIPT_AGAP_2350, Q_HYD_J_PER_KG,
    RECEIPT_PATH as FORMAL_SWARM_RECEIPT_PATH,
};

pub use l5_extract_runtime::{
    haskell_module_inventory, l5_extract_runtime_honest, l5_extract_runtime_probe,
    l5_extraction_wired, l5_probe_detail, l5_receipt_status_label, l5_runtime_inventory,
    l5_workflow_path, L5ExtractRuntimeProbe, L5RuntimeInventory, JOB_ID as L5_EXTRACT_JOB_ID,
    L5_EXPECTED_GATE_EXIT, L5_GATE_SCRIPT_REL, L5_WORKFLOW_REL, POSTURE_TAG as L5_EXTRACT_POSTURE,
    PRIOR_SWARM_RECEIPT_PATH as L5_PRIOR_SWARM_RECEIPT, RECEIPT_PATH as L5_EXTRACT_RECEIPT_PATH,
};

pub use l5_lcert::{
    l5_lcert_factor_closed, l5_lcert_honest, l5_lcert_probe, L5LcertProbe,
    JOB_ID as L5_LCERT_JOB_ID, POSTURE_TAG as L5_LCERT_POSTURE,
    PRIOR_Y78_RECEIPT_PATH as L5_LCERT_PRIOR_Y78_RECEIPT, RECEIPT_PATH as L5_LCERT_RECEIPT_PATH,
    Z121_JOB_ID as L5_LCERT_Z121_JOB_ID, Z121_WAVE_SLOT as L5_LCERT_Z121_WAVE_SLOT,
};

pub use l7_lcert_capstone::{
    l6_crosswalk_partial, l6_crosswalk_wired, l7_capstone_wired, l7_lcert_capstone_honest,
    l7_lcert_capstone_probe, l_cert_ledger_path, lcert_factor_readiness_matrix,
    lcert_gate_factor_table, lcert_prereq_factor_rows, L7LcertCapstoneProbe, LcertFactorRow,
    JOB_ID as L7_LCERT_JOB_ID, LCERT_EXPECTED_GATE_EXIT, L_CERT_LEDGER_REL,
    POSTURE_TAG as L7_LCERT_POSTURE, PRIOR_RECEIPT_PATH as L7_PRIOR_RECEIPT,
    RECEIPT_PATH as L7_LCERT_RECEIPT_PATH,
};

pub use pbm_009_ws_faithful_all::{
    bench_consumer_posture_pins_honest, lean_faithful_gate_on_disk,
    pbm_009_ac03_fence_deepen_closed, pbm_009_ac03_honest, pbm_009_ac03_probe,
    pbm_009_done_when_probe, pbm_009_formal_fence_closed, pbm_009_fully_closed,
    pbm_009_j4_absorb_honest, pbm_009_j4_absorb_probe, pbm_009_production_tensor_closed,
    pbm_009_production_wired, pbm_009_ws_faithful_all_probe_honest,
    probe_pbm_009_ac03_fence_deepen, probe_pbm_009_formal_ws_faithful_all,
    run_formal_faithful_fence_audit, Pbm009Ac03Probe, Pbm009DoneWhenProbe, Pbm009FaithfulWireHop,
    Pbm009FormalAudit, Pbm009FormalProbe, Pbm009J4AbsorbProbe, Pbm009WsFaithfulAllProbe,
    ATOM_TOTAL as PBM_009_ATOM_TOTAL, B6_DISSIPATION_DEFER_SURFACE as PBM_009_B6_DISSIPATION,
    BENCH_CONSUMER_PATH as PBM_009_BENCH_PATH, BENCH_POSTURE_FIXTURE as PBM_009_POSTURE_FIXTURE,
    DEFER_BLOCKER_PINNED_COUNT as PBM_009_DEFER_BLOCKER_COUNT,
    D_EVALUATOR_LANDED_COUNT as PBM_009_D_LANDED_COUNT, FLEET_PARENT as PBM_009_FLEET_PARENT,
    FORMAL_PROBE_COUNT as PBM_009_FORMAL_PROBE_COUNT,
    FORMAL_WITNESS_RELPATH as PBM_009_FORMAL_WITNESS,
    J4_WIRE_HOP_COUNT as PBM_009_J4_WIRE_HOP_COUNT, JOB_ID as PBM_009_JOB_ID,
    LEAN_SOURCE_RELPATH as PBM_009_LEAN_SOURCE, PARENT_WORKSTREAM_ID as PBM_009_PARENT_ID,
    POSTURE_TAG as PBM_009_POSTURE, PRIOR_E4_RECEIPT as PBM_009_PRIOR_E4_RECEIPT,
    PRIOR_J4_JOB_ID as PBM_009_PRIOR_J4_JOB_ID, PRIOR_J4_RECEIPT as PBM_009_PRIOR_J4_RECEIPT,
    PRIOR_Y59_RECEIPT as PBM_009_PRIOR_Y59_RECEIPT, PRIOR_Z68_RECEIPT as PBM_009_PRIOR_Z68_RECEIPT,
    PSI_WITNESSED_COUNT as PBM_009_PSI_WITNESSED, RECEIPT_PATH as PBM_009_RECEIPT_PATH,
    WIRE_HOPS as PBM_009_WIRE_HOPS, WITNESSED_ATOM_COUNT as PBM_009_WITNESSED_COUNT,
    WORKSTREAM_ID as PBM_009_WORKSTREAM_ID,
};

pub use pbm_007_ws_cert_proved::{
    catalog_export_deferred as pbm_007_catalog_export_deferred, lean_cert_proved_posture_on_disk,
    pbm_007_d1650_honest, pbm_007_done_when_probe, pbm_007_formal_fence_closed,
    pbm_007_fully_closed, pbm_007_k1938_honest, pbm_007_k1938_probe,
    pbm_007_k1941_fence_deepen_closed, pbm_007_k1941_honest, pbm_007_k1941_probe,
    pbm_007_production_wired, pbm_007_ws_cert_proved_probe_honest,
    probe_pbm_007_formal_ws_cert_proved, probe_pbm_007_k1941_fence_deepen,
    run_formal_cert_proved_fence_audit, Pbm007CertProvedWireHop, Pbm007DoneWhenProbe,
    Pbm007FormalAudit, Pbm007FormalProbe, Pbm007K1938Probe, Pbm007K1941Probe,
    Pbm007WsCertProvedProbe, ABSORBED_J39_RECEIPT as PBM_007_ABSORBED_J39_RECEIPT,
    ABSORBED_Y58_RECEIPT as PBM_007_ABSORBED_Y58_RECEIPT,
    ABSORBED_Z100_RECEIPT as PBM_007_ABSORBED_Z100_RECEIPT,
    ABSORBED_Z43_RECEIPT as PBM_007_ABSORBED_Z43_RECEIPT,
    BENCH_CONSUMER_PATH as PBM_007_BENCH_PATH, BENCH_POSTURE_FIXTURE as PBM_007_POSTURE_FIXTURE,
    EXPECTED_PROVED_COUNT as PBM_007_EXPECTED_PROVED, FLEET_PARENT as PBM_007_FLEET_PARENT,
    FORMAL_PROBE_COUNT as PBM_007_FORMAL_PROBE_COUNT,
    FORMAL_WITNESS_RELPATH as PBM_007_FORMAL_WITNESS, JOB_ID as PBM_007_JOB_ID,
    K2_WIRE_HOP_COUNT as PBM_007_K2_WIRE_HOP_COUNT, LEAN_SOURCE_RELPATH as PBM_007_LEAN_SOURCE,
    META_OWNER_PATH as PBM_007_META_OWNER, PARENT_WORKSTREAM_ID as PBM_007_PARENT_ID,
    POSTH_02_BARC_SURFACE as PBM_007_POSTH_02_SURFACE, POSTURE_TAG as PBM_007_POSTURE,
    PRIOR_D3_JOB_ID as PBM_007_PRIOR_D3_JOB_ID, PRIOR_D3_RECEIPT as PBM_007_PRIOR_D3_RECEIPT,
    PRIOR_K2_JOB_ID as PBM_007_PRIOR_K2_JOB_ID, PRIOR_K2_RECEIPT as PBM_007_PRIOR_K2_RECEIPT,
    PROBE_COUNT as PBM_007_PROBE_COUNT, RECEIPT_PATH as PBM_007_RECEIPT_PATH,
    WIRE_HOPS as PBM_007_WIRE_HOPS, WORKSTREAM_ID as PBM_007_WORKSTREAM_ID,
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
    credit_greedy_sum_slices(n, weights, admissible)
}

/// Safe slice wrapper — shared by C ABI and `umst-ffi` correspondence tests.
#[must_use]
pub fn credit_greedy_sum_slices(n: usize, weights: *const f64, admissible: *const u8) -> f64 {
    if n == 0 || weights.is_null() || admissible.is_null() {
        return 0.0;
    }
    let mut s = 0.0;
    for i in 0..n {
        // SAFETY: caller guarantees `n` valid elements in each slice.
        if unsafe { *admissible.add(i) != 0 } {
            s += unsafe { *weights.add(i) };
        }
    }
    s
}

/// Safe slice wrapper for Rust callers (`weights.len()` must equal `admissible.len()`).
#[must_use]
pub fn credit_greedy_sum_safe(weights: &[f64], admissible: &[u8]) -> f64 {
    if weights.is_empty() || weights.len() != admissible.len() {
        return 0.0;
    }
    credit_greedy_sum_slices(weights.len(), weights.as_ptr(), admissible.as_ptr())
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

// ---------------------------------------------------------------------------
// AGAP-2350-FORMAL night residual deepen (honest GROUND-1 posture)
// ---------------------------------------------------------------------------

/// AGAP-2350 night slot id.
pub const FORMAL_NIGHT_2350_JOB_ID: &str = "AGAP-2350-FORMAL";

/// Completion receipt cross-ref for AGAP-2350 night wave.
pub const FORMAL_RECEIPT_PATH_2350: &str =
    "old/residuals/residuals/misc-outputs-tmp/COMPLETION_AGAP_AGENT_FORMAL_2350.md";

/// Prior formal crypto deepen receipt.
pub const FORMAL_PRIOR_RECEIPT_PATH: &str =
    "old/residuals/residuals/misc-outputs-tmp/COMPLETION_AGAP_AGENT_FORMAL-CRYPTO_2033.md";

/// Night deepen probe — Lean crypto GROUND-1 tier posture (no fake theorem GREEN).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormalNight2350DeepenProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub ffi_abi_version: u32,
    pub ground1_crypto_wired: bool,
    pub full_meso_sorry_free: bool,
    pub production_wired: bool,
}

/// AGAP-2350 FORMAL night deepen — honest partial formal posture.
#[must_use]
pub fn formal_night_2350_deepen_probe() -> FormalNight2350DeepenProbe {
    FormalNight2350DeepenProbe {
        job_id: FORMAL_NIGHT_2350_JOB_ID,
        receipt_path: FORMAL_RECEIPT_PATH_2350,
        ffi_abi_version: UMST_FFI_ABI_VERSION,
        ground1_crypto_wired: true,
        full_meso_sorry_free: false,
        production_wired: false,
    }
}

/// Honesty gate for operator receipts.
#[must_use]
pub fn formal_night_2350_deepen_honest(probe: &FormalNight2350DeepenProbe) -> bool {
    probe.job_id == FORMAL_NIGHT_2350_JOB_ID
        && probe.receipt_path.contains("FORMAL_2350")
        && probe.ffi_abi_version == UMST_FFI_ABI_VERSION
        && probe.ground1_crypto_wired
        && !probe.full_meso_sorry_free
        && !probe.production_wired
}

#[cfg(test)]
mod formal_night_2350_tests {
    use super::*;

    #[test]
    fn agap_2350_formal_night_metadata() {
        assert_eq!(FORMAL_NIGHT_2350_JOB_ID, "AGAP-2350-FORMAL");
        assert!(FORMAL_PRIOR_RECEIPT_PATH.contains("FORMAL-CRYPTO_2033"));
    }

    #[test]
    fn formal_night_deepen_honest_ground1_not_full_green() {
        let probe = formal_night_2350_deepen_probe();
        assert!(formal_night_2350_deepen_honest(&probe));
        assert!(!probe.full_meso_sorry_free);
        assert!(!probe.production_wired);
    }
}
