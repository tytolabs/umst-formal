// SPDX-License-Identifier: MIT
//
// umst-ffi-bridge — material-agnostic C-ABI thermodynamic gate
//
// Pure morphisms only: scalars in → scalars out. Cement chemistry lives in
// `umst-concrete-ffi` (cartridge fiber).

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
    let mut s = 0.0;
    for i in 0..n {
        if *admissible.add(i) != 0 {
            s += *weights.add(i);
        }
    }
    s
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
