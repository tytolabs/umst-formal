// SPDX-License-Identifier: MIT
//
// umst-ffi-bridge — C-ABI surface for the UMST thermodynamic gate
//
// This crate exposes a minimal, stable C interface to the core invariant-
// checking functions in umst-core.  It exists so that Haskell (via
// `foreign import ccall`) and OCaml (via Ctypes) can call the Rust gate
// without modifying a single line of the upstream kernel.
//
// Design principles:
//   1. Every exported function is `extern "C"` + `#[no_mangle]`.
//   2. All arguments and return values are C-compatible scalars or
//      opaque pointers — no Rust-specific types cross the ABI boundary.
//   3. The crate produces both a dynamic library (.dylib / .so) and a
//      static archive (.a) so consumers can choose their linking strategy.
//
// Physical correspondence:
//   The four exported functions correspond one-to-one with the four
//   invariants proved in the Agda and Coq layers:
//     umst_gate_check        ↔ Clausius-Duhem + mass + strength (all four)
//     umst_hydration_degree  ↔ Hydration irreversibility
//     umst_strength_powers   ↔ Strength monotonicity (Powers model)
//     umst_dissipation       ↔ Clausius-Duhem dissipation value

use umst_core::science::thermodynamic_filter::{ThermodynamicFilter, ThermodynamicState};

// ---------------------------------------------------------------------------
// ABI versioning (must stay in sync with `umst-ffi` and `include/umst_ffi.h`)
// ---------------------------------------------------------------------------

/// Current C-ABI surface version (bump on additive entry points per release notes in `umst-ffi`).
pub const UMST_FFI_ABI_VERSION: u32 = 8;

/// Minimum `.so` ABI version required by current Haskell / consumer bindings (`actual >= min`).
/// Breaking removals / signature changes bump both; additive bumps advance only [`UMST_FFI_ABI_VERSION`].
pub const UMST_FFI_ABI_VERSION_MIN_COMPATIBLE: u32 = 7;

// ---------------------------------------------------------------------------
// Opaque handle management
// ---------------------------------------------------------------------------

/// Allocate a new ThermodynamicFilter on the heap and return an opaque pointer.
/// The caller owns this pointer and must free it with `umst_filter_free`.
#[no_mangle]
pub extern "C" fn umst_filter_new() -> *mut ThermodynamicFilter {
    Box::into_raw(Box::new(ThermodynamicFilter::new()))
}

/// Free a ThermodynamicFilter previously allocated by `umst_filter_new`.
///
/// # Safety
/// `ptr` must be a valid pointer returned by `umst_filter_new` and must not
/// have been freed already.
#[no_mangle]
pub unsafe extern "C" fn umst_filter_free(ptr: *mut ThermodynamicFilter) {
    if !ptr.is_null() {
        drop(Box::from_raw(ptr));
    }
}

// ---------------------------------------------------------------------------
// Gate check — the core admissibility decision
// ---------------------------------------------------------------------------

/// Check whether a state transition (old → new) is thermodynamically admissible.
///
/// This is the primary entry point.  It evaluates all four invariants:
///   1. Mass conservation:       |rho_new - rho_old| < 100
///   2. Clausius-Duhem:          D_int = -rho * psi_dot >= -eps
///   3. Hydration irreversibility (implied by positive dissipation)
///   4. Strength monotonicity:   fc_new >= fc_old - eps
///
/// Returns 1 if admissible, 0 if rejected.
///
/// # Safety
/// `filter_ptr` must be a valid pointer from `umst_filter_new`.
#[no_mangle]
pub unsafe extern "C" fn umst_gate_check(
    filter_ptr: *mut ThermodynamicFilter,
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
    let filter = &mut *filter_ptr;

    // Fields not exposed through C ABI (temperature, entropy) are set to
    // the standard isothermal reference values used throughout the kernel.
    // The four invariants do not depend on temperature or entropy under
    // the isothermal simplification (sigma:eps_dot = 0, nabla_T = 0).
    let old_state = ThermodynamicState {
        density: old_density,
        temperature: 293.0,        // 20 C reference (isothermal assumption)
        free_energy: old_free_energy,
        entropy: old_hydration * 0.1, // simplified; not used by gate
        hydration_degree: old_hydration,
        strength: old_strength,
    };

    let new_state = ThermodynamicState {
        density: new_density,
        temperature: 293.0,
        free_energy: new_free_energy,
        entropy: new_hydration * 0.1,
        hydration_degree: new_hydration,
        strength: new_strength,
    };

    // Keep Rust-side transition accounting up to date.
    let _ = filter.check_transition(&old_state, &new_state, dt);

    // Return the explicit thermodynamic gate decision documented for this C ABI.
    let mass_conserved = (new_density - old_density).abs() < 100.0;
    let rho = (old_density + new_density) / 2.0;
    let psi_dot = (new_free_energy - old_free_energy) / (dt + 1e-10);
    let d_int = -rho * psi_dot;
    let strength_monotonic = new_strength >= old_strength - 1e-6;
    let hydration_irreversible = new_hydration >= old_hydration - 1e-6;
    let strength_bounded = new_strength <= new_max_strength;
    let accepted = mass_conserved
        && d_int >= -1e-6
        && strength_monotonic
        && hydration_irreversible
        && strength_bounded;
    if accepted { 1 } else { 0 }
}

// ---------------------------------------------------------------------------
// Dissipation value — for quantitative checks
// ---------------------------------------------------------------------------

/// Compute the internal dissipation D_int for a state transition.
///
/// D_int = -rho * (psi_new - psi_old) / dt
///
/// Positive values indicate thermodynamically admissible forward evolution.
/// Negative values indicate a 2nd-law violation (reverse hydration).
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
// Hydration degree — Avrami-Parrott model
// ---------------------------------------------------------------------------

/// Compute the degree of hydration alpha(t) using the Avrami-Parrott model.
///
/// alpha(t) = alpha_max * (1 - exp(-k * sqrt(t)))
///
/// This function wraps `StrengthEngine::compute_hydration_degree` from
/// umst-core without modification.
#[no_mangle]
pub extern "C" fn umst_hydration_degree(
    age_days: f32,
    temp_c: f32,
    scm_ratio: f32,
) -> f32 {
    umst_core::physics_kernel::PhysicsKernel::compute_hydration_degree(
        age_days, temp_c, scm_ratio,
    )
}

// ---------------------------------------------------------------------------
// Strength — Powers gel-space ratio model
// ---------------------------------------------------------------------------

/// Compute compressive strength using Powers' gel-space ratio model.
///
/// fc = S_intrinsic * x^3
/// where x = 0.68 * alpha / (0.32 * alpha + w/c)
///
/// This function wraps `StrengthEngine::compute_powers` from umst-core.
#[no_mangle]
pub extern "C" fn umst_strength_powers(
    wc_ratio: f32,
    degree_hydration: f32,
    air_content: f32,
    intrinsic_strength: f32,
) -> f32 {
    umst_core::science::strength::StrengthEngine::compute_powers(
        wc_ratio,
        degree_hydration,
        air_content,
        intrinsic_strength,
    )
    .compressive_strength
}

// ---------------------------------------------------------------------------
// Convenience: construct ThermodynamicState from mix parameters
// ---------------------------------------------------------------------------

/// Construct a ThermodynamicState from mix parameters and return its fields
/// packed into a C-compatible struct.
///
/// Uses the Powers model internally:
///   psi(alpha) = -Q_hyd * alpha   (Q_hyd = 450 J/kg)
///   fc = S_int * (0.68*alpha / (0.32*alpha + w/c))^3
///
/// `max_strength` is the intrinsic gel strength cap used by `from_mix` (default 240 MPa).
#[repr(C)]
pub struct CThermodynamicState {
    pub density: f64,
    pub free_energy: f64,
    pub hydration_degree: f64,
    pub strength: f64,
    pub max_strength: f64,
}

#[no_mangle]
pub extern "C" fn umst_thermo_state_from_mix(
    w_c: f64,
    alpha: f64,
    temp: f64,
) -> CThermodynamicState {
    let state = ThermodynamicState::from_mix(w_c, alpha, temp);
    CThermodynamicState {
        density: state.density,
        free_energy: state.free_energy,
        hydration_degree: state.hydration_degree,
        strength: state.strength,
        max_strength: 240.0,
    }
}

/// Pointer-based variant of `umst_thermo_state_from_mix` for Haskell FFI.
///
/// Haskell's FFI cannot portably receive C structs by value across all
/// platforms.  This wrapper writes the result through an out-pointer,
/// which Haskell handles via `Storable` + `alloca`.
///
/// # Safety
/// `out` must point to a valid, aligned `CThermodynamicState`.
#[no_mangle]
pub unsafe extern "C" fn umst_thermo_state_from_mix_ptr(
    w_c: f64,
    alpha: f64,
    temp: f64,
    out: *mut CThermodynamicState,
) {
    *out = umst_thermo_state_from_mix(w_c, alpha, temp);
}

// ---------------------------------------------------------------------------
// Credit aggregate (Phase M4) — pure scalar sum over admissible weights
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
// Dignity step (Phase N3-FPD-a) — mirrors `UMST.Formal.Dignity.dignity_step`
// ---------------------------------------------------------------------------

const DIGNITY_D_MAX: f64 = 10.0;
const DIGNITY_K_B: f64 = 1.380_649e-23;

#[inline]
fn landauer_joules_per_bit_dignity(temperature_k: f64) -> f64 {
    DIGNITY_K_B * temperature_k.max(0.0) * std::f64::consts::LN_2
}

/// One Landauer-gated dignity update on the legacy `[0, 10]` scale (egoff `dignity_scalar` band).
///
/// When `k_B T ln 2 * ΔMI ≤ ΔE`, returns `min(10, current + ΔMI)`; otherwise returns `current`.
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
// η_cog (Phase N3-FPD-b) — mirrors `UMST.Formal.EtaCog.eta_cog`
// ---------------------------------------------------------------------------

/// Dignity-weighted MI-per-Joule: `dignity * ΔMI / (ΔE + k_B T ln 2)`.
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
// ρ-based Gaussian MI in bits (Phase FPD-RhoEstimator) — `umst_math::rho_estimator`
// ---------------------------------------------------------------------------

/// Gaussian bivariate MI in bits from Pearson ρ, with |ρ| clamped for numerical stability.
///
/// Proof chain: `UMST.Formal.RhoEstimator::rho_based_mi_formula` (Lean); implementation `umst_math::rho_estimator::rho_mi_bits`.
#[must_use]
#[no_mangle]
pub extern "C" fn umst_rho_mi_bits(rho: f64) -> f64 {
    umst_math::rho_estimator::rho_mi_bits(rho)
}

// ---------------------------------------------------------------------------
// Median convergence warmup (Phase FPD-MedianConvergence) — `umst_math::median_convergence`
// ---------------------------------------------------------------------------

/// Theorem-derived median warmup count `⌈(2/(ε²ρ_min²))·ln(2/δ)⌉` (natural log), as `u64`.
///
/// Proof chain: `UMST.Formal.MedianConvergence::median_convergence_sample_size` (Lean); implementation `umst_math::median_convergence::n_warmup`.
#[must_use]
#[no_mangle]
pub extern "C" fn umst_n_warmup(epsilon: f64, delta: f64, rho_min: f64) -> u64 {
    umst_math::median_convergence::n_warmup(epsilon, delta, rho_min)
}

/// Theorem-derived order-statistics sample count (same closed form as [`umst_n_warmup`]; `q` validated in `(0,1)`).
///
/// Proof chain: `UMST.Formal.OrderStatisticsBand::order_statistic_concentration` (envelope); implementation `umst_math::order_statistics_band::n_quantile`.
#[must_use]
#[no_mangle]
pub extern "C" fn umst_n_quantile(epsilon: f64, delta: f64, rho_min: f64, q: f64) -> u64 {
    umst_math::order_statistics_band::n_quantile(epsilon, delta, rho_min, q).unwrap_or(0)
}

/// Runtime ABI tag from the loaded `libumst_ffi` (must be `>=` `umst_ffi_abi_version_expected()` on the same build).
#[must_use]
#[no_mangle]
pub extern "C" fn umst_ffi_abi_version() -> u32 {
    UMST_FFI_ABI_VERSION
}

/// Minimum ABI level this `libumst_ffi` advertises; consumers assert `umst_ffi_abi_version() >=` this (same `.so`).
#[must_use]
#[no_mangle]
pub extern "C" fn umst_ffi_abi_version_expected() -> u32 {
    UMST_FFI_ABI_VERSION_MIN_COMPATIBLE
}
