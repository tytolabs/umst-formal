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
        max_strength: 150.0,       // conservative upper bound
    };

    let new_state = ThermodynamicState {
        density: new_density,
        temperature: 293.0,
        free_energy: new_free_energy,
        entropy: new_hydration * 0.1,
        hydration_degree: new_hydration,
        strength: new_strength,
        max_strength: new_max_strength,
    };

    let result = filter.check_transition(&old_state, &new_state, dt);
    if result.is_admissible() { 1 } else { 0 }
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
        max_strength: state.max_strength,
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
