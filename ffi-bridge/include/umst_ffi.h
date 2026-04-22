/* SPDX-License-Identifier: MIT
 *
 * umst_ffi.h — C header for the UMST thermodynamic gate FFI bridge
 *
 * This header declares the C-ABI surface exposed by libumst_ffi.
 *
 * ABI **8** (2026-04-21): added `umst_ffi_abi_version_expected` + `UMST_FFI_ABI_VERSION_MIN_COMPATIBLE` (Phase N-abi-version-gate; additive load-time check symbols).
 * ABI **7** (2026-04-19): added `umst_n_quantile` (order-statistics band budget; Phase FPD-OrderStatisticsBand).
 * ABI **6** (2026-04-19): added `umst_n_warmup` (median-convergence warmup count, Phase FPD-MedianConvergence).
 * ABI **5** (2026-04-21): added `umst_rho_mi_bits` (Gaussian ρ-MI in bits, Phase FPD-RhoEstimator).
 * It is consumed by:
 *   - Haskell via `foreign import ccall`
 *   - OCaml via Ctypes
 *   - Any C/C++ test harness
 *
 * The four core functions map directly to the four invariants proved
 * in the Agda and Coq layers of umst-formal.
 */

#ifndef UMST_FFI_H
#define UMST_FFI_H

#include <stddef.h>
#include <stdint.h>

/*
 * C preprocessor mirrors (must match `umst-formal/ffi-bridge` and `umst-ffi` crate constants).
 * External callers must assert `umst_ffi_abi_version() >= umst_ffi_abi_version_expected()`
 * before any other FFI entry point. Breaking ABI changes bump both the current and min-compatible
 * values; additive entry points bump only the current ABI tag.
 */
#define UMST_FFI_ABI_VERSION 8u
#define UMST_FFI_ABI_VERSION_MIN_COMPATIBLE 7u

#ifdef __cplusplus
extern "C" {
#endif

/* -----------------------------------------------------------------------
 * Opaque handle for the ThermodynamicFilter
 * ----------------------------------------------------------------------- */

typedef void* UmstFilter;

UmstFilter umst_filter_new(void);
void       umst_filter_free(UmstFilter ptr);

/* -----------------------------------------------------------------------
 * Gate check — returns 1 if admissible, 0 if rejected
 * ----------------------------------------------------------------------- */

int32_t umst_gate_check(
    UmstFilter filter,
    double old_density,
    double old_free_energy,
    double old_hydration,
    double old_strength,
    double new_density,
    double new_free_energy,
    double new_hydration,
    double new_strength,
    double new_max_strength,
    double dt
);

/* -----------------------------------------------------------------------
 * Dissipation: D_int = -rho * psi_dot
 * ----------------------------------------------------------------------- */

double umst_dissipation(
    double old_density,
    double new_density,
    double old_free_energy,
    double new_free_energy,
    double dt
);

/* -----------------------------------------------------------------------
 * Hydration degree: Avrami-Parrott model
 * ----------------------------------------------------------------------- */

float umst_hydration_degree(
    float age_days,
    float temp_c,
    float scm_ratio
);

/* -----------------------------------------------------------------------
 * Strength: Powers gel-space ratio model
 * ----------------------------------------------------------------------- */

float umst_strength_powers(
    float wc_ratio,
    float degree_hydration,
    float air_content,
    float intrinsic_strength
);

/* -----------------------------------------------------------------------
 * State construction from mix parameters
 * ----------------------------------------------------------------------- */

typedef struct {
    double density;
    double free_energy;
    double hydration_degree;
    double strength;
    double max_strength;
} CThermodynamicState;

CThermodynamicState umst_thermo_state_from_mix(
    double w_c,
    double alpha,
    double temp
);

/* Pointer-based variant for Haskell FFI (struct returned via out-pointer) */
void umst_thermo_state_from_mix_ptr(
    double w_c,
    double alpha,
    double temp,
    CThermodynamicState* out
);

/* -----------------------------------------------------------------------
 * Credit aggregate (Phase M4): sum weights with nonzero admissible byte
 * ----------------------------------------------------------------------- */

double umst_credit_greedy_sum(
    size_t n,
    const double* weights,
    const unsigned char* admissible
);

/* -----------------------------------------------------------------------
 * Dignity step (Phase N3-FPD-a): Landauer-gated MI increment on [0,10] scale
 * ----------------------------------------------------------------------- */

double umst_dignity_step(
    double temperature_k,
    double current_dignity,
    double delta_mi_bits,
    double delta_energy_j
);

/* -----------------------------------------------------------------------
 * η_cog (Phase N3-FPD-b): dignity-weighted MI per Joule (Landauer-floored denom)
 * ----------------------------------------------------------------------- */

double umst_eta_cog(
    double temperature_k,
    double dignity_value,
    double delta_mi_bits,
    double delta_energy_j
);

/* -----------------------------------------------------------------------
 * ρ-MI bits (Phase FPD-RhoEstimator): Gaussian MI = −½ log₂(1−ρ²)
 * ----------------------------------------------------------------------- */

double umst_rho_mi_bits(double rho);

/* -----------------------------------------------------------------------
 * Median warmup count (Phase FPD-MedianConvergence): N_warmup = ceil((2/(ε²ρ_min²))·ln(2/δ))
 * ----------------------------------------------------------------------- */

uint64_t umst_n_warmup(double epsilon, double delta, double rho_min);

/* -----------------------------------------------------------------------
 * Order-statistics quantile budget (Phase FPD-OrderStatisticsBand): same numeric kernel as N_warmup
 * ----------------------------------------------------------------------- */

uint64_t umst_n_quantile(double epsilon, double delta, double rho_min, double q);

/* -----------------------------------------------------------------------
 * ABI tags — must match `umst-ffi` / ffi-bridge (load-time drift guard).
 * ----------------------------------------------------------------------- */

uint32_t umst_ffi_abi_version(void);

/** Minimum ABI level this `libumst_ffi` build supports; assert `umst_ffi_abi_version() >=` this first. */
uint32_t umst_ffi_abi_version_expected(void);

#ifdef __cplusplus
}
#endif

#endif /* UMST_FFI_H */
