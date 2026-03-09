/* SPDX-License-Identifier: MIT
 *
 * umst_ffi.h — C header for the UMST thermodynamic gate FFI bridge
 *
 * This header declares the C-ABI surface exposed by libumst_ffi.
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

#include <stdint.h>

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

#ifdef __cplusplus
}
#endif

#endif /* UMST_FFI_H */
