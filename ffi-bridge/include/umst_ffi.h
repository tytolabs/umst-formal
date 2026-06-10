/* SPDX-License-Identifier: MIT
 *
 * umst_ffi.h — C header for the material-agnostic UMST thermodynamic gate FFI
 *
 * Cement chemistry (hydration, Powers, from_mix) moved to umst_concrete_ffi.h.
 *
 * ABI **9** (2026-06-10): pure `umst_gate_check` (no filter handle); cement symbols removed.
 * ABI **8** (2026-04-21): `umst_ffi_abi_version_expected` + min-compatible gate.
 */

#ifndef UMST_FFI_H
#define UMST_FFI_H

#include <stddef.h>
#include <stdint.h>

#define UMST_FFI_ABI_VERSION 9u
#define UMST_FFI_ABI_VERSION_MIN_COMPATIBLE 9u

#ifdef __cplusplus
extern "C" {
#endif

/* Gate check — returns 1 if admissible, 0 if rejected (pure; no filter handle). */
int32_t umst_gate_check(
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

double umst_dissipation(
    double old_density,
    double new_density,
    double old_free_energy,
    double new_free_energy,
    double dt
);

double umst_credit_greedy_sum(
    size_t n,
    const double* weights,
    const unsigned char* admissible
);

double umst_dignity_step(
    double temperature_k,
    double current_dignity,
    double delta_mi_bits,
    double delta_energy_j
);

double umst_eta_cog(
    double temperature_k,
    double dignity_value,
    double delta_mi_bits,
    double delta_energy_j
);

double umst_rho_mi_bits(double rho);

uint64_t umst_n_warmup(double epsilon, double delta, double rho_min);

uint64_t umst_n_quantile(double epsilon, double delta, double rho_min, double q);

uint32_t umst_ffi_abi_version(void);

uint32_t umst_ffi_abi_version_expected(void);

#ifdef __cplusplus
}
#endif

#endif /* UMST_FFI_H */
