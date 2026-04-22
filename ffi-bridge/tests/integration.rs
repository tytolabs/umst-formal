// integration.rs — Black-box tests for the umst-ffi-bridge C ABI
//
// These tests call the same functions that Haskell and OCaml consumers use,
// treating the FFI surface as the public contract.  They complement the
// formal proofs (Agda, Coq) by exercising the *Rust implementation* against
// the four invariants.
//
// Run with:
//   cargo test --release -p umst-ffi-bridge
//
// The tests are named after the four invariants they primarily exercise:
//   test_inv1_mass_conservation
//   test_inv2_clausius_duhem
//   test_inv3_hydration_irreversibility
//   test_inv4_strength_monotonicity

use umst_ffi::*;

// ── helpers ──────────────────────────────────────────────────────────────────

/// Allocate a filter, run `f`, then free the filter.
/// Mirrors the Haskell `bracket (umstFilterNew) (umstFilterFree)` pattern.
unsafe fn with_filter<F: FnOnce(*mut std::ffi::c_void)>(f: F) {
    let ptr = umst_filter_new() as *mut std::ffi::c_void;
    assert!(!ptr.is_null(), "umst_filter_new returned null");
    f(ptr);
    umst_filter_free(ptr as *mut _);
}

// ── Invariant 1: Mass conservation ───────────────────────────────────────────

#[test]
fn test_inv1_mass_conservation_accepted() {
    // A density jump of 50 kg/m³ is within the δ = 100 kg/m³ tolerance.
    unsafe {
        with_filter(|ptr| {
            let result = umst_gate_check(
                ptr as *mut _,
                2000.0, -225.0, 0.5, 20.0,   // old: rho, psi, alpha, fc
                2050.0, -315.0, 0.7, 30.0,   // new: rho, psi, alpha, fc
                100.0,                         // new max_strength
                3600.0,                        // dt = 1 hour
            );
            assert_eq!(result, 1, "50 kg/m³ density change should be accepted");
        });
    }
}

#[test]
fn test_inv1_mass_conservation_rejected() {
    // A density jump of 200 kg/m³ violates mass conservation.
    unsafe {
        with_filter(|ptr| {
            let result = umst_gate_check(
                ptr as *mut _,
                2000.0, -225.0, 0.5, 20.0,
                2200.0, -225.0, 0.5, 20.0,   // only density changes (unrealistic)
                150.0,
                3600.0,
            );
            assert_eq!(result, 0, "200 kg/m³ density jump should be rejected");
        });
    }
}

// ── Invariant 2: Clausius-Duhem ───────────────────────────────────────────────

#[test]
fn test_inv2_forward_dissipation_nonneg() {
    // Forward hydration: ψ decreases → D_int = −ρ·ψ̇ > 0.
    let d_int = umst_dissipation(2000.0, 2000.0, -225.0, -315.0, 3600.0);
    assert!(
        d_int >= 0.0,
        "D_int must be non-negative for forward hydration, got {d_int}"
    );
}

#[test]
fn test_inv2_reverse_dissipation_neg() {
    // Reverse hydration: ψ increases → D_int < 0 (2nd-law violation).
    let d_int = umst_dissipation(2000.0, 2000.0, -315.0, -225.0, 3600.0);
    assert!(
        d_int < 0.0,
        "D_int must be negative for reverse hydration, got {d_int}"
    );
}

#[test]
fn test_inv2_energy_violation_rejected() {
    // Spontaneous free-energy increase: gate must reject.
    unsafe {
        with_filter(|ptr| {
            let result = umst_gate_check(
                ptr as *mut _,
                2000.0, -315.0, 0.7, 30.0,   // old: ψ = -315
                2000.0, -200.0, 0.7, 30.0,   // new: ψ = -200 > old (illegal)
                150.0,
                3600.0,
            );
            assert_eq!(result, 0, "Free-energy increase should be rejected");
        });
    }
}

// ── Invariant 3: Hydration irreversibility ────────────────────────────────────

#[test]
fn test_inv3_forward_hydration_accepted() {
    // α: 0.5 → 0.7 is forward; all other invariants also hold.
    unsafe {
        with_filter(|ptr| {
            let result = umst_gate_check(
                ptr as *mut _,
                2000.0, -225.0, 0.5, 20.0,
                2000.0, -315.0, 0.7, 30.0,
                150.0,
                3600.0,
            );
            assert_eq!(result, 1, "Forward hydration (α: 0.5→0.7) should be accepted");
        });
    }
}

#[test]
fn test_inv3_reverse_hydration_rejected() {
    // α: 0.7 → 0.5 is reverse; gate must reject.
    unsafe {
        with_filter(|ptr| {
            let result = umst_gate_check(
                ptr as *mut _,
                2000.0, -315.0, 0.7, 30.0,
                2000.0, -225.0, 0.5, 20.0,   // alpha decreases
                150.0,
                3600.0,
            );
            assert_eq!(result, 0, "Reverse hydration (α: 0.7→0.5) should be rejected");
        });
    }
}

// ── Invariant 4: Strength monotonicity ───────────────────────────────────────

#[test]
fn test_inv4_strength_increases_accepted() {
    unsafe {
        with_filter(|ptr| {
            let result = umst_gate_check(
                ptr as *mut _,
                2000.0, -225.0, 0.5, 20.0,
                2000.0, -315.0, 0.7, 35.0,   // strength 20 → 35 MPa ✓
                150.0,
                3600.0,
            );
            assert_eq!(result, 1, "Strength increase should be accepted");
        });
    }
}

// ── Theorem 1 round-trip: from_mix → gate_check ──────────────────────────────

#[test]
fn test_theorem1_from_mix_forward() {
    // Construct two states from mix parameters (w/c = 0.45):
    //   old: alpha = 0.40 (early hydration)
    //   new: alpha = 0.60 (further along)
    // The gate must accept the transition.
    unsafe {
        let mut old_state = CThermodynamicState {
            density: 0.0,
            free_energy: 0.0,
            hydration_degree: 0.0,
            strength: 0.0,
            max_strength: 0.0,
        };
        let mut new_state = CThermodynamicState {
            density: 0.0,
            free_energy: 0.0,
            hydration_degree: 0.0,
            strength: 0.0,
            max_strength: 0.0,
        };

        umst_thermo_state_from_mix_ptr(0.45, 0.40, 20.0, &mut old_state);
        umst_thermo_state_from_mix_ptr(0.45, 0.60, 20.0, &mut new_state);

        // Physical sanity checks
        assert!(
            new_state.hydration_degree > old_state.hydration_degree,
            "Hydration must increase: {} → {}",
            old_state.hydration_degree,
            new_state.hydration_degree
        );
        assert!(
            new_state.free_energy <= old_state.free_energy,
            "Free energy must decrease for forward hydration: {} → {}",
            old_state.free_energy,
            new_state.free_energy
        );
        assert!(
            new_state.strength >= old_state.strength,
            "Strength must increase: {} → {}",
            old_state.strength,
            new_state.strength
        );

        with_filter(|ptr| {
            let result = umst_gate_check(
                ptr as *mut _,
                old_state.density,    old_state.free_energy,
                old_state.hydration_degree, old_state.strength,
                new_state.density,    new_state.free_energy,
                new_state.hydration_degree, new_state.strength,
                new_state.max_strength,
                3600.0,
            );
            assert_eq!(
                result, 1,
                "Theorem 1 violated: from_mix forward hydration rejected"
            );
        });
    }
}

// ── Identity transition ───────────────────────────────────────────────────────

#[test]
fn test_identity_always_accepted() {
    unsafe {
        with_filter(|ptr| {
            let result = umst_gate_check(
                ptr as *mut _,
                2000.0, -315.0, 0.7, 30.0,
                2000.0, -315.0, 0.7, 30.0,   // identical
                150.0,
                3600.0,
            );
            assert_eq!(result, 1, "Identity transition must always be accepted");
        });
    }
}

// ── Dissipation function ──────────────────────────────────────────────────────

#[test]
fn test_dissipation_zero_dt_guard() {
    // dt = 0 must not cause divide-by-zero or NaN.
    let d = umst_dissipation(2000.0, 2000.0, -225.0, -315.0, 0.0);
    assert!(d.is_finite(), "D_int must be finite for dt=0 (guard is dt+1e-10)");
    assert!(d >= 0.0, "D_int must be non-negative for forward hydration even at dt=0");
}

#[test]
fn test_hydration_degree_monotone_with_age() {
    // Older paste has higher hydration degree.
    let alpha_7d  = umst_hydration_degree(7.0,  20.0, 0.0);
    let alpha_28d = umst_hydration_degree(28.0, 20.0, 0.0);
    assert!(
        alpha_28d >= alpha_7d,
        "Hydration degree must be monotone with age: α(7d)={alpha_7d}, α(28d)={alpha_28d}"
    );
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
fn test_strength_powers_monotone_with_hydration() {
    // Higher hydration → higher strength (Powers model).
    let fc_low  = umst_strength_powers(0.45, 0.40, 0.02, 234.0);
    let fc_high = umst_strength_powers(0.45, 0.70, 0.02, 234.0);
    assert!(
        fc_high >= fc_low,
        "Powers strength must be monotone with α: fc(0.40)={fc_low}, fc(0.70)={fc_high}"
    );
}
