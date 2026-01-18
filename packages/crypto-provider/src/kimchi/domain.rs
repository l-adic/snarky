// Domain-related polynomial evaluation functions for Kimchi linearization.
//
// These functions compute values that depend on the evaluation domain and
// evaluation point (zeta), used in the linearization polynomial evaluation.

use ark_ff::FftField;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use napi::bindgen_prelude::*;
use napi_derive::napi;

// Note on naming: Fp = Pallas base field = Vesta scalar field
//                 Fq = Pallas scalar field = Vesta base field
// The External types follow the same pattern as linearization.rs
use crate::pasta::pallas::scalar_field::FieldExternal as FqExternal; // External<Fq>
use crate::pasta::vesta::scalar_field::FieldExternal as FpExternal; // External<Fp>

/// Compute the unnormalized Lagrange basis polynomial evaluated at a point.
///
/// This computes: (pt^n - 1) / (pt - ω^i)
///
/// Where:
/// - n is the domain size (2^domain_log2)
/// - ω is the domain generator
/// - i is the offset (possibly adjusted by zk_rows if zk_rows is true)
///
/// The `zk_rows` flag indicates whether to offset the index by the number of
/// zero-knowledge rows (which shifts the index into the "padding" region).
fn unnormalized_lagrange_basis<F: FftField>(
    domain_log2: u32,
    zk_rows: bool,
    offset: i32,
    pt: F,
) -> F {
    let domain = Radix2EvaluationDomain::<F>::new(1 << domain_log2).expect("Invalid domain size");

    // Compute the actual index, accounting for zk_rows if needed
    // When zk_rows is true, we're computing a Lagrange basis that accounts for
    // the zero-knowledge rows at the end of the domain
    let actual_offset = if zk_rows {
        // Typically zk_rows = 3 in Kimchi, offset into the ZK region
        let zk_rows_count = 3i32; // Standard Kimchi ZK rows
        (domain.size() as i32) - zk_rows_count + offset
    } else {
        offset
    };

    // Handle negative indices by wrapping around
    let omega_i = if actual_offset < 0 {
        domain
            .group_gen
            .pow([(-actual_offset) as u64])
            .inverse()
            .expect("Group generator should be invertible")
    } else {
        domain.group_gen.pow([actual_offset as u64])
    };

    // Compute (pt^n - 1) / (pt - ω^i)
    domain.evaluate_vanishing_polynomial(pt) / (pt - omega_i)
}

/// Compute the polynomial that vanishes on the last n rows of the domain.
///
/// This computes: ∏_{j=0}^{n-1} (pt - ω^(size - n + j))
///
/// For `VanishesOnZeroKnowledgeAndPreviousRows`, n = zk_rows + 1.
fn eval_vanishes_on_last_n_rows<F: FftField>(domain_log2: u32, n: u64, pt: F) -> F {
    if n == 0 {
        return F::one();
    }

    let domain = Radix2EvaluationDomain::<F>::new(1 << domain_log2).expect("Invalid domain size");

    let size = domain.size() as u64;
    let mut term = domain.group_gen.pow([size - n]);
    let mut acc = pt - term;
    for _ in 0..n - 1 {
        term *= domain.group_gen;
        acc *= pt - term;
    }
    acc
}

// ============================================================================
// PALLAS (Fp = VestaScalarField = PallasBaseField) FFI
// ============================================================================

/// Compute unnormalized Lagrange basis for Pallas base field (Fp).
///
/// Used in linearization evaluation for Pallas-based circuits.
#[napi]
pub fn pallas_unnormalized_lagrange_basis(
    domain_log2: u32,
    zk_rows: bool,
    offset: i32,
    pt: &FpExternal,
) -> FpExternal {
    let result = unnormalized_lagrange_basis(domain_log2, zk_rows, offset, **pt);
    External::new(result)
}

/// Compute the polynomial that vanishes on zero-knowledge and previous rows for Pallas.
///
/// This is `eval_vanishes_on_last_n_rows` with n = zk_rows + 1.
/// Standard Kimchi uses zk_rows = 3, so this vanishes on the last 4 rows.
#[napi]
pub fn pallas_vanishes_on_zk_and_previous_rows(
    domain_log2: u32,
    zk_rows: u32,
    pt: &FpExternal,
) -> FpExternal {
    // Type inferred from pt
    let result = eval_vanishes_on_last_n_rows(domain_log2, (zk_rows + 1) as u64, **pt);
    External::new(result)
}

// ============================================================================
// VESTA (Fq = PallasScalarField = VestaBaseField) FFI
// ============================================================================

/// Compute unnormalized Lagrange basis for Vesta base field (Fq).
///
/// Used in linearization evaluation for Vesta-based circuits.
#[napi]
pub fn vesta_unnormalized_lagrange_basis(
    domain_log2: u32,
    zk_rows: bool,
    offset: i32,
    pt: &FqExternal,
) -> FqExternal {
    let result = unnormalized_lagrange_basis(domain_log2, zk_rows, offset, **pt);
    External::new(result)
}

/// Compute the polynomial that vanishes on zero-knowledge and previous rows for Vesta.
///
/// This is `eval_vanishes_on_last_n_rows` with n = zk_rows + 1.
/// Standard Kimchi uses zk_rows = 3, so this vanishes on the last 4 rows.
#[napi]
pub fn vesta_vanishes_on_zk_and_previous_rows(
    domain_log2: u32,
    zk_rows: u32,
    pt: &FqExternal,
) -> FqExternal {
    // Type inferred from pt
    let result = eval_vanishes_on_last_n_rows(domain_log2, (zk_rows + 1) as u64, **pt);
    External::new(result)
}
