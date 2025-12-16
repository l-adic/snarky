//! Pasta curves (Pallas and Vesta) with conditional backend support
//!
//! This module provides a unified API for Pasta curves that works with either:
//! - arkworks curves (ark-pallas, ark-vesta) - default
//! - mina-curves (from proof-systems)
//!
//! The implementation is identical regardless of backend - only the underlying
//! types change based on feature flags.

pub mod pallas;
pub mod types;
pub mod vesta;

// Re-export only the NAPI functions, not the type aliases
// Pallas functions
pub use pallas::scalar_field::{
    pallas_scalarfield_add, pallas_scalarfield_div, pallas_scalarfield_eq,
    pallas_scalarfield_from_bigint, pallas_scalarfield_from_string, pallas_scalarfield_invert,
    pallas_scalarfield_modulus, pallas_scalarfield_mul, pallas_scalarfield_one,
    pallas_scalarfield_pow, pallas_scalarfield_rand, pallas_scalarfield_sub,
    pallas_scalarfield_to_bigint, pallas_scalarfield_to_string, pallas_scalarfield_zero,
};

// Note: Pallas base field functions removed - handled via Vesta scalar field cross-wiring

pub use pallas::group::{
    pallas_group_add, pallas_group_eq, pallas_group_identity, pallas_group_neg, pallas_group_rand,
    pallas_group_scale, pallas_group_to_affine, pallas_group_to_string, pallas_group_weierstrass_a,
    pallas_group_weierstrass_b,
};

// Vesta functions
pub use vesta::scalar_field::{
    vesta_scalarfield_add, vesta_scalarfield_div, vesta_scalarfield_eq,
    vesta_scalarfield_from_bigint, vesta_scalarfield_from_string, vesta_scalarfield_invert,
    vesta_scalarfield_modulus, vesta_scalarfield_mul, vesta_scalarfield_one, vesta_scalarfield_pow,
    vesta_scalarfield_rand, vesta_scalarfield_sub, vesta_scalarfield_to_bigint,
    vesta_scalarfield_to_string, vesta_scalarfield_zero,
};

// Note: Vesta base field functions removed - handled via Pallas scalar field cross-wiring

pub use vesta::group::{
    vesta_group_add, vesta_group_eq, vesta_group_identity, vesta_group_neg, vesta_group_rand,
    vesta_group_scale, vesta_group_to_affine, vesta_group_to_string, vesta_group_weierstrass_a,
    vesta_group_weierstrass_b,
};
