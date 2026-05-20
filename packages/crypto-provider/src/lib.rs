//! Unified crypto-provider: NAPI bindings for the Pasta-curve Kimchi
//! proof system. Used by the PureScript snarky library.
//!
//! Coverage:
//! - **Pasta curves** (Pallas, Vesta): field arithmetic and group operations
//! - **Poseidon** (Kimchi-compatible parameters)
//! - **Kimchi** gate verification helpers (used by the circuit-diff test suite)
//!
//! # Architecture
//!
//! ```text
//! PureScript (Snarky.Curves.Pasta) → FFI → crypto-provider (Rust/NAPI)
//! ```
//!
//! Field elements and group points are passed as opaque `External<T>` handles
//! that JavaScript/PureScript cannot inspect directly.

// ============================================================================
// CURVES MODULE
// Field arithmetic and elliptic curve group operations.
// ============================================================================

/// BigInt conversion utilities between NAPI, num-bigint, and arkworks.
mod bigint;

/// Pasta curves (Pallas and Vesta) - used for recursive SNARKs in Mina.
pub mod pasta;

// Re-export pasta functions for backward compatibility
pub use pasta::*;

// ============================================================================
// KIMCHI MODULE
// Poseidon hashing with Kimchi-compatible parameters, plus gate verification
// functions for testing circuit implementations against reference code.
// ============================================================================

/// Kimchi-specific functionality: Poseidon hash, gate verification, linearization.
pub mod kimchi;

pub use kimchi::poseidon::{
    pallas::{
        pallas_domain_prefix_to_field, pallas_init_with_domain, pallas_poseidon_apply_mds,
        pallas_poseidon_full_round, pallas_poseidon_get_mds_matrix, pallas_poseidon_get_num_rounds,
        pallas_poseidon_get_round_constants, pallas_poseidon_hash, pallas_poseidon_permute,
        pallas_poseidon_sbox, pallas_sponge_absorb, pallas_sponge_create, pallas_sponge_squeeze,
    },
    vesta::{
        vesta_domain_prefix_to_field, vesta_init_with_domain, vesta_poseidon_apply_mds,
        vesta_poseidon_full_round, vesta_poseidon_get_mds_matrix, vesta_poseidon_get_num_rounds,
        vesta_poseidon_get_round_constants, vesta_poseidon_hash, vesta_poseidon_permute,
        vesta_poseidon_sbox, vesta_sponge_absorb, vesta_sponge_create, vesta_sponge_squeeze,
    },
};

pub use kimchi::verify::{
    verify_pallas_complete_add, verify_pallas_generic, verify_pallas_poseidon_gadget,
    verify_pallas_varbasemul, verify_vesta_complete_add, verify_vesta_generic,
    verify_vesta_poseidon_gadget, verify_vesta_varbasemul,
};

pub use kimchi::test_linearization::{evaluate_pallas_linearization, evaluate_vesta_linearization};
