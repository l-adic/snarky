// Kimchi functionality - Poseidon gates and Mina proof-system integration
//
// This module provides Poseidon hash function operations that match the
// Mina Kimchi proof system exactly, enabling verification that PureScript
// circuits satisfy the Rust Kimchi gate equations.

pub mod poseidon;

pub mod verify;

pub use poseidon::*;
pub use verify::*;
