// Kimchi functionality - Poseidon gates and Mina proof-system integration
//
// This module provides Poseidon hash function operations that match the
// Mina Kimchi proof system exactly, enabling verification that PureScript
// circuits satisfy the Rust Kimchi gate equations.

pub mod circuit;
pub mod domain;
pub mod poseidon;
pub mod test_linearization;
pub mod verify;

pub use circuit::*;
pub use domain::*;
pub use poseidon::*;
pub use test_linearization::*;
pub use verify::*;
