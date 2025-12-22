// Test utilities for validating circuit constraints against Kimchi gate implementations
//
// This module provides functions to verify that PureScript-generated circuit constraints
// and witness values satisfy the same equations as the Rust Kimchi proof system.

pub mod complete_add;

pub use complete_add::*;
