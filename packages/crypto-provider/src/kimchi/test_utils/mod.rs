// Test utilities for validating circuit constraints against Kimchi gate implementations
//
// This module provides functions to verify that PureScript-generated circuit constraints
// and witness values satisfy the same equations as the Rust Kimchi proof system.

pub mod complete_add;
pub mod generic;
pub mod poseidon;
pub mod varbasemul;

pub use complete_add::*;
pub use generic::*;
pub use poseidon::*;
pub use varbasemul::*;

use kimchi::circuits::wires::COLUMNS;
use napi_derive::napi;

#[napi]
pub fn get_columns_count() -> u32 {
    COLUMNS as u32
}
