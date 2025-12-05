use napi::bindgen_prelude::*;
use napi_derive::napi;

pub mod circuit;

// Re-export all curves functionality
pub use curves_napi::*;

#[napi]
pub fn init() -> Result<()> {
    Ok(())
}