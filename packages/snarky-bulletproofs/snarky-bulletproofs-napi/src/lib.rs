use napi::bindgen_prelude::*;
use napi_derive::napi;

pub mod circuit;
pub mod types;

// Re-export all curves functionality
pub use curves_napi::*;

#[napi]
pub fn init() -> Result<()> {
    Ok(())
}
