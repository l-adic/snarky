pub mod bn254;

mod bigint;

// Pasta curves with conditional backend support
#[cfg(any(feature = "arkworks", feature = "mina-curves-backend"))]
pub mod pasta;

// Re-export pasta functions for backward compatibility
#[cfg(any(feature = "arkworks", feature = "mina-curves-backend"))]
pub use pasta::*;
