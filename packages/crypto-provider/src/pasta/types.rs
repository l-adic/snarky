//! Conditional type aliases for Pasta curves
//!
//! This module provides the same API regardless of whether we're using
//! arkworks curves (ark-pallas/ark-vesta) or mina-curves.

// Compile-time check to ensure exactly one backend is enabled
#[cfg(not(any(feature = "arkworks", feature = "mina-curves-backend")))]
compile_error!("Either 'arkworks' or 'mina-curves-backend' feature must be enabled");

#[cfg(all(feature = "arkworks", feature = "mina-curves-backend"))]
compile_error!("Cannot enable both 'arkworks' and 'mina-curves-backend' features simultaneously");

// Arkworks backend types
#[cfg(all(feature = "arkworks", not(feature = "mina-curves-backend")))]
mod backend {
    // Pallas types from arkworks
    pub use ark_pallas::{
        Affine as PallasGroup,
        Fq as PallasBaseField,   // Pallas base field
        Fr as PallasScalarField, // Pallas scalar field
        PallasConfig,
        Projective as ProjectivePallas,
    };

    // Vesta types from arkworks
    pub use ark_vesta::{
        Affine as VestaGroup,
        Fq as VestaBaseField,   // Vesta base field (= Pallas scalar field)
        Fr as VestaScalarField, // Vesta scalar field (= Pallas base field)
        Projective as ProjectiveVesta,
        VestaConfig,
    };
}

// Mina-curves backend types
#[cfg(all(feature = "mina-curves-backend", not(feature = "arkworks")))]
mod backend {
    // Pallas types from mina-curves
    pub use mina_curves::pasta::{
        Fp as PallasBaseField,   // Pallas base field
        Fq as PallasScalarField, // Pallas scalar field
        Pallas as PallasGroup,
        PallasParameters as PallasConfig,
        ProjectivePallas,
    };

    // Vesta types from mina-curves
    pub use mina_curves::pasta::{
        Fp as VestaScalarField, // Vesta scalar field (= Pallas base field)
        Fq as VestaBaseField,   // Vesta base field (= Pallas scalar field)
        ProjectiveVesta,
        Vesta as VestaGroup,
        VestaParameters as VestaConfig,
    };
}

// Re-export all types from the selected backend
pub use backend::*;
