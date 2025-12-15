// Conditional type aliases for backend selection
// This mirrors the pattern used in curves-napi to support both arkworks and mina-curves

#[cfg(feature = "arkworks")]
mod arkworks_types {
    pub use ark_pallas::{Fr as PallasScalarField, Projective as PallasProjective};
    pub use ark_vesta::{Fr as VestaScalarField, Projective as VestaProjective};
}

#[cfg(feature = "mina-curves-backend")]
mod mina_types {
    pub use mina_curves::pasta::{
        Fp as VestaScalarField, Fq as PallasScalarField, ProjectivePallas as PallasProjective,
        ProjectiveVesta as VestaProjective,
    };
}

// Re-export the appropriate types based on feature selection
#[cfg(feature = "arkworks")]
pub use arkworks_types::*;

#[cfg(feature = "mina-curves-backend")]
pub use mina_types::*;

// Type aliases for bulletproofs types that depend on field types
use napi::bindgen_prelude::External;

// Re-export bulletproofs types for use in circuit.rs
pub use bulletproofs::circuit::types::{Circuit, Statement, Witness, CRS};

pub type PallasCrsExternal = External<CRS<PallasProjective>>;
pub type PallasWitnessExternal = External<Witness<PallasScalarField>>;
pub type PallasStatementExternal = External<Statement<PallasProjective>>;
pub type PallasCircuitExternal = External<Circuit<PallasScalarField>>;
pub type PallasProofExternal = External<Vec<u8>>;

pub type VestaCrsExternal = External<CRS<VestaProjective>>;
pub type VestaWitnessExternal = External<Witness<VestaScalarField>>;
pub type VestaStatementExternal = External<Statement<VestaProjective>>;
pub type VestaCircuitExternal = External<Circuit<VestaScalarField>>;
pub type VestaProofExternal = External<Vec<u8>>;
