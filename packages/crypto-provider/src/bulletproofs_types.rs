// Conditional type aliases for backend selection
// This mirrors the pattern used in pasta module to support both arkworks and mina-curves

use crate::pasta::types::{
    PallasScalarField, ProjectivePallas as PallasProjective, ProjectiveVesta as VestaProjective,
    VestaScalarField,
};

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
