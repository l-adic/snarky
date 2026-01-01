//! Type aliases for Pasta curves using mina-curves backend

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
