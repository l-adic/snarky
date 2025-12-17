use ark_ec::models::short_weierstrass::SWCurveConfig;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField, UniformRand, Zero};
use napi::bindgen_prelude::*;
use napi_derive::napi;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::str::FromStr;

use super::types::{
    PallasConfig, PallasGroup, PallasScalarField, ProjectivePallas, VestaScalarField,
};

pub mod scalar_field {
    use super::*;
    use crate::bigint::napi_bigint_to_ark_bigint;

    pub type FieldExternal = External<PallasScalarField>;

    #[napi]
    pub fn pallas_scalarfield_zero() -> FieldExternal {
        External::new(PallasScalarField::zero())
    }

    #[napi]
    pub fn pallas_scalarfield_one() -> FieldExternal {
        External::new(PallasScalarField::one())
    }

    #[napi]
    pub fn pallas_scalarfield_from_string(s: String) -> Result<FieldExternal> {
        PallasScalarField::from_str(&s)
            .map(External::new)
            .map_err(|_| Error::from_reason("Failed to parse field element"))
    }

    #[napi]
    pub fn pallas_scalarfield_add(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
        External::new(**a + **b)
    }

    #[napi]
    pub fn pallas_scalarfield_sub(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
        External::new(**a - **b)
    }

    #[napi]
    pub fn pallas_scalarfield_mul(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
        External::new(**a * **b)
    }

    #[napi]
    pub fn pallas_scalarfield_div(a: &FieldExternal, b: &FieldExternal) -> Result<FieldExternal> {
        if let Some(b_inv) = b.inverse() {
            Ok(External::new(**a * b_inv))
        } else {
            Err(Error::from_reason("Division by zero"))
        }
    }

    #[napi]
    pub fn pallas_scalarfield_invert(x: &FieldExternal) -> Result<FieldExternal> {
        if let Some(inv) = x.inverse() {
            Ok(External::new(inv))
        } else {
            Err(Error::from_reason("Element is not invertible"))
        }
    }

    #[napi]
    pub fn pallas_scalarfield_eq(a: &FieldExternal, b: &FieldExternal) -> bool {
        **a == **b
    }

    #[napi]
    pub fn pallas_scalarfield_to_string(x: &FieldExternal) -> String {
        format!("{:?}", **x)
    }

    #[napi]
    pub fn pallas_scalarfield_rand(seed: u32) -> FieldExternal {
        let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
        External::new(PallasScalarField::rand(&mut rng))
    }

    #[napi]
    pub fn pallas_scalarfield_modulus() -> String {
        PallasScalarField::MODULUS.to_string()
    }

    #[napi]
    pub fn pallas_scalarfield_from_bigint(
        bigint: napi::bindgen_prelude::BigInt,
    ) -> Result<FieldExternal> {
        let ark_bigint = napi_bigint_to_ark_bigint::<PallasScalarField, 4>(bigint)?;
        let field_elem = PallasScalarField::from(ark_bigint);
        Ok(External::new(field_elem))
    }

    #[napi]
    pub fn pallas_scalarfield_to_bigint(x: &FieldExternal) -> napi::bindgen_prelude::BigInt {
        let repr = x.into_bigint();
        crate::bigint::ark_bigint_to_napi(&repr)
    }

    #[napi]
    pub fn pallas_scalarfield_pow(
        base: &FieldExternal,
        exponent: napi::bindgen_prelude::BigInt,
    ) -> Result<FieldExternal> {
        let exp_ark = crate::bigint::napi_bigint_to_ark_bigint::<PallasScalarField, 4>(exponent)?;
        let exp_limbs = exp_ark.as_ref();
        let result = base.pow(exp_limbs);
        Ok(External::new(result))
    }
}

// Note: Pallas base field operations handled via Vesta scalar field (curve duality)

pub mod group {
    use super::*;

    type G = External<PallasGroup>;

    #[napi]
    pub fn pallas_group_weierstrass_a() -> External<VestaScalarField> {
        let coeff_a = <PallasConfig as SWCurveConfig>::COEFF_A;
        External::new(coeff_a)
    }

    #[napi]
    pub fn pallas_group_weierstrass_b() -> External<VestaScalarField> {
        let coeff_b = <PallasConfig as SWCurveConfig>::COEFF_B;
        External::new(coeff_b)
    }

    #[napi]
    pub fn pallas_group_add(p1: &G, p2: &G) -> G {
        let result = (**p1 + **p2).into();
        External::new(result)
    }

    #[napi]
    pub fn pallas_group_rand(seed: u32) -> G {
        let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
        let point: ProjectivePallas = UniformRand::rand(&mut rng);
        External::new(point.into_affine())
    }

    #[napi]
    pub fn pallas_group_identity() -> G {
        External::new(PallasGroup::identity())
    }

    #[napi]
    pub fn pallas_group_eq(p1: &G, p2: &G) -> bool {
        **p1 == **p2
    }

    #[napi]
    pub fn pallas_group_to_string(p: &G) -> String {
        format!("{:?}", **p)
    }

    #[napi]
    pub fn pallas_group_neg(p: &G) -> G {
        External::new(-(**p))
    }

    #[napi]
    pub fn pallas_group_scale(p: &G, scalar: &scalar_field::FieldExternal) -> G {
        let result = (**p * **scalar).into_affine();
        External::new(result)
    }

    #[napi]
    pub fn pallas_group_to_affine(
        p: &G,
    ) -> Option<(External<VestaScalarField>, External<VestaScalarField>)> {
        if (**p).is_zero() {
            // Point at infinity (identity element) has no affine coordinates
            None
        } else {
            Some((External::new(p.x), External::new(p.y)))
        }
    }
}
