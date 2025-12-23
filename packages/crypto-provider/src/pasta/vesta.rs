use ark_ec::models::short_weierstrass::SWCurveConfig;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField, UniformRand, Zero};
use napi::bindgen_prelude::*;
use napi_derive::napi;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::str::FromStr;

use super::types::{PallasScalarField, ProjectiveVesta, VestaConfig, VestaGroup, VestaScalarField};

pub mod scalar_field {
    use super::*;
    use crate::bigint::napi_bigint_to_ark_bigint;

    pub type FieldExternal = External<VestaScalarField>;

    #[napi]
    pub fn vesta_scalarfield_zero() -> FieldExternal {
        External::new(VestaScalarField::zero())
    }

    #[napi]
    pub fn vesta_scalarfield_one() -> FieldExternal {
        External::new(VestaScalarField::one())
    }

    #[napi]
    pub fn vesta_scalarfield_from_string(s: String) -> Result<FieldExternal> {
        VestaScalarField::from_str(&s)
            .map(External::new)
            .map_err(|_| Error::from_reason("Failed to parse field element"))
    }

    #[napi]
    pub fn vesta_scalarfield_add(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
        External::new(**a + **b)
    }

    #[napi]
    pub fn vesta_scalarfield_sub(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
        External::new(**a - **b)
    }

    #[napi]
    pub fn vesta_scalarfield_mul(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
        External::new(**a * **b)
    }

    #[napi]
    pub fn vesta_scalarfield_div(a: &FieldExternal, b: &FieldExternal) -> Result<FieldExternal> {
        if let Some(b_inv) = b.inverse() {
            Ok(External::new(**a * b_inv))
        } else {
            Err(Error::from_reason("Division by zero"))
        }
    }

    #[napi]
    pub fn vesta_scalarfield_invert(x: &FieldExternal) -> Result<FieldExternal> {
        if let Some(inv) = x.inverse() {
            Ok(External::new(inv))
        } else {
            Err(Error::from_reason("Element is not invertible"))
        }
    }

    #[napi]
    pub fn vesta_scalarfield_eq(a: &FieldExternal, b: &FieldExternal) -> bool {
        **a == **b
    }

    #[napi]
    pub fn vesta_scalarfield_to_string(x: &FieldExternal) -> String {
        format!("{:?}", **x)
    }

    #[napi]
    pub fn vesta_scalarfield_rand(seed: u32) -> FieldExternal {
        let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
        External::new(VestaScalarField::rand(&mut rng))
    }

    #[napi]
    pub fn vesta_scalarfield_modulus() -> String {
        VestaScalarField::MODULUS.to_string()
    }

    #[napi]
    pub fn vesta_scalarfield_from_bigint(
        bigint: napi::bindgen_prelude::BigInt,
    ) -> Result<FieldExternal> {
        let ark_bigint = napi_bigint_to_ark_bigint::<VestaScalarField, 4>(bigint)?;
        let field_elem = VestaScalarField::from(ark_bigint);
        Ok(External::new(field_elem))
    }

    #[napi]
    pub fn vesta_scalarfield_to_bigint(x: &FieldExternal) -> napi::bindgen_prelude::BigInt {
        let repr = x.into_bigint();
        crate::bigint::ark_bigint_to_napi(&repr)
    }

    #[napi]
    pub fn vesta_scalarfield_pow(
        base: &FieldExternal,
        exponent: napi::bindgen_prelude::BigInt,
    ) -> Result<FieldExternal> {
        let exp_ark = crate::bigint::napi_bigint_to_ark_bigint::<VestaScalarField, 4>(exponent)?;
        let exp_limbs = exp_ark.as_ref();
        let result = base.pow(exp_limbs);
        Ok(External::new(result))
    }
}

// Note: Vesta base field operations removed - now handled via Pallas scalar field cross-wiring in JS layer

pub mod group {
    use ark_ec::short_weierstrass::Affine;

    use crate::pallas;

    use super::*;

    type G = External<VestaGroup>;

    #[napi]
    pub fn vesta_group_weierstrass_a() -> External<PallasScalarField> {
        let coeff_a = <VestaConfig as SWCurveConfig>::COEFF_A;
        External::new(coeff_a)
    }

    #[napi]
    pub fn vesta_group_weierstrass_b() -> External<PallasScalarField> {
        let coeff_b = <VestaConfig as SWCurveConfig>::COEFF_B;
        External::new(coeff_b)
    }

    #[napi]
    pub fn vesta_group_add(p1: &G, p2: &G) -> G {
        let result = (**p1 + **p2).into();
        External::new(result)
    }

    #[napi]
    pub fn vesta_group_rand(seed: u32) -> G {
        let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
        let point: ProjectiveVesta = UniformRand::rand(&mut rng);
        External::new(point.into_affine())
    }

    #[napi]
    pub fn vesta_group_identity() -> G {
        External::new(VestaGroup::identity())
    }

    #[napi]
    pub fn vesta_group_eq(p1: &G, p2: &G) -> bool {
        **p1 == **p2
    }

    #[napi]
    pub fn vesta_group_to_string(p: &G) -> String {
        format!("{:?}", **p)
    }

    #[napi]
    pub fn vesta_group_neg(p: &G) -> G {
        External::new(-(**p))
    }

    #[napi]
    pub fn vesta_group_scale(p: &G, scalar: &scalar_field::FieldExternal) -> G {
        let result = (**p * **scalar).into_affine();
        External::new(result)
    }

    #[napi]
    pub fn vesta_group_to_affine(
        p: &G,
    ) -> Option<(External<PallasScalarField>, External<PallasScalarField>)> {
        if (**p).is_zero() {
            // Point at infinity (identity element) has no affine coordinates
            None
        } else {
            Some((External::new(p.x), External::new(p.y)))
        }
    }

    #[napi]
    pub fn vesta_group_from_affine(
        x: &pallas::scalar_field::FieldExternal,
        y: &pallas::scalar_field::FieldExternal
    ) -> G {
        let p = Affine {x: **x, y: **y, infinity: false};
        p.into()
    }
}
