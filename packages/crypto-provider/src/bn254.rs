use ark_bn254::{g1::Config as Bn254Config, Fq as Bn254Fq, Fr as Bn254Fr, G1Affine as Affine};
use ark_ec::models::short_weierstrass::SWCurveConfig;
use ark_ec::CurveGroup;
use ark_ff::{Field, One, PrimeField, UniformRand, Zero};
use napi::bindgen_prelude::*;
use napi_derive::napi;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::str::FromStr;

pub mod scalar_field {
    use super::*;
    use crate::bigint::napi_bigint_to_ark_bigint;

    pub type FieldExternal = External<Bn254Fr>;

    #[napi]
    pub fn bn254_scalarfield_zero() -> FieldExternal {
        External::new(Bn254Fr::zero())
    }

    #[napi]
    pub fn bn254_scalarfield_one() -> FieldExternal {
        External::new(Bn254Fr::one())
    }

    #[napi]
    pub fn bn254_scalarfield_from_string(s: String) -> Result<FieldExternal> {
        Bn254Fr::from_str(&s)
            .map(External::new)
            .map_err(|_| Error::from_reason("Failed to parse field element"))
    }

    #[napi]
    pub fn bn254_scalarfield_add(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
        External::new(**a + **b)
    }

    #[napi]
    pub fn bn254_scalarfield_sub(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
        External::new(**a - **b)
    }

    #[napi]
    pub fn bn254_scalarfield_mul(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
        External::new(**a * **b)
    }

    #[napi]
    pub fn bn254_scalarfield_div(a: &FieldExternal, b: &FieldExternal) -> Result<FieldExternal> {
        if b.is_zero() {
            return Err(Error::from_reason("Division by zero"));
        }
        Ok(External::new(**a / **b))
    }

    #[napi]
    pub fn bn254_scalarfield_invert(a: &FieldExternal) -> Result<FieldExternal> {
        a.inverse()
            .map(External::new)
            .ok_or_else(|| Error::from_reason("Cannot invert zero"))
    }

    #[napi]
    pub fn bn254_scalarfield_eq(a: &FieldExternal, b: &FieldExternal) -> bool {
        **a == **b
    }

    #[napi]
    pub fn bn254_scalarfield_to_string(a: &FieldExternal) -> String {
        a.to_string()
    }

    #[napi]
    pub fn bn254_scalarfield_rand(seed: u32) -> FieldExternal {
        let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
        External::new(Bn254Fr::rand(&mut rng))
    }

    #[napi]
    pub fn bn254_scalarfield_from_bigint(bigint: BigInt) -> Result<FieldExternal> {
        let ark_bigint = napi_bigint_to_ark_bigint::<Bn254Fr, 4>(bigint)?;
        let field_elem = Bn254Fr::from(ark_bigint);
        Ok(External::new(field_elem))
    }

    #[napi]
    pub fn bn254_scalarfield_modulus() -> BigInt {
        crate::bigint::ark_bigint_to_napi(&Bn254Fr::MODULUS)
    }

    #[napi]
    pub fn bn254_scalarfield_to_bigint(a: &FieldExternal) -> BigInt {
        let repr = a.into_bigint();
        crate::bigint::ark_bigint_to_napi(&repr)
    }

    #[napi]
    pub fn bn254_scalarfield_pow(base: &FieldExternal, exponent: BigInt) -> Result<FieldExternal> {
        let exp_ark = napi_bigint_to_ark_bigint::<Bn254Fr, 4>(exponent)?;
        let exp_limbs = exp_ark.as_ref();
        let result = base.pow(exp_limbs);
        Ok(External::new(result))
    }
}

pub mod base_field {
    use super::*;
    use crate::bigint::napi_bigint_to_ark_bigint;

    pub type BaseFieldExternal = External<Bn254Fq>;

    #[napi]
    pub fn bn254_basefield_zero() -> BaseFieldExternal {
        External::new(Bn254Fq::zero())
    }

    #[napi]
    pub fn bn254_basefield_one() -> BaseFieldExternal {
        External::new(Bn254Fq::one())
    }

    #[napi]
    pub fn bn254_basefield_from_string(s: String) -> Result<BaseFieldExternal> {
        Bn254Fq::from_str(&s)
            .map(External::new)
            .map_err(|_| Error::from_reason("Failed to parse base field element"))
    }

    #[napi]
    pub fn bn254_basefield_add(a: &BaseFieldExternal, b: &BaseFieldExternal) -> BaseFieldExternal {
        External::new(**a + **b)
    }

    #[napi]
    pub fn bn254_basefield_sub(a: &BaseFieldExternal, b: &BaseFieldExternal) -> BaseFieldExternal {
        External::new(**a - **b)
    }

    #[napi]
    pub fn bn254_basefield_mul(a: &BaseFieldExternal, b: &BaseFieldExternal) -> BaseFieldExternal {
        External::new(**a * **b)
    }

    #[napi]
    pub fn bn254_basefield_div(
        a: &BaseFieldExternal,
        b: &BaseFieldExternal,
    ) -> Result<BaseFieldExternal> {
        if b.is_zero() {
            return Err(Error::from_reason("Division by zero"));
        }
        Ok(External::new(**a / **b))
    }

    #[napi]
    pub fn bn254_basefield_invert(a: &BaseFieldExternal) -> Result<BaseFieldExternal> {
        a.inverse()
            .map(External::new)
            .ok_or_else(|| Error::from_reason("Cannot invert zero"))
    }

    #[napi]
    pub fn bn254_basefield_eq(a: &BaseFieldExternal, b: &BaseFieldExternal) -> bool {
        **a == **b
    }

    #[napi]
    pub fn bn254_basefield_to_string(a: &BaseFieldExternal) -> String {
        a.to_string()
    }

    #[napi]
    pub fn bn254_basefield_rand(seed: u32) -> BaseFieldExternal {
        let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
        External::new(Bn254Fq::rand(&mut rng))
    }

    #[napi]
    pub fn bn254_basefield_from_bigint(bigint: BigInt) -> Result<BaseFieldExternal> {
        let ark_bigint = napi_bigint_to_ark_bigint::<Bn254Fq, 4>(bigint)?;
        let field_elem = Bn254Fq::from(ark_bigint);
        Ok(External::new(field_elem))
    }

    #[napi]
    pub fn bn254_basefield_modulus() -> BigInt {
        crate::bigint::ark_bigint_to_napi(&Bn254Fq::MODULUS)
    }

    #[napi]
    pub fn bn254_basefield_to_bigint(a: &BaseFieldExternal) -> BigInt {
        let repr = a.into_bigint();
        crate::bigint::ark_bigint_to_napi(&repr)
    }

    #[napi]
    pub fn bn254_basefield_pow(
        base: &BaseFieldExternal,
        exponent: BigInt,
    ) -> Result<BaseFieldExternal> {
        let exp_ark = napi_bigint_to_ark_bigint::<Bn254Fq, 4>(exponent)?;
        let exp_limbs = exp_ark.as_ref();
        let result = base.pow(exp_limbs);
        Ok(External::new(result))
    }
}

pub mod group {
    use super::*;
    use ark_bn254::G1Projective as Projective;
    use ark_ec::AffineRepr;

    type G = External<Affine>;
    type BaseFieldExternal = External<Bn254Fq>;

    #[napi]
    pub fn bn254_group_weierstrass_a() -> BaseFieldExternal {
        External::new(<Bn254Config as SWCurveConfig>::COEFF_A)
    }

    #[napi]
    pub fn bn254_group_weierstrass_b() -> BaseFieldExternal {
        External::new(<Bn254Config as SWCurveConfig>::COEFF_B)
    }

    #[napi]
    pub fn bn254_group_add(p1: &G, p2: &G) -> G {
        let result = **p1 + **p2;
        External::new(result.into())
    }

    #[napi]
    pub fn bn254_group_rand(seed: u32) -> G {
        let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
        let point: Projective = UniformRand::rand(&mut rng);
        External::new(point.into_affine())
    }

    #[napi]
    pub fn bn254_group_identity() -> G {
        External::new(Affine::identity())
    }

    #[napi]
    pub fn bn254_group_eq(p1: &G, p2: &G) -> bool {
        **p1 == **p2
    }

    #[napi]
    pub fn bn254_group_to_string(p: &G) -> String {
        format!("{:?}", **p)
    }

    #[napi]
    pub fn bn254_group_neg(p: &G) -> G {
        External::new(-(**p))
    }

    #[napi]
    pub fn bn254_group_scale(p: &G, scalar: &scalar_field::FieldExternal) -> G {
        let result = (**p) * (**scalar);
        External::new(result.into())
    }

    #[napi]
    pub fn bn254_group_to_affine(p: &G) -> Option<(BaseFieldExternal, BaseFieldExternal)> {
        if (**p).is_zero() {
            // Point at infinity (identity element) has no affine coordinates
            None
        } else {
            Some((External::new(p.x), External::new(p.y)))
        }
    }

    #[napi]
    pub fn bn254_group_from_affine(
        x: &base_field::BaseFieldExternal,
        y: &base_field::BaseFieldExternal
    ) -> G {
        let p = Affine {x: **x, y: **y, infinity: false};
        p.into()
    }
}
