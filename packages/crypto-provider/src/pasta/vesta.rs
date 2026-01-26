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

    /// Parse a field element from a little-endian hex string (as used in test vectors)
    #[napi]
    pub fn vesta_scalarfield_from_hex_le(hex: String) -> Result<FieldExternal> {
        use ark_serialize::CanonicalDeserialize;

        // Decode hex to bytes
        let bytes = hex::decode(&hex)
            .map_err(|e| Error::from_reason(format!("Invalid hex string: {e}")))?;

        // Deserialize from little-endian bytes (arkworks canonical format)
        let field_elem = VestaScalarField::deserialize_uncompressed(&bytes[..])
            .map_err(|e| Error::from_reason(format!("Failed to deserialize field element: {e}")))?;

        Ok(External::new(field_elem))
    }

    /// Serialize a field element to a little-endian hex string
    #[napi]
    pub fn vesta_scalarfield_to_hex_le(x: &FieldExternal) -> Result<String> {
        use ark_serialize::CanonicalSerialize;

        let mut bytes = Vec::new();
        x.serialize_uncompressed(&mut bytes)
            .map_err(|e| Error::from_reason(format!("Failed to serialize field element: {e}")))?;

        Ok(hex::encode(&bytes))
    }

    #[napi]
    pub fn vesta_endo_base() -> External<PallasScalarField> {
        use mina_curves::pasta::Vesta;
        use poly_commitment::ipa::endos;
        let (endo_q, _endo_r) = endos::<Vesta>();
        External::new(endo_q)
    }

    #[napi]
    pub fn vesta_endo_scalar() -> FieldExternal {
        use mina_curves::pasta::Vesta;
        use poly_commitment::ipa::endos;
        let (_endo_q, endo_r) = endos::<Vesta>();
        External::new(endo_r)
    }

    /// Check if field element is a quadratic residue (has a square root)
    #[napi]
    pub fn vesta_scalarfield_is_square(x: &FieldExternal) -> bool {
        x.legendre().is_qr()
    }

    /// Compute the square root of a field element if it exists
    #[napi]
    pub fn vesta_scalarfield_sqrt(x: &FieldExternal) -> Option<FieldExternal> {
        x.sqrt().map(External::new)
    }
}

/// BW19 GroupMap parameters for Vesta curve
/// These are precomputed constants used for hash-to-curve
pub mod group_map {
    use super::*;
    use kimchi::groupmap::{BWParameters, GroupMap};

    /// Get all BW19 parameters for Vesta curve as an array
    /// Returns [u, fu, sqrt_neg_three_u_squared_minus_u_over_2, sqrt_neg_three_u_squared, inv_three_u_squared]
    #[napi]
    pub fn vesta_bw19_params() -> Vec<External<PallasScalarField>> {
        let params: BWParameters<VestaConfig> = BWParameters::setup();
        vec![
            External::new(params.u),
            External::new(params.fu),
            External::new(params.sqrt_neg_three_u_squared_minus_u_over_2),
            External::new(params.sqrt_neg_three_u_squared),
            External::new(params.inv_three_u_squared),
        ]
    }

    /// Hash a base field element to a point on the Vesta curve using BW19 algorithm
    /// Returns (x, y) coordinates in the base field (= PallasScalarField)
    #[napi]
    pub fn vesta_group_map(
        t: &External<PallasScalarField>,
    ) -> (External<PallasScalarField>, External<PallasScalarField>) {
        let params: BWParameters<VestaConfig> = BWParameters::setup();
        let (x, y) = params.to_group(**t);
        (External::new(x), External::new(y))
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
    pub fn vesta_group_generator() -> G {
        External::new(VestaGroup::generator())
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
        y: &pallas::scalar_field::FieldExternal,
    ) -> G {
        let p = Affine {
            x: **x,
            y: **y,
            infinity: false,
        };
        p.into()
    }
}
