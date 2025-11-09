use crate::bigint::napi_bigint_to_ark_bigint;
use ark_ff::{Field, One, PrimeField, UniformRand, Zero};
use ark_pallas::Fq as VestaFr;
use napi::bindgen_prelude::*;
use napi_derive::napi;
use num_bigint::BigUint;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::str::FromStr;

type FieldExternal = External<VestaFr>;

#[napi]
pub fn vesta_zero() -> FieldExternal {
    External::new(VestaFr::zero())
}

#[napi]
pub fn vesta_one() -> FieldExternal {
    External::new(VestaFr::one())
}

#[napi]
pub fn vesta_from_string(s: String) -> Result<FieldExternal> {
    VestaFr::from_str(&s)
        .map(External::new)
        .map_err(|_| Error::from_reason("Failed to parse field element"))
}

#[napi]
pub fn vesta_add(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
    External::new(**a + **b)
}

#[napi]
pub fn vesta_sub(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
    External::new(**a - **b)
}

#[napi]
pub fn vesta_mul(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
    External::new(**a * **b)
}

#[napi]
pub fn vesta_div(a: &FieldExternal, b: &FieldExternal) -> Result<FieldExternal> {
    if b.is_zero() {
        return Err(Error::from_reason("Division by zero"));
    }
    Ok(External::new(**a / **b))
}

#[napi]
pub fn vesta_invert(a: &FieldExternal) -> Result<FieldExternal> {
    a.inverse()
        .map(External::new)
        .ok_or_else(|| Error::from_reason("Cannot invert zero"))
}

#[napi]
pub fn vesta_eq(a: &FieldExternal, b: &FieldExternal) -> bool {
    **a == **b
}

#[napi]
pub fn vesta_to_string(a: &FieldExternal) -> String {
    a.to_string()
}

#[napi]
pub fn vesta_rand(seed: u32) -> FieldExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
    External::new(VestaFr::rand(&mut rng))
}

#[napi]
pub fn vesta_from_bigint(bigint: BigInt) -> Result<FieldExternal> {
    // Use the bigint module to handle conversion with proper modular reduction
    let ark_bigint = napi_bigint_to_ark_bigint::<VestaFr, 4>(bigint)?;
    let field_elem = VestaFr::from(ark_bigint);
    Ok(External::new(field_elem))
}

#[napi]
pub fn vesta_modulus() -> BigInt {
    // Convert modulus to BigUint and then to NAPI BigInt
    let modulus_biguint: BigUint = VestaFr::MODULUS.into();

    // Get the u64 limbs (little-endian)
    let limbs: Vec<u64> = modulus_biguint.to_u64_digits();

    BigInt {
        sign_bit: false,
        words: limbs,
    }
}
