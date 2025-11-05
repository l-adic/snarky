use ark_ff::{Field, Zero, One, UniformRand};
use ark_bn254::Fr as BN254Fr;
use napi::bindgen_prelude::*;
use napi_derive::napi;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::str::FromStr;

type FieldExternal = External<BN254Fr>;

#[napi]
pub fn bn254_zero() -> FieldExternal {
    External::new(BN254Fr::zero())
}

#[napi]
pub fn bn254_one() -> FieldExternal {
    External::new(BN254Fr::one())
}

#[napi]
pub fn bn254_from_string(s: String) -> Result<FieldExternal> {
    BN254Fr::from_str(&s)
        .map(|value| External::new(value))
        .map_err(|_| Error::from_reason("Failed to parse field element"))
}

#[napi]
pub fn bn254_add(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
    External::new(**a + **b)
}

#[napi]
pub fn bn254_sub(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
    External::new(**a - **b)
}

#[napi]
pub fn bn254_mul(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
    External::new(**a * **b)
}

#[napi]
pub fn bn254_div(a: &FieldExternal, b: &FieldExternal) -> Result<FieldExternal> {
    if b.is_zero() {
        return Err(Error::from_reason("Division by zero"));
    }
    Ok(External::new(**a / **b))
}

#[napi]
pub fn bn254_invert(a: &FieldExternal) -> Result<FieldExternal> {
    a.inverse()
        .map(|value| External::new(value))
        .ok_or_else(|| Error::from_reason("Cannot invert zero"))
}

#[napi]
pub fn bn254_eq(a: &FieldExternal, b: &FieldExternal) -> bool {
    **a == **b
}

#[napi]
pub fn bn254_to_string(a: &FieldExternal) -> String {
    a.to_string()
}

#[napi]
pub fn bn254_rand(seed: u32) -> FieldExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
    External::new(BN254Fr::rand(&mut rng))
}
