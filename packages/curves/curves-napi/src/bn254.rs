use ark_ff::{Field, Zero, One, UniformRand};
use ark_bn254::Fr as BN254Fr;
use napi::bindgen_prelude::*;
use napi_derive::napi;
use std::str::FromStr;

type FieldExternal = External<BN254Fr>;

#[napi]
pub fn zero() -> FieldExternal {
    External::new(BN254Fr::zero())
}

#[napi]
pub fn one() -> FieldExternal {
    External::new(BN254Fr::one())
}

#[napi]
pub fn random() -> FieldExternal {
    let mut rng = ark_std::rand::thread_rng();
    External::new(BN254Fr::rand(&mut rng))
}

#[napi]
pub fn from_string(s: String) -> Result<FieldExternal> {
    BN254Fr::from_str(&s)
        .map(|value| External::new(value))
        .map_err(|_| Error::from_reason("Failed to parse field element"))
}

#[napi]
pub fn add(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
    External::new(**a + **b)
}

#[napi]
pub fn sub(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
    External::new(**a - **b)
}

#[napi]
pub fn mul(a: &FieldExternal, b: &FieldExternal) -> FieldExternal {
    External::new(**a * **b)
}

#[napi]
pub fn div(a: &FieldExternal, b: &FieldExternal) -> Result<FieldExternal> {
    if b.is_zero() {
        return Err(Error::from_reason("Division by zero"));
    }
    Ok(External::new(**a / **b))
}

#[napi]
pub fn invert(a: &FieldExternal) -> Result<FieldExternal> {
    a.inverse()
        .map(|value| External::new(value))
        .ok_or_else(|| Error::from_reason("Cannot invert zero"))
}

#[napi]
pub fn eq(a: &FieldExternal, b: &FieldExternal) -> bool {
    **a == **b
}

#[napi]
pub fn to_string(a: &FieldExternal) -> String {
    a.to_string()
}