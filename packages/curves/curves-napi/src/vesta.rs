use ark_ff::{Field, Zero, One, UniformRand};
use ark_pallas::Fq as VestaFr;
use napi::bindgen_prelude::*;
use napi_derive::napi;
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
        .map(|value| External::new(value))
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
        .map(|value| External::new(value))
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