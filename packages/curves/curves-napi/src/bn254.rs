use ark_ff::{Field, Zero, One, UniformRand, PrimeField};
use ark_bn254::Fr as BN254Fr;
use napi::bindgen_prelude::*;
use napi_derive::napi;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::str::FromStr;
use num_bigint::BigUint;

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

#[napi]
pub fn bn254_from_bigint(bigint: BigInt) -> Result<FieldExternal> {
    // Check if negative
    if bigint.sign_bit {
        return Err(Error::from_reason("Negative BigInt not supported for field elements"));
    }
    
    // Convert u64 words to u32 words for num_bigint::BigUint
    let mut u32_words = Vec::new();
    for word in bigint.words {
        // Split each u64 into two u32s (little-endian)
        u32_words.push(word as u32);
        u32_words.push((word >> 32) as u32);
    }
    let biguint = BigUint::new(u32_words);
    
    // Use PrimeField's From<BigUint> trait (automatically reduces modulo p)
    let field_elem = BN254Fr::from(biguint);
    Ok(External::new(field_elem))
}

#[napi]
pub fn bn254_modulus() -> BigInt {
    // Convert modulus to BigUint and then to NAPI BigInt
    let modulus_biguint: BigUint = BN254Fr::MODULUS.into();
    
    // Get the u64 limbs (little-endian)
    let limbs: Vec<u64> = modulus_biguint.to_u64_digits();
    
    BigInt {
        sign_bit: false,
        words: limbs,
    }
}
