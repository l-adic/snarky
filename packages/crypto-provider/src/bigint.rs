//! BigInt conversion utilities for bridging JavaScript and Rust.
//!
//! This module handles conversions between three BigInt representations:
//!
//! - **NAPI BigInt**: JavaScript's native BigInt, passed via NAPI as `{sign_bit, words}`
//! - **num-bigint**: Rust's arbitrary-precision integers (for intermediate computation)
//! - **arkworks BigInt**: Fixed-limb representation used by ark_ff field elements
//!
//! Key operations:
//! - Automatic modular reduction when converting to field elements
//! - Correct handling of negative numbers (reduced to positive representatives)
//! - Round-trip preservation for values in range

use ark_ff::{BigInt, PrimeField};
use core::convert::TryInto;
use napi::bindgen_prelude::{BigInt as NapiBigInt, Result as NapiResult};
use napi::Error;
use num_bigint::{BigInt as NumBigInt, BigUint, Sign};
use num_integer::Integer;

/// Converts a NAPI BigInt (u64 limbs) to a signed num_bigint::BigInt
pub fn napi_bigint_to_num_bigint(bigint: NapiBigInt) -> NapiResult<NumBigInt> {
    let u32_words: Vec<u32> = bigint
        .words
        .iter()
        .flat_map(|&word| [word as u32, (word >> 32) as u32])
        .collect();

    let sign = if bigint.sign_bit {
        Sign::Minus
    } else {
        Sign::Plus
    };
    Ok(NumBigInt::from_biguint(sign, BigUint::new(u32_words)))
}

/// Reduces NumBigInt modulo F::MODULUS and converts to ark_ff::BigInt<N>
pub fn num_bigint_to_ark_bigint<F, const N: usize>(num_bigint: NumBigInt) -> NapiResult<BigInt<N>>
where
    F: PrimeField<BigInt = BigInt<N>>,
{
    let modulus_bigint: NumBigInt = F::MODULUS.into();

    // mod_floor handles both positive and negative numbers correctly
    let reduced = num_bigint.mod_floor(&modulus_bigint);
    let positive_biguint = reduced
        .to_biguint()
        .ok_or_else(|| Error::from_reason("Failed to convert to BigUint"))?;

    // Convert to ark_ff::BigInt limbs
    let mut limbs = positive_biguint.to_u64_digits();

    if limbs.len() > N {
        return Err(Error::from_reason("Value exceeds fixed limb size"));
    }

    limbs.resize(N, 0);
    let u64_array: [u64; N] = limbs
        .try_into()
        .map_err(|_| Error::from_reason("Limb count mismatch"))?;

    Ok(BigInt::new(u64_array))
}

/// Public API: converts NAPI BigInt to ark_ff BigInt with modular reduction
pub fn napi_bigint_to_ark_bigint<F, const N: usize>(bigint: NapiBigInt) -> NapiResult<BigInt<N>>
where
    F: PrimeField<BigInt = BigInt<N>>,
{
    let num_bigint = napi_bigint_to_num_bigint(bigint)?;
    num_bigint_to_ark_bigint::<F, N>(num_bigint)
}

/// Converts a NumBigInt to NAPI BigInt
pub fn num_bigint_to_napi(num: &NumBigInt) -> NapiBigInt {
    let (sign, bytes) = num.to_bytes_le();
    let mut words = Vec::new();

    for chunk in bytes.chunks(8) {
        let mut word = 0u64;
        for (i, &byte) in chunk.iter().enumerate() {
            word |= (byte as u64) << (i * 8);
        }
        words.push(word);
    }

    if words.is_empty() {
        words.push(0);
    }

    NapiBigInt {
        sign_bit: sign == Sign::Minus,
        words,
    }
}

/// Converts an ark_ff::BigInt to a NumBigInt
pub fn ark_bigint_to_num_bigint<const N: usize>(ark: &BigInt<N>) -> NumBigInt {
    let limbs = ark.as_ref();
    let biguint = BigUint::from_slice(
        &limbs
            .iter()
            .flat_map(|&limb| [limb as u32, (limb >> 32) as u32])
            .collect::<Vec<_>>(),
    );
    NumBigInt::from(biguint)
}

/// Converts an ark_ff::BigInt to a NAPI BigInt
pub fn ark_bigint_to_napi<const N: usize>(ark: &BigInt<N>) -> NapiBigInt {
    let num_bigint = ark_bigint_to_num_bigint(ark);
    num_bigint_to_napi(&num_bigint)
}
