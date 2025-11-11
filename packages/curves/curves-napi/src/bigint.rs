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

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use napi::bindgen_prelude::BigInt as NapiBigInt;
    use num_bigint::BigInt as NumBigInt;
    use proptest::prelude::*;

    // --- Inverse Functions ---


    // --- Property Tests ---

    proptest! {
        #[test]
        fn prop_napi_roundtrip(value: i64) {
            let original = NumBigInt::from(value);
            let napi = num_bigint_to_napi(&original);
            let recovered = napi_bigint_to_num_bigint(napi).unwrap();
            prop_assert_eq!(original, recovered);
        }

        #[test]
        fn prop_napi_roundtrip_large(high: u64, low: u64) {
            // Test with numbers that require multiple u64 words
            let bytes = [
                low.to_le_bytes(),
                high.to_le_bytes(),
            ].concat();
            let original = NumBigInt::from_bytes_le(Sign::Plus, &bytes);

            let napi = num_bigint_to_napi(&original);
            let recovered = napi_bigint_to_num_bigint(napi).unwrap();
            prop_assert_eq!(original, recovered);
        }

        #[test]
        fn prop_ark_preserves_small_positive(value in 0u64..1_000_000) {
            let original = NumBigInt::from(value);
            let ark: BigInt<4> = num_bigint_to_ark_bigint::<Fr, 4>(original.clone()).unwrap();
            let recovered = ark_bigint_to_num_bigint(ark);
            prop_assert_eq!(original, recovered);
        }

        #[test]
        fn prop_ark_reduces_modulo(value: i64, multiplier in 0i32..10) {
            let modulus: NumBigInt = Fr::MODULUS.into();
            let input = NumBigInt::from(value) + &modulus * multiplier;

            let ark: BigInt<4> = num_bigint_to_ark_bigint::<Fr, 4>(input).unwrap();
            let result = ark_bigint_to_num_bigint(ark);

            // Result should be in range [0, modulus)
            prop_assert!(result >= NumBigInt::from(0));
            prop_assert!(result < modulus);
        }

        #[test]
        fn prop_ark_negative_becomes_positive(value in 1i64..1_000_000) {
            let input = NumBigInt::from(-value);
            let ark: BigInt<4> = num_bigint_to_ark_bigint::<Fr, 4>(input).unwrap();
            let result = ark_bigint_to_num_bigint(ark);

            // Negative inputs should produce positive outputs
            prop_assert!(result > NumBigInt::from(0));

            // And should equal modulus - value
            let modulus: NumBigInt = Fr::MODULUS.into();
            let expected = modulus - NumBigInt::from(value);
            prop_assert_eq!(result, expected);
        }

        #[test]
        fn prop_full_pipeline_idempotent(value in 0u64..1_000_000) {
            // Converting twice should give the same result
            let original = NumBigInt::from(value);

            let napi1 = num_bigint_to_napi(&original);
            let ark1: BigInt<4> = napi_bigint_to_ark_bigint::<Fr, 4>(napi1).unwrap();

            let napi2 = num_bigint_to_napi(&original);
            let ark2: BigInt<4> = napi_bigint_to_ark_bigint::<Fr, 4>(napi2).unwrap();

            prop_assert_eq!(ark1, ark2);
        }

        #[test]
        fn prop_modular_arithmetic_consistent(a: i32, b: i32) {
            let modulus: NumBigInt = Fr::MODULUS.into();

            let num_a = NumBigInt::from(a);
            let num_b = NumBigInt::from(b);

            // (a + b) mod p == ((a mod p) + (b mod p)) mod p
            let sum = &num_a + &num_b;
            let ark_sum: BigInt<4> = num_bigint_to_ark_bigint::<Fr, 4>(sum).unwrap();
            let result_sum = ark_bigint_to_num_bigint(ark_sum);

            let ark_a: BigInt<4> = num_bigint_to_ark_bigint::<Fr, 4>(num_a).unwrap();
            let ark_b: BigInt<4> = num_bigint_to_ark_bigint::<Fr, 4>(num_b).unwrap();
            let reduced_a = ark_bigint_to_num_bigint(ark_a);
            let reduced_b = ark_bigint_to_num_bigint(ark_b);
            let sum_reduced = (&reduced_a + &reduced_b).mod_floor(&modulus);

            prop_assert_eq!(result_sum, sum_reduced);
        }
    }

    // A few hand-picked edge cases that are good to explicitly test
    #[test]
    fn test_edge_cases() {
        // Zero
        let zero = NumBigInt::from(0);
        let napi = num_bigint_to_napi(&zero);
        assert_eq!(napi_bigint_to_num_bigint(napi).unwrap(), zero);

        // Exactly the modulus
        let modulus: NumBigInt = Fr::MODULUS.into();
        let ark: BigInt<4> = num_bigint_to_ark_bigint::<Fr, 4>(modulus).unwrap();
        let result = ark_bigint_to_num_bigint(ark);
        assert_eq!(result, NumBigInt::from(0));
    }
}
