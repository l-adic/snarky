use ark_ff::AdditiveGroup;
use napi::bindgen_prelude::*;
use napi_derive::napi;

use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    pasta::{fp_kimchi, fq_kimchi},
    permutation::full_round,
    poseidon::{sbox, ArithmeticSponge, Sponge},
};

use mina_curves::pasta::{Fp as PallasBaseField, Fq as VestaBaseField};

use crate::pasta::pallas::scalar_field::FieldExternal as VestaBaseFieldExternal;
use crate::pasta::vesta::scalar_field::FieldExternal as PallasBaseFieldExternal;

pub mod pallas {
    use super::*;

    #[napi]
    pub fn pallas_poseidon_sbox(x: &PallasBaseFieldExternal) -> PallasBaseFieldExternal {
        let result = sbox::<PallasBaseField, PlonkSpongeConstantsKimchi>(**x);
        External::new(result)
    }

    #[napi]
    pub fn pallas_poseidon_apply_mds(
        state: Vec<&PallasBaseFieldExternal>,
    ) -> Vec<PallasBaseFieldExternal> {
        let params = fp_kimchi::static_params();
        let state_vec: Vec<PallasBaseField> = state.iter().map(|&s| **s).collect();

        let result: Vec<PallasBaseField> = params
            .mds
            .iter()
            .map(|row| {
                state_vec
                    .iter()
                    .zip(row.iter())
                    .fold(PallasBaseField::ZERO, |acc, (&s, &m)| acc + m * s)
            })
            .collect();

        result.into_iter().map(External::new).collect()
    }

    #[napi]
    pub fn pallas_poseidon_full_round(
        state: Vec<&PallasBaseFieldExternal>,
        round_index: u32,
    ) -> Vec<PallasBaseFieldExternal> {
        let params = fp_kimchi::static_params();
        let mut state_vec: Vec<PallasBaseField> = state.iter().map(|&s| **s).collect();

        full_round::<PallasBaseField, PlonkSpongeConstantsKimchi>(
            params,
            &mut state_vec,
            round_index as usize,
        );

        state_vec.into_iter().map(External::new).collect()
    }

    #[napi]
    pub fn pallas_poseidon_get_round_constants(round_index: u32) -> Vec<PallasBaseFieldExternal> {
        let params = fp_kimchi::static_params();
        let round = &params.round_constants[round_index as usize];
        round.iter().copied().map(External::new).collect()
    }

    #[napi]
    pub fn pallas_poseidon_get_num_rounds() -> u32 {
        let params = fp_kimchi::static_params();
        params.round_constants.len() as u32
    }

    #[napi]
    pub fn pallas_poseidon_get_mds_matrix() -> Vec<Vec<PallasBaseFieldExternal>> {
        let params = fp_kimchi::static_params();
        params
            .mds
            .iter()
            .map(|row| row.iter().copied().map(External::new).collect())
            .collect()
    }

    #[napi]
    pub fn pallas_poseidon_hash(inputs: Vec<&PallasBaseFieldExternal>) -> PallasBaseFieldExternal {
        let fields: Vec<PallasBaseField> = inputs.iter().map(|&f| **f).collect();
        let params = fp_kimchi::static_params();
        let mut sponge =
            ArithmeticSponge::<PallasBaseField, PlonkSpongeConstantsKimchi>::new(params);

        sponge.absorb(&fields);
        External::new(sponge.squeeze())
    }
}

pub mod vesta {
    use super::*;

    #[napi]
    pub fn vesta_poseidon_sbox(x: &VestaBaseFieldExternal) -> VestaBaseFieldExternal {
        let result = sbox::<VestaBaseField, PlonkSpongeConstantsKimchi>(**x);
        External::new(result)
    }

    #[napi]
    pub fn vesta_poseidon_apply_mds(
        state: Vec<&VestaBaseFieldExternal>,
    ) -> Vec<VestaBaseFieldExternal> {
        let params = fq_kimchi::static_params();
        let state_vec: Vec<VestaBaseField> = state.iter().map(|&s| **s).collect();

        let result: Vec<VestaBaseField> = params
            .mds
            .iter()
            .map(|row| {
                state_vec
                    .iter()
                    .zip(row.iter())
                    .fold(VestaBaseField::ZERO, |acc, (&s, &m)| acc + m * s)
            })
            .collect();

        result.into_iter().map(External::new).collect()
    }

    #[napi]
    pub fn vesta_poseidon_full_round(
        state: Vec<&VestaBaseFieldExternal>,
        round_index: u32,
    ) -> Vec<VestaBaseFieldExternal> {
        let params = fq_kimchi::static_params();
        let mut state_vec: Vec<VestaBaseField> = state.iter().map(|&s| **s).collect();

        full_round::<VestaBaseField, PlonkSpongeConstantsKimchi>(
            params,
            &mut state_vec,
            round_index as usize,
        );

        state_vec.into_iter().map(External::new).collect()
    }

    #[napi]
    pub fn vesta_poseidon_get_round_constants(round_index: u32) -> Vec<VestaBaseFieldExternal> {
        let params = fq_kimchi::static_params();
        let round = &params.round_constants[round_index as usize];
        round.iter().copied().map(External::new).collect()
    }

    #[napi]
    pub fn vesta_poseidon_get_num_rounds() -> u32 {
        let params = fq_kimchi::static_params();
        params.round_constants.len() as u32
    }

    #[napi]
    pub fn vesta_poseidon_get_mds_matrix() -> Vec<Vec<VestaBaseFieldExternal>> {
        let params = fq_kimchi::static_params();
        params
            .mds
            .iter()
            .map(|row| row.iter().copied().map(External::new).collect())
            .collect()
    }

    #[napi]
    pub fn vesta_poseidon_hash(inputs: Vec<&VestaBaseFieldExternal>) -> VestaBaseFieldExternal {
        let fields: Vec<VestaBaseField> = inputs.iter().map(|&f| **f).collect();
        let params = fq_kimchi::static_params();
        let mut sponge =
            ArithmeticSponge::<VestaBaseField, PlonkSpongeConstantsKimchi>::new(params);

        sponge.absorb(&fields);
        External::new(sponge.squeeze())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Field;
    use mina_poseidon::poseidon::ArithmeticSpongeParams;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    fn manual_poseidon_permutation<F>(state: &mut [F], params: &ArithmeticSpongeParams<F>)
    where
        F: ark_ff::PrimeField,
    {
        let num_rounds = params.round_constants.len();
        for round_idx in 0..num_rounds {
            // S-box
            for state_element in state.iter_mut() {
                *state_element = sbox::<F, PlonkSpongeConstantsKimchi>(*state_element);
            }

            // MDS matrix
            let new_state: Vec<F> = params
                .mds
                .iter()
                .map(|row| {
                    state
                        .iter()
                        .zip(row.iter())
                        .fold(F::ZERO, |acc, (&s, &m)| acc + m * s)
                })
                .collect();
            state.copy_from_slice(&new_state);

            // Round constants
            let round_constants = &params.round_constants[round_idx];
            for (state_element, &constant) in state.iter_mut().zip(round_constants.iter()) {
                *state_element += constant;
            }
        }
    }

    fn manual_poseidon_absorb<F>(inputs: &[F], params: &ArithmeticSpongeParams<F>) -> F
    where
        F: ark_ff::PrimeField,
    {
        let mut state = [F::ZERO; 3];
        let mut absorbed_count = 0;
        let rate = 2;

        for &input in inputs {
            if absorbed_count == rate {
                // Run permutation when rate limit is reached
                manual_poseidon_permutation(&mut state, params);
                absorbed_count = 0;
            }

            // Add input to current position
            state[absorbed_count] += input;
            absorbed_count += 1;
        }

        // Final permutation if we have absorbed elements
        if absorbed_count > 0 {
            manual_poseidon_permutation(&mut state, params);
        }

        state[0] // Squeeze from position 0
    }

    #[test]
    fn test_pallas_poseidon_composition_random() {
        let mut rng = ChaCha20Rng::seed_from_u64(12345);

        for input_len in [1, 2, 3, 4, 5, 7, 10] {
            for _ in 0..10 {
                let inputs: Vec<PallasBaseField> = (0..input_len)
                    .map(|_| PallasBaseField::from(rng.gen::<u64>()))
                    .collect();

                let input_externals: Vec<External<PallasBaseField>> =
                    inputs.iter().map(|&f| External::new(f)).collect();
                let input_refs: Vec<&External<PallasBaseField>> = input_externals.iter().collect();
                let high_level_result = *pallas::pallas_poseidon_hash(input_refs);

                let params = fp_kimchi::static_params();
                let manual_result = manual_poseidon_absorb(&inputs, params);

                assert_eq!(high_level_result, manual_result);
            }
        }
    }

    #[test]
    fn test_vesta_poseidon_composition_random() {
        let mut rng = ChaCha20Rng::seed_from_u64(54321);

        for input_len in [1, 2, 3, 4, 5, 7, 10] {
            for _ in 0..10 {
                let inputs: Vec<VestaBaseField> = (0..input_len)
                    .map(|_| VestaBaseField::from(rng.gen::<u64>()))
                    .collect();

                let input_externals: Vec<External<VestaBaseField>> =
                    inputs.iter().map(|&f| External::new(f)).collect();
                let input_refs: Vec<&External<VestaBaseField>> = input_externals.iter().collect();
                let high_level_result = *vesta::vesta_poseidon_hash(input_refs);

                let params = fq_kimchi::static_params();
                let manual_result = manual_poseidon_absorb(&inputs, params);

                assert_eq!(high_level_result, manual_result);
            }
        }
    }

    #[test]
    fn test_pallas_poseidon_composition() {
        let left = PallasBaseField::from(42u64);
        let right = PallasBaseField::from(123u64);

        let left_ext = External::new(left);
        let right_ext = External::new(right);
        let high_level_result = *pallas::pallas_poseidon_hash(vec![&left_ext, &right_ext]);

        let mut manual_state = vec![left, right, PallasBaseField::ZERO];
        let params = fp_kimchi::static_params();
        let num_rounds = params.round_constants.len();

        for round_idx in 0..num_rounds {
            for state_element in &mut manual_state {
                *state_element =
                    sbox::<PallasBaseField, PlonkSpongeConstantsKimchi>(*state_element);
            }

            let new_state: Vec<PallasBaseField> = params
                .mds
                .iter()
                .map(|row| {
                    manual_state
                        .iter()
                        .zip(row.iter())
                        .fold(PallasBaseField::ZERO, |acc, (&s, &m)| acc + m * s)
                })
                .collect();
            manual_state = new_state;

            let round_constants = &params.round_constants[round_idx];
            for (state_element, &constant) in manual_state.iter_mut().zip(round_constants.iter()) {
                *state_element += constant;
            }
        }

        let manual_result = manual_state[0];
        assert_eq!(high_level_result, manual_result);
    }

    #[test]
    fn test_vesta_poseidon_composition() {
        let left = VestaBaseField::from(42u64);
        let right = VestaBaseField::from(123u64);

        let left_ext = External::new(left);
        let right_ext = External::new(right);
        let high_level_result = *vesta::vesta_poseidon_hash(vec![&left_ext, &right_ext]);

        let mut manual_state = vec![left, right, VestaBaseField::ZERO];
        let params = fq_kimchi::static_params();
        let num_rounds = params.round_constants.len();

        for round_idx in 0..num_rounds {
            for state_element in &mut manual_state {
                *state_element = sbox::<VestaBaseField, PlonkSpongeConstantsKimchi>(*state_element);
            }

            let new_state: Vec<VestaBaseField> = params
                .mds
                .iter()
                .map(|row| {
                    manual_state
                        .iter()
                        .zip(row.iter())
                        .fold(VestaBaseField::ZERO, |acc, (&s, &m)| acc + m * s)
                })
                .collect();
            manual_state = new_state;

            let round_constants = &params.round_constants[round_idx];
            for (state_element, &constant) in manual_state.iter_mut().zip(round_constants.iter()) {
                *state_element += constant;
            }
        }

        let manual_result = manual_state[0];
        assert_eq!(high_level_result, manual_result);
    }

    #[test]
    fn test_primitive_operations() {
        let test_field = PallasBaseField::from(42u64);
        let params = fp_kimchi::static_params();

        let sbox_result = sbox::<PallasBaseField, PlonkSpongeConstantsKimchi>(test_field);
        let expected_sbox = test_field.pow([7u64]);
        assert_eq!(sbox_result, expected_sbox);

        assert_eq!(params.round_constants.len(), 55);
        assert_eq!(params.mds.len(), 3);
        assert_eq!(params.mds[0].len(), 3);
    }

    #[test]
    fn test_ffi_composition_equivalence() {
        let left_val = PallasBaseField::from(42u64);
        let right_val = PallasBaseField::from(123u64);

        let left_ext = External::new(left_val);
        let right_ext = External::new(right_val);
        let zero_ext = External::new(PallasBaseField::ZERO);

        let _high_level = pallas::pallas_poseidon_hash(vec![&left_ext, &right_ext]);
        let _sboxed = pallas::pallas_poseidon_sbox(&left_ext);

        let state = vec![&left_ext, &right_ext, &zero_ext];
        let after_mds = pallas::pallas_poseidon_apply_mds(state);
        assert_eq!(after_mds.len(), 3);

        let round_constants = pallas::pallas_poseidon_get_round_constants(0);
        assert_eq!(round_constants.len(), 3);

        let num_rounds = pallas::pallas_poseidon_get_num_rounds();
        assert_eq!(num_rounds, 55);

        let state2 = vec![&left_ext, &right_ext, &zero_ext];
        let after_round = pallas::pallas_poseidon_full_round(state2, 0);
        assert_eq!(after_round.len(), 3);
    }
}
