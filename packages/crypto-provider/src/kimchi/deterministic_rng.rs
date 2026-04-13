//! Deterministic RNG for kimchi proof creation.
//!
//! Sister module to `mina/src/lib/crypto/proof-systems/kimchi-stubs/src/deterministic_rng.rs`.
//! Both wrappers around the kimchi prover (OCaml's kimchi-stubs and PureScript's
//! crypto-provider) seed the SAME `ChaCha20Rng` from the same env var so that
//! `ProverProof::create` draws identical bytes on both sides — required for
//! the byte-identical trace reproduction tests.
//!
//! The env var must be set; missing or unparseable values panic loudly. We
//! intentionally do NOT fall back to `OsRng` — silent non-determinism is the
//! exact problem this module exists to eliminate.

use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

const SEED_ENV_VAR: &str = "KIMCHI_DETERMINISTIC_SEED";

/// Build a fresh `ChaCha20Rng` seeded from `KIMCHI_DETERMINISTIC_SEED`.
///
/// Each call returns an independently-seeded RNG with the SAME starting
/// state, so consecutive proof creations begin from the same RNG draws.
/// This matches the OCaml-side helper bit-for-bit.
pub fn make_rng() -> ChaCha20Rng {
    let raw = std::env::var(SEED_ENV_VAR).unwrap_or_else(|_| {
        panic!(
            "{} environment variable must be set to a u64 seed; \
             crypto-provider has been patched to require deterministic RNG. \
             See packages/pickles/test/Test/Pickles/Main.purs for context.",
            SEED_ENV_VAR
        )
    });
    let seed: u64 = raw.parse().unwrap_or_else(|e| {
        panic!(
            "{} must parse as u64, got `{}`: {}",
            SEED_ENV_VAR, raw, e
        )
    });
    ChaCha20Rng::seed_from_u64(seed)
}
