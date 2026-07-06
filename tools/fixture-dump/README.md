# fixture-dump

Fixtures and test vectors for the Lean formalization (`formal/`), recorded from
proof-systems itself: every value comes from the production Rust code the Lean modules
transcribe, so the `formal/scripts/check_*` drivers validate the transcriptions against
exactly what downstream consumers run.

## Building and running

The crate path-depends on the proof-systems submodule and needs its pinned toolchain
(1.92; the snarky root pins 1.88, which is too old — the crate's own `rust-toolchain.toml`
selects the right one when invoked via rustup):

```sh
cd tools/fixture-dump
rustup run 1.92 cargo build --release
```

Two binaries, both deterministic (seeded ChaCha20), both writing into `formal/`:

```sh
# Sponge-layer artifacts: constants + vectors
./target/release/sponge_dump ../../formal/Kimchi/Sponge ../../formal/fixtures

# IPA opening-proof fixtures (wire data + layer-check transcript values)
./target/release/ipa_dump ../../formal/fixtures
```

## What each binary emits

`sponge_dump`:

| artifact | contents | checked by |
|---|---|---|
| `Kimchi/Sponge/PoseidonConstantsFq.lean` / `…Fp.lean` | the `fq_kimchi` / `fp_kimchi` Poseidon tables, as generated committed Lean constants | (consumed by the library) |
| `fixtures/poseidon_{fq,fp}_vectors.json` | `ArithmeticSponge` absorb/squeeze traces, both Pasta fields | `scripts/check_sponge_vectors.sh` |
| `fixtures/fq_sponge_vectors.json` / `…_pallas_….json` | `DefaultFqSponge` op traces — every ordered pair of the six op kinds plus mixed sequences | `scripts/check_fq_sponge.sh` |
| `fixtures/group_map_vectors.json` | SvdW `to_group` vectors | `scripts/check_fq_sponge.sh` |

`ipa_dump`:

| artifact | contents | checked by |
|---|---|---|
| `fixtures/ipa_opening_vesta.json` | a single opening (1 poly × 1 point) | `scripts/check_ipa_fixture.sh` (wire fields only), `scripts/check_ipa_transcript.sh` (recorded transcript values) |
| `fixtures/ipa_batch_vesta.json` | a batched opening (2 polys × 2 points) | same |

`ipa_dump` is a thin wrapper over the production prover/verifier: proofs come from
`SRS::commit`/`SRS::open`, the batched `SRS::verify` is asserted at dump time, and the
harness is proof-systems' own `tests/ipa_commitment.rs::test_opening_proof`. The recorded
transcript values (`u_base`, `chal`, `c`) exist only for layer bisection — the end-to-end
check derives them in Lean and never reads them.

## When to regenerate

On a proof-systems submodule bump (or when adding vector coverage). Regeneration is
byte-stable for unchanged sources — a diff after regenerating is itself a drift check.
Commit the regenerated constants and fixtures together with the bump.
