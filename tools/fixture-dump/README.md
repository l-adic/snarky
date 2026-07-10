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

# IPA opening-proof fixtures (wire format only)
./target/release/ipa_dump ../../formal/fixtures

# Permutation-argument fixture (wired circuit, production accumulator)
./target/release/perm_dump ../../formal/fixtures
```

## What each binary emits

`sponge_dump`:

| artifact | contents | checked by |
|---|---|---|
| `Kimchi/Sponge/PoseidonConstantsFq.lean` / `…Fp.lean` | the `fq_kimchi` / `fp_kimchi` Poseidon tables, as generated committed Lean constants | (consumed by the library) |
| `fixtures/poseidon_{fq,fp}_vectors.json` | `ArithmeticSponge` absorb/squeeze traces, both Pasta fields | `scripts/check_sponge_vectors.sh` |
| `fixtures/fq_sponge_vectors.json` / `…_pallas_….json` | `DefaultFqSponge` op traces — every ordered pair of the six op kinds plus mixed sequences | `scripts/check_fq_sponge.sh` |
| `fixtures/group_map_vectors.json` / `…_pallas_….json` | SvdW `to_group` vectors, both curves | `scripts/check_fq_sponge.sh` |

`ipa_dump`:

| artifact | contents | checked by |
|---|---|---|
| `fixtures/ipa_opening_{vesta,pallas}.json` | a single opening (1 poly × 1 point) | `scripts/check_ipa_fixture.sh` |
| `fixtures/ipa_batch_{vesta,pallas}.json` | a batched opening (2 polys × 2 points) | same |
| `fixtures/ipa_chunked{2,3}_{vesta,pallas}.json` | combine-then-open chunked openings (1 poly × 1 point × 2/3 chunks; the production `chunk_commitment(x^n)` combination recorded per poly) | same |
| `fixtures/ipa_chunked_{batch,ragged}_{vesta,pallas}.json` | chunked batches (2 polys × 2 points, uniform 2/2 and ragged 1/3 chunk counts; multi-chunk `PolyComm`s through the batch path, with the production `combine_commitments`/`combined_inner_product` targets recorded) | same |

`perm_dump`:

| artifact | contents | checked by |
|---|---|---|
| `fixtures/perm_vesta.json` | a wired circuit's permutation data — shifts, sigma columns, witness, and the `perm_aggreg` accumulator over the domain (production prove+verify asserted) | `scripts/check_perm_fixture.sh` |

`index_dump`:

| artifact | contents | checked by |
|---|---|---|
| `fixtures/index_vesta.json` | a mixed-gate circuit (public, generic, Poseidon, CompleteAdd, EndoMulScalar; wired) — the padded gate table, domain/permutation constants, witness, and the production derived columns (kimchi's row checker and prove+verify asserted) | `scripts/check_index_fixture.sh` |

`ipa_dump` is a thin wrapper over the production prover/verifier: proofs come from
`SRS::commit`/`SRS::open`, the batched `SRS::verify` is asserted at dump time, and the
harness is proof-systems' own `tests/ipa_commitment.rs::test_opening_proof`. Nothing
transcript-derived is recorded: the Lean verifier re-derives the `U` base and every
Fiat-Shamir challenge from the wire data through its own sponge layer.

## When to regenerate

On a proof-systems submodule bump (or when adding vector coverage). Regeneration is
byte-stable for unchanged sources — a diff after regenerating is itself a drift check.
Commit the regenerated constants and fixtures together with the bump.
