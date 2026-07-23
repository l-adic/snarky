# fixture-dump

Fixtures and test vectors for the Lean formalization (`formal/`), recorded from
proof-systems itself: every value comes from the production Rust code the Lean modules
transcribe, so the per-package `formal/*/scripts/check_*` drivers validate the
transcriptions against exactly what downstream consumers run.

## Building and running

The crate path-depends on the proof-systems submodule and needs its pinned toolchain
(1.92; the snarky root pins 1.88, which is too old — the crate's own `rust-toolchain.toml`
selects the right one when invoked via rustup):

```sh
cd tools/fixture-dump
rustup run 1.92 cargo build --release
```

Nine binaries, all deterministic (seeded ChaCha20). `formal/` is a workspace of
packages, each owning its fixtures — every binary takes its output directory as an
argument, and the right target depends on which package checks the artifact. Several
binaries emit MORE THAN ONE fixture from a single invocation (`index_dump` writes three
indices; `kimchi_proof_dump` writes two proof serializations; `kimchi_proof_dump_nc2`
writes both Pasta curves):

```sh
# Sponge-layer artifacts: constants + vectors  →  the poseidon package
./target/release/sponge_dump ../../formal/poseidon/Poseidon ../../formal/poseidon/fixtures

# IPA opening-proof fixtures (wire format only)  →  the bulletproof-pcs package
./target/release/ipa_dump ../../formal/bulletproof-pcs/fixtures

# kimchi-protocol fixtures  →  the kimchi package
./target/release/perm_dump ../../formal/kimchi/fixtures
./target/release/index_dump ../../formal/kimchi/fixtures
./target/release/linearization_dump ../../formal/kimchi/fixtures
./target/release/kimchi_proof_dump ../../formal/kimchi/fixtures
./target/release/kimchi_proof_dump_nc2 ../../formal/kimchi/fixtures
./target/release/kimchi_proof_dump_nc8 ../../formal/kimchi/fixtures
./target/release/kimchi_proof_dump_2pub ../../formal/kimchi/fixtures
```

> **Caveat (`sponge_dump`'s Lean output):** the generated-constants half of
> `sponge_dump` predates the `formal/` package split — it still writes
> `PoseidonConstantsF{q,p}.lean` under a `Kimchi.Sponge.*` namespace, while the
> committed files are `formal/poseidon/Poseidon/Constants{Fq,Fp}.lean` under
> `Poseidon.*`. On regeneration, rename the files and namespaces to match the
> committed layout (the constant values are what the regeneration refreshes). The
> JSON vector output is current.

## What each binary emits

Paths below are relative to `formal/`.

`sponge_dump`:

| artifact | contents | checked by |
|---|---|---|
| `poseidon/Poseidon/Constants{Fq,Fp}.lean` | the `fq_kimchi` / `fp_kimchi` Poseidon tables, as generated committed Lean constants (see the caveat above on the emitted names) | (consumed by the library) |
| `poseidon/fixtures/poseidon_{fq,fp}_vectors.json` | `ArithmeticSponge` absorb/squeeze traces, both Pasta fields | `poseidon/scripts/check_sponge_vectors.sh` |
| `poseidon/fixtures/fq_sponge_vectors.json` / `…_pallas_….json` | `DefaultFqSponge` op traces — every ordered pair of the six op kinds plus mixed sequences | `poseidon/scripts/check_fq_sponge.sh` |
| `poseidon/fixtures/group_map_vectors.json` / `…_pallas_….json` | SvdW `to_group` vectors, both curves | `poseidon/scripts/check_fq_sponge.sh` |

`ipa_dump`:

| artifact | contents | checked by |
|---|---|---|
| `bulletproof-pcs/fixtures/ipa_opening_{vesta,pallas}.json` | a single opening (1 poly × 1 point) | `bulletproof-pcs/scripts/check_ipa_fixture.sh` |
| `bulletproof-pcs/fixtures/ipa_batch_{vesta,pallas}.json` | a batched opening (2 polys × 2 points) | same |
| `bulletproof-pcs/fixtures/ipa_chunked{2,3}_{vesta,pallas}.json` | combine-then-open chunked openings (1 poly × 1 point × 2/3 chunks; the production `chunk_commitment(x^n)` combination recorded per poly) | same |
| `bulletproof-pcs/fixtures/ipa_chunked_{batch,ragged}_{vesta,pallas}.json` | chunked batches (2 polys × 2 points, uniform 2/2 and ragged 1/3 chunk counts; multi-chunk `PolyComm`s through the batch path, with the production `combine_commitments`/`combined_inner_product` targets recorded) | same |

`perm_dump`:

| artifact | contents | checked by |
|---|---|---|
| `kimchi/fixtures/perm_vesta.json` | a wired circuit's permutation data — shifts, sigma columns, witness, and the `perm_aggreg` accumulator over the domain (production prove+verify asserted) | `kimchi/scripts/check_perm_fixture.sh` |

`index_dump` (three fixtures — the mixed-gate circuit, public/generic/Poseidon/CompleteAdd/EndoMulScalar and wired; the padded gate table, domain/permutation constants, witness, and the production derived columns; kimchi's row checker and prove+verify asserted for each):

| artifact | contents | checked by |
|---|---|---|
| `kimchi/fixtures/index_vesta.json` | the UNCHUNKED regression (Vesta, `override_srs_size = None`, one chunk, `zk_rows = 3`, so the σ interior-mask range is empty) | `kimchi/scripts/check_index_fixture.sh`, `kimchi/scripts/check_vk_correspond.sh` |
| `kimchi/fixtures/index_vesta_nc2.json` / `…index_pallas_nc2.json` | the CHUNKED twins on both curves (`override_srs_size = n/2`, two chunks, `zk_rows = 5`, so the σ interior-mask range is NONEMPTY — rows 29, 30 at `n = 32`; the index model's σ-zeroing branch is pinned row-by-row here) | `kimchi/scripts/check_index_fixture.sh`; the Pallas one also `kimchi/scripts/check_vk_correspond.sh` |

`linearization_dump`:

| artifact | contents | checked by |
|---|---|---|
| `kimchi/fixtures/linearization_vesta.json` | the verifier's scalar side of a real proof over the same mixed-gate circuit — challenges, combined evaluations at ζ/ζω, and the production outputs (`ft_eval0`, `perm_scalars`, the token-evaluated constant term, per-gate combined constraints) | `kimchi/scripts/check_linearization.sh` |

`kimchi_proof_dump` (two serializations of ONE proof — a complete kimchi wire proof + verifier key over the mixed-gate circuit, same seed and domain-sized SRS as `linearization_vesta.json`: all commitments, uncombined evaluations, opening proof, public input, and the VK data incl. Lagrange-basis commitments, both endo coefficients, and the verifier-index digest):

| artifact | contents | checked by |
|---|---|---|
| `kimchi/fixtures/kimchi_proof_vesta.json` | the deployed wire form — WITHOUT `evals_public` (o1js / OCaml `to_repr` drop the public-eval chunks at `nc = 1`; the verifier recomputes them barycentrically) | `kimchi/scripts/check_kimchi_verifier.sh`, `kimchi/scripts/check_vk_correspond.sh` |
| `kimchi/fixtures/kimchi_proof_vesta_pub.json` | the SAME proof WITH the proof-carried `evals_public` — `ProverProof::create` always populates them and the verifier consumes carried evals at any `nc` (verifier.rs:332), so the carried-at-`nc = 1` case is production-reachable; exercises the Lean verifier's `PubEvalSrc.carried` branch at one chunk | `kimchi/scripts/check_kimchi_verifier.sh` |

`kimchi_proof_dump_nc2`:

| artifact | contents | checked by |
|---|---|---|
| `kimchi/fixtures/kimchi_proof_{vesta,pallas}_nc2.json` | the CHUNKED twins: the same mixed circuit and seed re-proved over a half-domain SRS (`override_srs_size = n/2` → `max_poly_size = n/2`, `nc = 2`, chunked `zk_rows`); every commitment dumped as its chunk vector, every evaluation as `[[ζ-chunks],[ζω-chunks]]`, plus the proof-carried public evaluations that production requires at `nc > 1` | `kimchi/scripts/check_kimchi_verifier.sh`; the Vesta one also `kimchi/scripts/check_vk_correspond.sh` |

`kimchi_proof_dump_nc2` additionally writes `kimchi_proof_{vesta,pallas}_nc2_debug.json`
sidecars next to the fixtures (the verifier's intermediate oracle values, for localizing
a Lean-side divergence layer by layer). They are debugging aids, gitignored
(`formal/kimchi/fixtures/.gitignore`), never checked in.

`kimchi_proof_dump_nc8`:

| artifact | contents | checked by |
|---|---|---|
| `kimchi/fixtures/kimchi_proof_vesta_nc8.json` | an `nc = 8` proof (nc > 2 parameter coverage): the same mixed circuit and seed re-proved over an `max_poly_size = 8` SRS. There the chunked `zk_rows` (19) grow the domain to `n = 64`, so `nc = n / max_poly_size = 8` with a full `56`-chunk quotient, and `max_poly_size = n/8 ≠ n/2`. Same chunk-array encoding as the `nc = 2` twins. (`nc = 3` is unproducible — a non-power-of-two `max_poly_size` misaligns the segment chunking and the production prover rejects it with `WrongBlinders`; `nc = 4` would need a larger circuit.) No debug sidecar. | `kimchi/scripts/check_kimchi_verifier.sh` |

`kimchi_proof_dump_2pub`:

| artifact | contents | checked by |
|---|---|---|
| `kimchi/fixtures/kimchi_proof_vesta_2pub.json` | a `public_count = 2` proof (`nc = 1`), over the two-public-input circuit (`two_public_circuit`): the mixed circuit's gate set with two public rows and a generic add of the two inputs. Same one-chunk encoding as `kimchi_proof_vesta.json`, with `public` carrying both inputs, so the verifier's public-commitment MSM and barycentric public-evaluation recomputation run over two elements. | `kimchi/scripts/check_kimchi_verifier.sh` |

`ipa_dump` is a thin wrapper over the production prover/verifier: proofs come from
`SRS::commit`/`SRS::open`, the batched `SRS::verify` is asserted at dump time, and the
harness is proof-systems' own `tests/ipa_commitment.rs::test_opening_proof`. Nothing
transcript-derived is recorded: the Lean verifier re-derives the `U` base and every
Fiat-Shamir challenge from the wire data through its own sponge layer.

## When to regenerate

On a proof-systems submodule bump (or when adding vector coverage). Regeneration is
byte-stable for unchanged sources — a diff after regenerating is itself a drift check.
Commit the regenerated constants and fixtures together with the bump.
