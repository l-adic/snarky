import Bulletproof.Protocol
import Bulletproof.Wire
import Bulletproof.Soundness
import Bulletproof.Reflection

/-!
# Bulletproof — the IPA polynomial commitment scheme

Root module of the `Bulletproof` library: the inner-product-argument polynomial
commitment as deployed by kimchi. The abstract scheme and its soundness (`Basic`,
`Batch`, `Chunk`, `Verify`, `Soundness/**` — opening soundness, batched opening
soundness, binding = no-DL-relation, the chunked width pass); the executable wire
verifier over the Pasta curves, driven by the Poseidon Fq-sponge (`Wire`); the
Fiat–Shamir instantiation — the `poseidon_fiat_shamir_{vesta,pallas}` axioms and the
per-curve headline soundness `ipa{Vesta,Pallas}_sound` (`Reflection`). The fixture
decoders for the proof-systems wire data live in the separate `BulletproofFixture`
target, driven by `scripts/check_ipa_fixture.lean`.

Trust surface: DL-binding (a hypothesis throughout) and the Fiat–Shamir axioms — the
declared assumption that the Poseidon sponge (the `poseidon` package) provides a valid
Fiat–Shamir transform.
-/
