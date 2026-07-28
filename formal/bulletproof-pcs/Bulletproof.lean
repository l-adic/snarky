import Bulletproof.Protocol
import Bulletproof.Wire
import Bulletproof.Soundness
import Bulletproof.Reflection
import Bulletproof.Forking.Capstone
import Bulletproof.Forking.KnowledgeSoundness

/-!
# Bulletproof — the IPA polynomial commitment scheme

Root module of the `Bulletproof` library: the inner-product-argument polynomial
commitment as deployed by kimchi. The abstract scheme and its soundness (`Basic`,
`Batch`, `Chunk`, `Verify`, `Soundness/**` — opening soundness, batched opening
soundness, binding = no-DL-relation, the chunked width pass); the executable wire
verifier over the Pasta curves, driven by the Poseidon Fq-sponge (`Wire`); the
reflection bridge between the two (`Reflection`); and the forking development
(`Forking/`), whose per-curve headline is the knowledge soundness of the deployed
verifier, `Ipa.Forking.ipa{Vesta,Pallas}_knowledge_sound`. The fixture decoders for
the proof-systems wire data live in the separate `BulletproofFixture` target, driven
by `scripts/check_ipa_fixture.lean`.

Trust surface: DL-binding (a hypothesis throughout) and the standard logical axioms —
no Fiat–Shamir axiom. The random-oracle idealisation enters only as the game's uniform
challenge table, and the sponge-faithfulness exhibits (`Forking/Transcript.lean`,
`Forking/Deployed.lean`) record how the game's reads relate to the deployed sponge.
-/
