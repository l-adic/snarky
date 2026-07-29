import Bulletproof.Protocol
import Bulletproof.Wire
import Bulletproof.Soundness
import Bulletproof.Reflection
import Bulletproof.Forking.Capstone
import Bulletproof.Forking.KnowledgeSoundness

/-!
# Bulletproof — the IPA polynomial commitment scheme

Root module of the `Bulletproof` library: the inner-product-argument polynomial commitment as
deployed by kimchi.

- `Bulletproof/Protocol.lean` — the abstract scheme: SRS and commitment, opening proof and
  verifier, the batched opening, and the chunk layer.
- `Bulletproof/Soundness.lean` and `Bulletproof/Soundness/SingleOpening.lean` — soundness of
  those openings: single-opening extraction, binding as no-DL-relation, and the batched and
  chunked headlines.
- `Bulletproof/Wire.lean` — the executable wire verifier over the Pasta curves, driven by the
  Poseidon Fq-sponge.
- `Bulletproof/Reflection.lean` — the bridge between the executable and abstract layers.
- `Bulletproof/Forking/` — the forking development, whose per-curve headline is knowledge
  soundness of the deployed verifier, `Ipa.Forking.ipa{Vesta,Pallas}_knowledge_sound`.

The fixture decoders for the proof-systems wire data live in the separate
`BulletproofFixture` target, driven by `scripts/check_ipa_fixture.lean`.

Trust surface: DL-binding, a hypothesis throughout, plus the standard logical axioms and the
Pasta trust base (the `native_decide` certificates that `scripts/check_axioms.lean` admits by
defining module). There is no Fiat–Shamir axiom: the random-oracle idealisation enters only
as the game's uniform challenge table, and the sponge-faithfulness exhibits
(`Forking/Transcript.lean`, `Forking/Deployed.lean`) record how the game's reads relate to
the deployed sponge.
-/
