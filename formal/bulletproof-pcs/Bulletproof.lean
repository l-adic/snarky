import Bulletproof.Protocol
import Bulletproof.Wire

/-!
# Bulletproof — the IPA polynomial commitment scheme

Root module of the `Bulletproof` library: the inner-product-argument polynomial commitment as
deployed by kimchi.

- `Bulletproof/Protocol.lean` — the abstract scheme: SRS and commitment, opening proof and
  verifier, the batched opening, and the chunk layer.
- `Bulletproof/Wire.lean` — the executable wire verifier over the Pasta curves, driven by the
  Poseidon Fq-sponge. This is what `Kimchi.Verifier.kimchiVerify` finishes on
  (`Ipa.verifyFrom`, from the warm fq-sponge state).

Both layers are **specifications**: the transcription proof-systems' `poly-commitment` is
measured against, and the anchor a circuit implementation of the opening check is proved
faithful to. The soundness development this package once carried — abstract opening
soundness, binding, and the forking/knowledge-soundness layer over `Zcash/ironwood` — was
retired; see `git log` for the tree.

The fixture decoders for the proof-systems wire data live in the separate
`BulletproofFixture` target, driven by `scripts/check_ipa_fixture.lean`.

Trust surface: the standard logical axioms plus the Pasta trust base (the `native_decide`
certificates that `scripts/check_axioms.lean` admits by defining module).
-/
