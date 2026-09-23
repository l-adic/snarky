import Bulletproof.Protocol
import Bulletproof.Wire

/-!
# Bulletproof — the IPA polynomial commitment scheme

The inner-product-argument polynomial commitment as deployed by kimchi.

- `Bulletproof/Protocol.lean` — the curve-generic algebra: the SRS, the generator commitment,
  the challenge polynomial `b`, and the batched opening's scalar combiners.
- `Bulletproof/Wire.lean` — the executable batched opening verifier over the Pasta curves,
  driven by the Poseidon fq-sponge. `Kimchi.Verifier.kimchiVerify` finishes on its
  warm-sponge entry point `Ipa.verifyFrom`.

Both are specifications, with no soundness claim: the verifier is the transcription
proof-systems' `poly-commitment` is checked against, and the anchor a circuit implementation
of the opening check is proved faithful to. The fixture decoders live in the separate
BulletproofFixture library.

Trust surface: the standard logical axioms plus the Pasta `native_decide` certificates.
-/
