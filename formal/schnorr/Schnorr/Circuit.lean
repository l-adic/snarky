import Schnorr.Wire
import Snarky.Kimchi.Circuit.RandomOracle
import Snarky.Kimchi.Circuit.RangeCheck
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul

/-!
# The in-circuit verifier

`verifyCircuit` implements the wire `verify` stage for stage, over the circuit field
`Fq` (the Vesta base field, where the statement's points have native coordinates):

- **the transcript** — `squeezeTranscript` hashes the six coordinates with the
  block-mode random-oracle gadget (`RandomOracle.hashVec`), computing the wire's
  `transcriptHash` over circuit variables;
- **the challenge** — `lowest128Bits` splits off the squeeze's low 128 bits (the
  `squeeze_challenge` flavor: both halves range-checked), and `endoMul` acts with
  them on the public key: the endomorphism expansion the wire side performs in
  `FqSponge.squeezeChallenge` is the gate's own recoding;
- **the response** — `z` enters as one field element (Type1: the Vesta scalar field
  is the smaller of the pair), and `scaleFast1` computes `[z]·G` at the full 255-bit
  width on the constant generator;
- **the check** — one complete addition and two coordinate equalities pin
  `[z]·G = u + [c]·pk`.

This module is the circuit alone; the laws tying it to `verify` are the package's
subject and live beside it.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

variable {c : Type}

/-- The circuit field reads canonical representatives through `ZMod.val` — the same
instance the CS-equality oracle declares at `Fp`. -/
instance instToNatFq : ToNat Fq := ⟨ZMod.val⟩

/-- The wire transcript hash, in-circuit: the six coordinates through the block-mode
random-oracle gadget — `transcriptHash` computed over circuit variables, gadget for
definition. -/
def squeezeTranscript [KimchiSystem Fq c] (pk u : AffinePoint (FVar Fq)) :
    CircuitM Fq c (FVar Fq) :=
  RandomOracle.hashVec _root_.Poseidon.fqParams
    [.const gen.x, .const gen.y, pk.x, pk.y, u.x, u.y]

/-- The in-circuit verifier: derive the challenge from the transcript, act with it on
the public key through the endomorphism, and pin `[z]·G = u + [c]·pk` on the
coordinates. -/
def verifyCircuit [BasicSystem Fq c] [KimchiSystem Fq c]
    (pk u : AffinePoint (FVar Fq)) (z : FVar Fq) :
    CircuitM Fq c PUnit := do
  let squeezed ← squeezeTranscript pk u
  let c ← lowest128Bits (.const Pasta.vestaEndo) squeezed
  let cpk ← endoMul Pasta.vestaEndo 32 pk c
  let zg ← scaleFast1 255 51 ⟨.const gen.x, .const gen.y⟩ ⟨z⟩
  let rhs ← addFast .checkFinite u cpk
  assertEqual zg.x rhs.p.x
  assertEqual zg.y rhs.p.y

end Schnorr
