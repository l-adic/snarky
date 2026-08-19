import Schnorr.Wire
import Snarky.Kimchi.Circuit.Poseidon
import Snarky.Kimchi.Circuit.RangeCheck
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul

/-!
# The in-circuit verifier

`verifyCircuit` implements the wire `verify` stage for stage, over the circuit field
`Fq` (the Vesta base field, where the statement's points have native coordinates):

- **the transcript** — the wire sponge's schedule for exactly six absorbed
  coordinates and one squeeze is three permutations with affine rate additions;
  `squeezeTranscript` runs the poseidon gadget three times and reads the first rate
  slot;
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

/-- The circuit field reads canonical representatives through `ZMod.val` — the same
instance the CS-equality oracle declares at `Fp`. -/
instance : ToNat Fq := ⟨ZMod.val⟩

/-- The wire sponge's transcript, in-circuit: six absorbed coordinates and one
squeeze. At rate 2 the automaton adds each absorbed pair into the two rate slots and
permutes at the block boundary, and the squeeze permutes once more and reads the
first slot — three poseidon gadgets with affine rate additions, the generator's
block over constants. -/
def squeezeTranscript (pk u : AffinePoint (FVar Fq)) :
    CircuitM Fq (KimchiConstraint Fq) (FVar Fq) := do
  let s1 ← poseidon _root_.Poseidon.fqParams
    (.const gen.x, .const gen.y, .const 0)
  let s2 ← poseidon _root_.Poseidon.fqParams
    (CVar.add_ s1.1 pk.x, CVar.add_ s1.2.1 pk.y, s1.2.2)
  let s3 ← poseidon _root_.Poseidon.fqParams
    (CVar.add_ s2.1 u.x, CVar.add_ s2.2.1 u.y, s2.2.2)
  pure s3.1

/-- The in-circuit verifier: derive the challenge from the transcript, act with it on
the public key through the endomorphism, and pin `[z]·G = u + [c]·pk` on the
coordinates. -/
def verifyCircuit (pk u : AffinePoint (FVar Fq)) (z : FVar Fq) :
    CircuitM Fq (KimchiConstraint Fq) PUnit := do
  let squeezed ← squeezeTranscript pk u
  let c ← lowest128Bits (.const Pasta.vestaEndo) squeezed
  let cpk ← endoMul Pasta.vestaEndo 32 pk c
  let zg ← scaleFast1 255 51 ⟨.const gen.x, .const gen.y⟩ ⟨z⟩
  let rhs ← addFast .checkFinite u cpk
  assertEqual zg.x rhs.p.x
  assertEqual zg.y rhs.p.y

end Schnorr
