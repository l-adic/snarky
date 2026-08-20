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

variable {F c : Type}

/-- The circuit field reads canonical representatives through `ZMod.val` — the same
instance the CS-equality oracle declares at `Fp`. -/
instance instToNatFq : ToNat Fq := ⟨ZMod.val⟩

/-- The statement's coordinate shape over a carrier: the two points and the
(`Type1`-shifted) response. At `FVar Fq` this is the in-circuit statement
`verifyCircuit` consumes; at `Fq` it is that bundle's `CircuitType` reading. The
wire `Statement` refines a reading — on-curve nonzero points and the scalar-field
response — which is exactly what the endpoint law recovers. -/
structure Statement.Raw (α : Type) where
  /-- The public key's coordinates. -/
  pk : AffinePoint α
  /-- The commitment's coordinates. -/
  u : AffinePoint α
  /-- The response, one shifted element (`Type1`: `p < q`). -/
  z : α

/-- The statement encodes as its five field elements, points first, coordinatewise. -/
instance instStatementRawCircuitType :
    CircuitType F (Statement.Raw F) (Statement.Raw (FVar F)) where
  size := 5
  valueToFields st := #v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z]
  fieldsToValue fs := ⟨⟨fs[0], fs[1]⟩, ⟨fs[2], fs[3]⟩, fs[4]⟩
  varToFields st := #v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z]
  fieldsToVar fs := ⟨⟨fs[0], fs[1]⟩, ⟨fs[2], fs[3]⟩, fs[4]⟩

/-- The statement bundle reads componentwise into a `Statement.Raw F` — the reading a
proof decomposes into the per-cell facts the gadget laws consume. -/
@[circuitVal] theorem readVal_statementRaw [Add F] [Mul F] (V : Valuation F)
    (st : Statement.Raw (FVar F)) :
    readVal V st = Statement.Raw.mk ⟨st.pk.x.val V, st.pk.y.val V⟩
      ⟨st.u.x.val V, st.u.y.val V⟩ (st.z.val V) := by
  show Statement.Raw.mk
      ⟨((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z]).map (·.val V))[0],
        ((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z]).map (·.val V))[1]⟩
      ⟨((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z]).map (·.val V))[2],
        ((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z]).map (·.val V))[3]⟩
      (((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z]).map (·.val V))[4]) = _
  simp

/-- The wire transcript hash, in-circuit: the six coordinates through the block-mode
random-oracle gadget — `transcriptHash` computed over circuit variables, gadget for
definition. -/
def squeezeTranscript [KimchiSystem Fq c] (pk u : AffinePoint (FVar Fq)) :
    CircuitM Fq c (FVar Fq) :=
  RandomOracle.hashVec Poseidon.fqParams
    [.const gen.x, .const gen.y, pk.x, pk.y, u.x, u.y]

/-- The in-circuit verifier: derive the challenge from the transcript, act with it on
the public key through the endomorphism, and pin `[z]·G = u + [c]·pk` on the
coordinates. -/
def verifyCircuit [BasicSystem Fq c] [KimchiSystem Fq c]
    (st : Statement.Raw (FVar Fq)) :
    CircuitM Fq c PUnit := do
  let squeezed ← squeezeTranscript st.pk st.u
  let c ← lowest128Bits (.const Pasta.vestaEndo) squeezed
  let cpk ← endoMul Pasta.vestaEndo 32 st.pk c
  let zg ← scaleFast1 255 51 ⟨.const gen.x, .const gen.y⟩ ⟨st.z⟩
  let rhs ← addFast .checkFinite st.u cpk
  assertEqual zg.x rhs.p.x
  assertEqual zg.y rhs.p.y

end Schnorr
