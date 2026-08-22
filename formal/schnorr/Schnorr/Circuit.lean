import Schnorr.Wire
import Snarky.Circuit.DSL.UnpackFull
import Snarky.Kimchi.Circuit.RandomOracle
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.CurvePoint

/-!
# The in-circuit verifier

`verifyCircuit` implements the wire `verify` stage for stage, over `Fq`: the six
coordinates through the block-mode random-oracle gadget (`RandomOracle.hashVec`),
`unpackFull` for the canonical challenge bits (low 128 packed by `packLow`),
`endoMul` for `[c]·pk`, `varBaseMul` for `[z]·G` on the constant generator with its
bits locked below the modulus (`ltBitstringValue`; the statement carries `z`
`Type1`-typed), and one complete addition with two coordinate equalities pinning
`[z]·G = u + [c]·pk`. The statement is `Wire`'s `Statement` at the carrier `FVar Fq`;
here its check is derived from its fields. The laws tying the circuit to the wire live
beside it.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

variable {F c : Type}

/-- The statement's check is its fields': both Vesta points pay their on-curve rows
(`CurvePoint.check`), the response cell nothing — derived through the product. -/
instance instStatementCheckedType [BasicSystem Fq c] :
    CheckedType Fq c (Statement (FVar Fq)) :=
  CheckedType.ofEquiv (c := c) Statement.equivProd

/-- The statement's contract is its fields': both points on-curve, nothing for the
response cell. -/
instance instStatementSoundCheckedType [BasicSystem Fq c] [ConstraintHolds Fq c]
    [LawfulBasicSystem Fq c] {V : Valuation Fq} :
    SoundCheckedType Fq c V (Statement (FVar Fq)) :=
  SoundCheckedType.ofEquiv Statement.equivProd

/-- The in-circuit verifier: hash the transcript, unpack it canonically and take the
low 128 bits as the challenge, act on the public key through the endomorphism, run
the ladder with its bits locked below the modulus, and pin `[z]·G = u + [c]·pk`.
The two canonicity locks (`unpackFull`, `assertBitsBelow` on the ladder's bits) are
what pin the cross-field readings to canonical representatives — without them the
challenge split and the ladder scalar are fixed only up to reconstruction classes.
The closing `assertNotEqual` excludes the one carrier whose decode is the zero
response (`Type1.zeroCarrier`) — the residue-`0` constant of the ladder's forbidden band,
mirroring the deployed `unshift_nonzero` convention. -/
def verifyCircuit [BasicSystem Fq c] [KimchiSystem Fq c]
    (st : Statement (FVar Fq)) :
    CircuitM Fq c PUnit := do
  let squeezed ← RandomOracle.hashVec Poseidon.fqParams
    [.const gen.x, .const gen.y, st.pk.point.x, st.pk.point.y, st.u.point.x, st.u.point.y]
  let hbits ← unpackFull PALLAS_SCALAR_CARD 255 squeezed
  let cpk ← endoMul Pasta.vestaEndo 32 st.pk.point ⟨packLow 128 (by omega) hbits⟩
  let zr ← varBaseMul 255 51 ⟨.const gen.x, .const gen.y⟩ st.z
  assertBitsBelow PALLAS_SCALAR_CARD 255 (zr.lsbBits.toList.map .unchecked)
  let rhs ← addFast .checkFinite st.u.point cpk
  assertEqual zr.g.x rhs.p.x
  assertEqual zr.g.y rhs.p.y
  assertNotEqual st.z.val (.const Type1.zeroCarrier)

end Schnorr
