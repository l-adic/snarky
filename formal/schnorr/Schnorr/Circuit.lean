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
`[z]·G = u + [c]·pk`. The laws tying it to `verify` live beside it.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

variable {F c : Type}

/-- The statement's coordinate shape over a carrier: at `FVar Fq` the in-circuit
statement, at `Fq` its `CircuitType` reading. The wire `Statement` refines a
reading with the on-curve proofs and the scalar-field response. -/
structure Statement.Raw (α : Type) where
  /-- The public key's coordinates. -/
  pk : AffinePoint α
  /-- The commitment's coordinates. -/
  u : AffinePoint α
  /-- The response, `Type1`-carried (`p < q`): the ladder consuming it realizes the
  shift, and `Type1.fromShifted` reads its scalar-field value. -/
  z : Type1 α

/-- The statement is its three fields. -/
@[simps apply symm_apply] def Statement.Raw.equivProd {α : Type} :
    Statement.Raw α ≃ AffinePoint α × AffinePoint α × Type1 α where
  toFun st := (st.pk, st.u, st.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

attribute [circuitVal] Statement.Raw.equivProd_apply Statement.Raw.equivProd_symm_apply

/-- The statement encodes as its five field elements, points first, coordinatewise —
the product presentation. -/
instance instStatementRawCircuitType :
    CircuitType F (Statement.Raw F) (Statement.Raw (FVar F)) :=
  CircuitType.ofEquiv
    (inferInstance : CircuitType F (AffinePoint F × AffinePoint F × Type1 F)
      (AffinePoint (FVar F) × AffinePoint (FVar F) × Type1 (FVar F)))
    Statement.Raw.equivProd Statement.Raw.equivProd

open CompElliptic.Curves.Pasta in
/-- The statement's input check: both points on Vesta through the `CurvePoint` gadget
(`assert_on_curve` at the public coordinates). The response cell carries no check of
its own — its canonicity is the circuit's business. -/
def Statement.Raw.check [BasicSystem Fq c] (st : Statement.Raw (FVar Fq)) :
    CircuitM Fq c PUnit := do
  CurvePoint.check (a := Vesta.curve.A) (b := Vesta.curve.B) ⟨st.pk⟩
  CurvePoint.check (a := Vesta.curve.A) (b := Vesta.curve.B) ⟨st.u⟩

/-- The statement pays its points' on-curve checks at the whole-circuit seam. -/
instance instStatementRawCheckedType [BasicSystem Fq c] :
    CheckedType Fq c (Statement.Raw (FVar Fq)) where
  check := Statement.Raw.check

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
    (st : Statement.Raw (FVar Fq)) :
    CircuitM Fq c PUnit := do
  let squeezed ← RandomOracle.hashVec Poseidon.fqParams
    [.const gen.x, .const gen.y, st.pk.x, st.pk.y, st.u.x, st.u.y]
  let hbits ← unpackFull PALLAS_SCALAR_CARD 255 squeezed
  let cpk ← endoMul Pasta.vestaEndo 32 st.pk ⟨packLow 128 (by omega) hbits⟩
  let zr ← varBaseMul 255 51 ⟨.const gen.x, .const gen.y⟩ st.z
  assertBitsBelow PALLAS_SCALAR_CARD 255 (zr.lsbBits.toList.map .unchecked)
  let rhs ← addFast .checkFinite st.u cpk
  assertEqual zr.g.x rhs.p.x
  assertEqual zr.g.y rhs.p.y
  assertNotEqual st.z.val (.const Type1.zeroCarrier)

end Schnorr
