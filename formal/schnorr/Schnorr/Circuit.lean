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
`unpackFull` for the canonical challenge bits (low 128 packed by `challengeOf`),
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

/-- The statement encodes as its five field elements, points first, coordinatewise. -/
instance instStatementRawCircuitType :
    CircuitType F (Statement.Raw F) (Statement.Raw (FVar F)) where
  size := 5
  valueToFields st := #v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z.val]
  fieldsToValue fs := ⟨⟨fs[0], fs[1]⟩, ⟨fs[2], fs[3]⟩, ⟨fs[4]⟩⟩
  varToFields st := #v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z.val]
  fieldsToVar fs := ⟨⟨fs[0], fs[1]⟩, ⟨fs[2], fs[3]⟩, ⟨fs[4]⟩⟩

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

/-- The statement bundle reads componentwise into a `Statement.Raw F`. -/
@[circuitVal] theorem readVal_statementRaw [Add F] [Mul F] (V : Valuation F)
    (st : Statement.Raw (FVar F)) :
    readVal V st = Statement.Raw.mk ⟨st.pk.x.val V, st.pk.y.val V⟩
      ⟨st.u.x.val V, st.u.y.val V⟩ ⟨st.z.val.val V⟩ := by
  show Statement.Raw.mk
      ⟨((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z.val]).map (·.val V))[0],
        ((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z.val]).map (·.val V))[1]⟩
      ⟨((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z.val]).map (·.val V))[2],
        ((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z.val]).map (·.val V))[3]⟩
      ⟨((#v[st.pk.x, st.pk.y, st.u.x, st.u.y, st.z.val]).map (·.val V))[4]⟩ = _
  simp

/-- The statement bundle is readable iff its five cells evaluate. -/
theorem readable_statementRaw_iff [Add F] [Mul F] {env : Assignments F}
    {st : Statement.Raw (FVar F)} :
    Readable (Statement.Raw F) env st ↔
      (st.pk.x.eval env).isOk ∧ (st.pk.y.eval env).isOk ∧
      (st.u.x.eval env).isOk ∧ (st.u.y.eval env).isOk ∧ (st.z.val.eval env).isOk := by
  constructor
  · intro h
    exact ⟨h 0 (show 0 < 5 by omega), h 1 (show 1 < 5 by omega),
      h 2 (show 2 < 5 by omega), h 3 (show 3 < 5 by omega), h 4 (show 4 < 5 by omega)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    have hi' : i < 5 := hi
    match i with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
    | 3 => exact h3
    | 4 => exact h4

/-- The statement bundle's prover-side reading is the pinned evaluation of its five
cells. -/
theorem reads_statementRaw_iff [Field F] {env : Assignments F}
    {st : Statement.Raw (FVar F)} {sv : Statement.Raw F} :
    Reads env st sv ↔
      st.pk.x.eval env = .ok sv.pk.x ∧ st.pk.y.eval env = .ok sv.pk.y ∧
      st.u.x.eval env = .ok sv.u.x ∧ st.u.y.eval env = .ok sv.u.y ∧
      st.z.val.eval env = .ok sv.z.val := by
  constructor
  · rintro ⟨hok, hval⟩
    rw [readable_statementRaw_iff] at hok
    obtain ⟨w0, h0⟩ := CVar.evalOk hok.1
    obtain ⟨w1, h1⟩ := CVar.evalOk hok.2.1
    obtain ⟨w2, h2⟩ := CVar.evalOk hok.2.2.1
    obtain ⟨w3, h3⟩ := CVar.evalOk hok.2.2.2.1
    obtain ⟨w4, h4⟩ := CVar.evalOk hok.2.2.2.2
    rw [readVal_statementRaw, CVar.val_toValuation h0, CVar.val_toValuation h1,
      CVar.val_toValuation h2, CVar.val_toValuation h3, CVar.val_toValuation h4]
      at hval
    rw [h0, h1, h2, h3, h4, ← hval]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨readable_statementRaw_iff.mpr
      ⟨isOk_of_eq h0, isOk_of_eq h1, isOk_of_eq h2, isOk_of_eq h3, isOk_of_eq h4⟩, ?_⟩
    rw [readVal_statementRaw, CVar.val_toValuation h0, CVar.val_toValuation h1,
      CVar.val_toValuation h2, CVar.val_toValuation h3, CVar.val_toValuation h4]

/-- The challenge wire: the packed low 128 bits of a 255-bit canonical unpack — an
affine combination, no constraints of its own. -/
@[irreducible] def challengeOf {F : Type} [Semiring F] [DecidableEq F]
    (bits : Vector (BoolVar F) 255) : FVar F :=
  pack (Vector.ofFn fun i : Fin 128 => bits[i.val]'(by omega))

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
  let cpk ← endoMul Pasta.vestaEndo 32 st.pk ⟨challengeOf hbits⟩
  let zr ← varBaseMul 255 51 ⟨.const gen.x, .const gen.y⟩ st.z
  assertBitsBelow PALLAS_SCALAR_CARD 255
    ((zr.lsbBits.toList.take (5 * 51)).map .unchecked)
  let rhs ← addFast .checkFinite st.u cpk
  assertEqual zr.g.x rhs.p.x
  assertEqual zr.g.y rhs.p.y
  assertNotEqual st.z.val (.const Type1.zeroCarrier)

end Schnorr
