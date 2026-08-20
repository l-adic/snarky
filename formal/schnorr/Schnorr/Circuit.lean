import Schnorr.Wire
import Snarky.Kimchi.Circuit.RandomOracle
import Snarky.Kimchi.Circuit.RangeCheck
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul

/-!
# The in-circuit verifier

`verifyCircuit` implements the wire `verify` stage for stage, over `Fq`: the six
coordinates through the block-mode random-oracle gadget (`RandomOracle.hashVec`),
`lowest128Bits` for the challenge split (both halves range-checked), `endoMul` for
`[c]·pk`, `scaleFast1` for `[z]·G` on the constant generator (`z` enters
`Type1`-shifted), and one complete addition with two coordinate equalities pinning
`[z]·G = u + [c]·pk`. The laws tying it to `verify` live beside it.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

variable {F c : Type}

/-- The circuit field reads canonical representatives through `ZMod.val`. -/
instance instToNatFq : ToNat Fq := ⟨ZMod.val⟩

/-- The statement's coordinate shape over a carrier: at `FVar Fq` the in-circuit
statement, at `Fq` its `CircuitType` reading. The wire `Statement` refines a
reading with the on-curve proofs and the scalar-field response. -/
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

/-- The statement's cells carry no check of their own (the `genericCheck`
convention) — what the statement must satisfy is the endpoint laws' business. -/
instance instStatementRawCheckedType : CheckedType F c (Statement.Raw (FVar F)) where
  check _ := .pure PUnit.unit

/-- The statement bundle reads componentwise into a `Statement.Raw F`. -/
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

/-- The statement bundle is readable iff its five cells evaluate. -/
theorem readable_statementRaw_iff [Add F] [Mul F] {env : Assignments F}
    {st : Statement.Raw (FVar F)} :
    Readable (Statement.Raw F) env st ↔
      (st.pk.x.eval env).isOk ∧ (st.pk.y.eval env).isOk ∧
      (st.u.x.eval env).isOk ∧ (st.u.y.eval env).isOk ∧ (st.z.eval env).isOk := by
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
      st.z.eval env = .ok sv.z := by
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

/-- The in-circuit verifier: hash the transcript, derive the challenge, act on the
public key through the endomorphism, and pin `[z]·G = u + [c]·pk`. -/
def verifyCircuit [BasicSystem Fq c] [KimchiSystem Fq c]
    (st : Statement.Raw (FVar Fq)) :
    CircuitM Fq c PUnit := do
  let squeezed ← RandomOracle.hashVec Poseidon.fqParams
    [.const gen.x, .const gen.y, st.pk.x, st.pk.y, st.u.x, st.u.y]
  let c ← lowest128Bits (.const Pasta.vestaEndo) squeezed
  let cpk ← endoMul Pasta.vestaEndo 32 st.pk c
  let zg ← scaleFast1 255 51 ⟨.const gen.x, .const gen.y⟩ ⟨st.z⟩
  let rhs ← addFast .checkFinite st.u cpk
  assertEqual zg.x rhs.p.x
  assertEqual zg.y rhs.p.y

end Schnorr
