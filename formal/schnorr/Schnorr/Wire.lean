import Poseidon.FqSponge
import Poseidon.RandomOracle
import Pasta.Basic
import Snarky.Kimchi.Circuit.CurvePoint
import Snarky.Types.Shifted

/-!
# Schnorr identification over Vesta — the wire protocol

Non-interactive Schnorr identification
(https://www.zkdocs.com/docs/zkdocs/zero-knowledge-protocols/schnorr/) at the
deployed Pasta instantiation: a prover holding `x` with `pk = [x]·G` commits
`u = [r]·G` and responds `z = r + c·x`; the verifier checks `[z]·G = u + [c]·pk`.

On the wire the statement is five field elements — `Statement Fq`: two Vesta-tagged
points and a `Type1`-carried response — and `verify` is the whole verifier at that
encoding: deserialize (both points on the curve, the response decode nonzero — the
deployed `unshift_nonzero` convention), then the check, scalars acting through the
point group's `Fp`-module structure. `verify_iff` is the same check read in Mathlib's
group — the form the gadget laws land on. The circuit works on the same `Statement`
at the carrier `FVar Fq`.

Points live on Vesta, so coordinates are in `Fq` and the exponents in `Fp`; the
circuit is an `Fq`-circuit, receiving `z` across the field boundary (`Type1`:
`p < q`, one shifted element). The challenge convention is the kimchi verifier's,
not zkdocs' `H(…) mod p`: hash the generator and statement coordinates with the
Vesta-side random oracle (`transcriptHash`), truncate to a 128-bit prechallenge,
act through the endomorphism expansion (`FqSponge.endoExpand`). The in-circuit
challenge then agrees with the wire by the gadget laws alone.
-/

namespace Schnorr

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon
open Snarky (Type1 FVar CircuitType)
open Snarky.Kimchi (VestaPoint)

/-- The generator: the prime-order Vesta point `(-1, 2)` — a constant of this
package, not a Mina-specified base. -/
def gen : SWPoint Vesta.curve := ⟨-1, 2, Or.inl (by decide)⟩

/-- The generator is on the curve. -/
theorem gen_onCurve : OnCurve Vesta.curve.A Vesta.curve.B (gen.x, gen.y) := by
  rcases gen.onCurve with h | h
  · exact h
  · exact absurd h (by decide)

/-- The generator as a Mathlib affine point. -/
theorem gen_nonsingular : Vesta.curve.toAffine.Nonsingular gen.x gen.y :=
  nonsingular_toW gen_onCurve

/-- The statement over a carrier: at `Fq` the wire's five field elements, at `FVar Fq`
the in-circuit statement. The points are Vesta-tagged — `verify` deserializes them,
and the circuit's derived `CheckedType` pays their on-curve rows — and the response is
`Type1`-carried (`p < q`): the ladder consuming it realizes the shift, and
`Type1.toScalar` reads its scalar-field value. -/
structure Statement (α : Type) where
  /-- The public key `[x]·G`. -/
  pk : VestaPoint α
  /-- The prover's commitment `[r]·G`. -/
  u : VestaPoint α
  /-- The response `r + c·x`, a Vesta scalar in its `Type1` carrier. -/
  z : Type1 α

/-- The statement is its three fields. -/
@[simps apply symm_apply] def Statement.equivProd {α : Type} :
    Statement α ≃ VestaPoint α × VestaPoint α × Type1 α where
  toFun st := (st.pk, st.u, st.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The statement encodes as its five field elements, points first, coordinatewise —
the product presentation. -/
instance instStatementCircuitType :
    CircuitType Fq (Statement Fq) (Statement (FVar Fq)) :=
  CircuitType.ofEquiv Statement.equivProd Statement.equivProd

/-- A point's serialization: its coordinates. -/
def encodePoint (P : SWPoint Vesta.curve) : VestaPoint Fq := ⟨⟨P.x, P.y⟩⟩

/-- The honest prover's serialization of its points and response. -/
def Statement.encode (pk u : SWPoint Vesta.curve) (z : Fp) : Statement Fq :=
  ⟨encodePoint pk, encodePoint u, Type1.toShifted z⟩

/-- The transcript hash, before truncation: the generator and statement coordinates
through the random oracle. A single squeeze is the block-mode hash of the absorbed
coordinates (`hash_eq_squeeze`), so this IS the Fq-sponge's squeeze. -/
def transcriptHash (pk u : VestaPoint Fq) : Fq :=
  Poseidon.RandomOracle.hash Poseidon.fqParams
    [gen.x, gen.y, pk.point.x, pk.point.y, u.point.x, u.point.y]

/-- The canonical 128-bit prechallenge: the low 128 bits of the transcript hash's
canonical representative — the Fq-sponge `challengeNat` convention. -/
def preChallenge (pk u : VestaPoint Fq) : ℕ :=
  (transcriptHash pk u).val % 2 ^ 128

/-- The challenge: the prechallenge through the endomorphism expansion, a Vesta
scalar. -/
def challenge (pk u : VestaPoint Fq) : Fp :=
  FqSponge.endoExpand FqVesta.spec.lam (preChallenge pk u)

/-- The wire verifier: deserialize — both points on Vesta, the response decode
nonzero — then `[z]·G = u + [c]·pk`, the scalars acting through the point group's
`Fp`-module structure. Off-curve coordinates and the zero response are rejected here,
as a deployed verifier rejects them at parsing. -/
def verify (st : Statement Fq) : Bool :=
  if h : OnCurve Vesta.curve.A Vesta.curve.B (st.pk.point.x, st.pk.point.y) ∧
      OnCurve Vesta.curve.A Vesta.curve.B (st.u.point.x, st.u.point.y) ∧
      st.z.toScalar ≠ (0 : Fp) then
    decide (st.z.toScalar • gen
      = (⟨st.u.point.x, st.u.point.y, Or.inl h.2.1⟩ : SWPoint Vesta.curve)
        + challenge st.pk st.u
          • (⟨st.pk.point.x, st.pk.point.y, Or.inl h.1⟩ : SWPoint Vesta.curve))
  else false

open WeierstrassCurve.Affine in
/-- `verify` in Mathlib's group: it accepts exactly the statements whose points
deserialize on-curve, whose response is nonzero, and whose affine points satisfy
`[z]·G = u + [c]·pk` — the form the gadget laws land on. -/
theorem verify_iff (st : Statement Fq) :
    verify st = true ↔
      ∃ (hpk : OnCurve Vesta.curve.A Vesta.curve.B (st.pk.point.x, st.pk.point.y))
        (hu : OnCurve Vesta.curve.A Vesta.curve.B (st.u.point.x, st.u.point.y)),
        st.z.toScalar ≠ (0 : Fp) ∧
        st.z.toScalar • Point.some gen.x gen.y gen_nonsingular
          = Point.some st.u.point.x st.u.point.y (nonsingular_toW hu)
            + challenge st.pk st.u
              • Point.some st.pk.point.x st.pk.point.y (nonsingular_toW hpk) := by
  unfold verify
  split
  · rename_i h
    rw [decide_eq_true_eq, ← (SWPoint.equivPoint Vesta.curve).injective.eq_iff, map_add,
      Pasta.vesta_equivPoint_smul, Pasta.vesta_equivPoint_smul,
      SWPoint.equivPoint_eq_some gen gen_onCurve,
      SWPoint.equivPoint_eq_some
        (⟨st.pk.point.x, st.pk.point.y, Or.inl h.1⟩ : SWPoint Vesta.curve) h.1,
      SWPoint.equivPoint_eq_some
        (⟨st.u.point.x, st.u.point.y, Or.inl h.2.1⟩ : SWPoint Vesta.curve) h.2.1]
    exact ⟨fun hv => ⟨h.1, h.2.1, h.2.2, hv⟩, fun ⟨_, _, _, hv⟩ => hv⟩
  · rename_i h
    exact ⟨fun hf => absurd hf Bool.false_ne_true,
      fun ⟨hpk, hu, hz, _⟩ => absurd ⟨hpk, hu, hz⟩ h⟩

/-- **Protocol completeness.** The honest prover convinces the verifier: for a key `x`
and nonce `r` whose points are nonzero — the zero point has no on-curve serialization —
and whose response is nonzero, the serialized statement `⟨[x]·G, [r]·G, r + c·x⟩`, `c`
its own challenge, passes `verify`. Scalars act through the point group's
`Fp`-module structure, so the check is `z = r + c·x` in `Fp`. This is also the
exhibit that `verify` accepts: the circuit laws' acceptance hypotheses are
satisfiable. -/
theorem completeness (x r : Fp) (hx : x • gen ≠ 0) (hr : r • gen ≠ 0)
    (hz : r + challenge (encodePoint (x • gen)) (encodePoint (r • gen)) * x ≠ 0) :
    verify (Statement.encode (x • gen) (r • gen)
      (r + challenge (encodePoint (x • gen)) (encodePoint (r • gen)) * x)) = true := by
  have hpkC := SWPoint.onCurve_of_ne_zero hx
  have huC := SWPoint.onCurve_of_ne_zero hr
  rw [verify_iff]
  refine ⟨hpkC, huC, ?_, ?_⟩
  · simpa [Statement.encode, Type1.toScalar_toShifted] using hz
  · simp only [Statement.encode, encodePoint, Type1.toScalar_toShifted]
    rw [← SWPoint.equivPoint_eq_some gen gen_onCurve,
      ← SWPoint.equivPoint_eq_some (r • gen) huC, ← SWPoint.equivPoint_eq_some (x • gen) hpkC,
      ← Pasta.vesta_equivPoint_smul, ← Pasta.vesta_equivPoint_smul, ← map_add, add_smul,
      mul_smul]

end Schnorr
