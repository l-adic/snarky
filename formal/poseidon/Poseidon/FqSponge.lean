import CompElliptic.Curves.Pasta
import Poseidon.Basic
import Pasta.Endo

/-!
# The kimchi Fq-sponge

The consumer-facing sponge of kimchi's Fiat–Shamir transform, transcribed from proof-systems
`mina_poseidon` `sponge.rs` (`DefaultFqSponge`) and built on the duplex automaton of
`Poseidon/Basic.lean`. It is generic over the curve's field pair: the sponge state lives in
the base field `ZMod base`, and challenges land in the scalar field `ZMod scalar`. The
field-dependent data comes from a `Spec`; everything else follows from the two
cardinalities.

## The limb buffer

Alongside the Poseidon state, the sponge carries a buffer `lastSqueezed` of 64-bit limbs.
Each raw squeeze contributes its two low limbs (128 high-entropy bits), and a scalar
challenge (`challenge`, 128 bits) is packed from the next two buffered limbs. Every
absorption clears the buffer, and field-element squeezes (`challengeFq`) bypass it and clear
it.

## The endomorphism expansion

A squeezed 128-bit prechallenge becomes an *effective* scalar `a·λ + b` through the
endomorphism expansion of `endoExpand` (`sponge.rs` `to_field_with_length`, Halo §6.2). It is
the same recoding the `EndoScalar` gate constrains in-circuit (`Kimchi.Gate.EndoScalar`,
accumulator init `(2, 2)`).

## The Pasta instantiations

`FqVesta.spec` and `FqPallas.spec` supply the two sides of the Pasta cycle
(`DefaultFqSponge<VestaParameters>` / `DefaultFqSponge<PallasParameters>`). Both are
validated against `DefaultFqSponge` op traces by `scripts/check_fq_sponge.lean`.
-/

namespace Poseidon.FqSponge

/-- The field-dependent data of a curve's Fq-sponge. Everything else, including which
`absorbFr` branch applies, is determined by the two cardinalities: a scalar absorbs directly
when `scalar < base`, and as (high bits, low bit) when the scalar field is the larger. -/
structure Spec (base scalar : ℕ) where
  /-- The Poseidon parameters over the base field. -/
  params : Params (ZMod base)
  /-- The endomorphism eigenvalue `λ` used by the scalar field's challenge expansion. -/
  lam : ZMod scalar

open CompElliptic.CurveForms.ShortWeierstrass

variable {base scalar : ℕ} [Field (ZMod base)] [Field (ZMod scalar)]

/-- A sponge in flight: the Poseidon automaton over the base field, plus its limb buffer. -/
structure S (base : ℕ) where
  /-- The Poseidon duplex automaton over the base field. -/
  sponge : State (ZMod base)
  /-- Buffered 64-bit limbs of raw squeezes not yet consumed by a challenge. -/
  lastSqueezed : List ℕ

/-- The fresh sponge: fresh automaton, empty buffer. -/
def init : S base := ⟨Poseidon.init, []⟩



/-- The two low 64-bit limbs of a squeezed element — its 128 high-entropy bits
(`HIGH_ENTROPY_LIMBS = 2`). -/
private def lowLimbs (x : ZMod base) : List ℕ :=
  [x.val % 2 ^ 64, x.val / 2 ^ 64 % 2 ^ 64]

/-- Absorb base-field elements (`absorb_fq`): clear the buffer, absorb each. -/
def absorbFq (spec : Spec base scalar) (s : S base) (xs : List (ZMod base)) : S base :=
  ⟨absorb spec.params s.sponge xs, []⟩

/-- Absorb a point (`absorb_g`): its `x` then its `y` coordinate, unconditionally. The
identity is the `(0, 0)` sentinel by construction (`SWPoint.zero`), so this absorbs two
zeros for it, exactly as production does. Branching to a single `0` here would leave the
duplex position one slot behind production on every transcript containing an identity
commitment. -/
def absorbG (spec : Spec base scalar) {E : SWCurve (ZMod base)} (s : S base)
    (P : SWPoint E) : S base :=
  absorbFq spec s [P.x, P.y]

/-- Absorb a scalar-field element (`absorb_fr`). The branch is determined by the
cardinalities: a smaller scalar modulus embeds directly; a larger one absorbs as its high
bits then its low bit. -/
def absorbFr (spec : Spec base scalar) (s : S base) (x : ZMod scalar) : S base :=
  if scalar < base then
    absorbFq spec s [((x.val : ℕ) : ZMod base)]
  else
    absorbFq spec s [((x.val / 2 : ℕ) : ZMod base), ((x.val % 2 : ℕ) : ZMod base)]

/-- Squeeze a raw base-field element (`challenge_fq` / `squeeze_field`): bypass and clear
the limb buffer. -/
def challengeFq (spec : Spec base scalar) (s : S base) : ZMod base × S base :=
  let (x, sp) := squeeze spec.params s.sponge
  (x, ⟨sp, []⟩)

/-- Take two 64-bit limbs from the buffer and pack them into a 128-bit value, refilling the
buffer from the sponge as needed (`squeeze_limbs` at `CHALLENGE_LENGTH_IN_LIMBS = 2`). The
`fuel` argument bounds the refills: each adds two limbs, so one suffices even from empty. -/
private def squeezeLimbsPacked (spec : Spec base scalar) : ℕ → S base → ℕ × S base
  | 0, s => (0, s)
  | fuel + 1, s =>
    match s.lastSqueezed with
    | l0 :: l1 :: rest => (l0 + l1 * 2 ^ 64, ⟨s.sponge, rest⟩)
    | buf =>
      let (x, sp) := squeeze spec.params s.sponge
      squeezeLimbsPacked spec fuel ⟨sp, buf ++ lowLimbs x⟩

/-- Squeeze a 128-bit prechallenge, as a natural number (`challenge`, before the field
cast). -/
def challengeNat (spec : Spec base scalar) (s : S base) : ℕ × S base :=
  squeezeLimbsPacked spec 2 s

/-- A prechallenge from an empty limb buffer is one raw squeeze's value mod `2^128`, both
of its limbs consumed, the buffer left empty. -/
theorem challengeNat_fresh (spec : Spec base scalar) (s : State (ZMod base)) :
    challengeNat spec ⟨s, []⟩
      = ((squeeze spec.params s).1.val % 2 ^ 128, ⟨(squeeze spec.params s).2, []⟩) := by
  rcases hsq : squeeze spec.params s with ⟨x, sp⟩
  simp only [challengeNat, squeezeLimbsPacked, lowLimbs, hsq, List.nil_append, Prod.mk.injEq,
    and_true]
  omega

/-- Squeeze a 128-bit prechallenge into the scalar field (`challenge`). -/
def challenge (spec : Spec base scalar) (s : S base) : ZMod scalar × S base :=
  let (n, s) := challengeNat spec s
  ((n : ZMod scalar), s)

/-- The endomorphism expansion of a 128-bit prechallenge into an effective scalar
(`to_field_with_length`, Halo §6.2): fold the 2-bit windows from the top into the
accumulators `a = b = 2`; the result is `a·λ + b`. -/
def endoExpand {F : Type*} [Field F] (lam : F) (chal : ℕ) : F :=
  let (a, b) := (List.range 64).reverse.foldl
    (fun (ab : F × F) i =>
      let (a, b) := (2 * ab.1, 2 * ab.2)
      let s : F := if chal.testBit (2 * i) then 1 else -1
      if chal.testBit (2 * i + 1) then (a + s, b) else (a, b + s))
    (2, 2)
  a * lam + b

/-- Squeeze an effective scalar challenge (`squeeze_challenge`,
`poly-commitment/src/commitment.rs`): a 128-bit prechallenge, endo-expanded at the spec's
eigenvalue. -/
def squeezeChallenge (spec : Spec base scalar) (s : S base) : ZMod scalar × S base :=
  let (n, s) := challengeNat spec s
  (endoExpand spec.lam n, s)

end Poseidon.FqSponge

namespace Poseidon

/-! ## The Pasta instantiations -/

namespace FqVesta

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The Vesta side of the cycle: the `fq_kimchi` parameters and the Vesta eigenvalue
(`DefaultFqSponge<VestaParameters>`). -/
def spec : FqSponge.Spec PALLAS_SCALAR_CARD PALLAS_BASE_CARD :=
  ⟨fqParams, ((Pasta.vestaLam : ℤ) : Fp)⟩

end FqVesta

namespace FqPallas

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The Pallas side of the cycle: the `fp_kimchi` parameters and the Pallas eigenvalue
(`DefaultFqSponge<PallasParameters>`). Here the scalar field is the larger of the pair, so
`absorbFr` takes the high-bits/low-bit branch. Nothing selects that branch but the
cardinalities. -/
def spec : FqSponge.Spec PALLAS_BASE_CARD PALLAS_SCALAR_CARD :=
  ⟨fpParams, ((Pasta.pallasLam : ℤ) : Fq)⟩

end FqPallas

end Poseidon
