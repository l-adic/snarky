import CompElliptic.Curves.Pasta
import Poseidon.Basic
import Pasta.Endo

/-!
# The kimchi Fq-sponge

The Fiat–Shamir sponge kimchi's verifier consumes, transcribed from proof-systems `sponge.rs`
and built on the duplex automaton of `Poseidon/Basic.lean`. The state lives in the base field
`ZMod base`; challenges land in the scalar field `ZMod scalar`. A `Spec` carries the Poseidon
parameters; everything else follows from the two cardinalities.

## The limb buffer

Alongside the Poseidon state, the sponge buffers 64-bit limbs (`lastSqueezed`). Each raw
squeeze contributes its two low limbs, and a 128-bit prechallenge (`challengeNat`) packs the
next two. Absorbing clears the buffer; a field-element squeeze (`challengeFq`) bypasses and
clears it. The bounds live in the types `Limb` and `Prechallenge`.

## The endomorphism expansion

`endoExpand` turns a prechallenge into an effective scalar `a·λ + b` (Halo §6.2): the
recoding `Kimchi.Gate.EndoScalar.constraints` checks in-circuit, from accumulators `(2, 2)`.

## The Pasta instantiations

`FqVesta.spec` and `FqPallas.spec` are the two sides of the Pasta cycle, both checked against
production op traces by `formal/poseidon/scripts/check_fq_sponge.lean`.
-/

namespace Poseidon.FqSponge

/-- The field-dependent data of a curve's Fq-sponge: its Poseidon parameters. The
`absorbFr` branch is decided by the cardinalities alone. -/
structure Spec (base scalar : ℕ) where
  /-- The Poseidon parameters over the base field. -/
  params : Params (ZMod base)
  /-- One round-constant triple per round (`fullRounds`). Carried here so that no consumer
  takes it as a hypothesis. -/
  hsize : params.roundConstants.size = fullRounds

open CompElliptic.CurveForms.ShortWeierstrass

variable {base scalar : ℕ} [Field (ZMod base)] [Field (ZMod scalar)]

/-- A 64-bit limb of a raw squeeze. -/
abbrev Limb := { n : ℕ // n < 2 ^ 64 }

/-- A 128-bit prechallenge: what a limb-packed squeeze produces, before its field cast
(`challenge`) or endo-expansion (`squeezeChallenge`). -/
abbrev Prechallenge := { n : ℕ // n < 2 ^ 128 }

/-- A sponge in flight: the Poseidon automaton over the base field, plus its limb buffer. -/
structure S (base : ℕ) where
  /-- The Poseidon duplex automaton over the base field. -/
  sponge : State (ZMod base)
  /-- Buffered 64-bit limbs of raw squeezes not yet consumed by a prechallenge. -/
  lastSqueezed : List Limb

/-- The fresh sponge: fresh automaton, empty buffer. -/
def init : S base := ⟨Poseidon.init, []⟩



/-- The two low 64-bit limbs of a squeezed element. -/
private def lowLimbs (x : ZMod base) : List Limb :=
  [⟨x.val % 2 ^ 64, Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
    ⟨x.val / 2 ^ 64 % 2 ^ 64, Nat.mod_lt _ (Nat.two_pow_pos _)⟩]

/-- Absorb base-field elements, clearing the buffer. -/
def absorbFq (spec : Spec base scalar) (s : S base) (xs : List (ZMod base)) : S base :=
  ⟨absorb spec.params s.sponge xs, []⟩

/-- Absorb a point: its `x` then its `y` coordinate, unconditionally. The identity is the
`(0, 0)` sentinel (`SWPoint.zero`), so it absorbs two zeros, as production does; a single `0`
would put the duplex one slot behind on any transcript with an identity commitment. -/
def absorbG (spec : Spec base scalar) {E : SWCurve (ZMod base)} (s : S base)
    (P : SWPoint E) : S base :=
  absorbFq spec s [P.x, P.y]

/-- Absorb a scalar-field element: directly when `scalar < base`, otherwise as its high bits
then its low bit. -/
def absorbFr (spec : Spec base scalar) (s : S base) (x : ZMod scalar) : S base :=
  if scalar < base then
    absorbFq spec s [((x.val : ℕ) : ZMod base)]
  else
    absorbFq spec s [((x.val / 2 : ℕ) : ZMod base), ((x.val % 2 : ℕ) : ZMod base)]

/-- Squeeze a raw base-field element, bypassing and clearing the limb buffer. -/
def challengeFq (spec : Spec base scalar) (s : S base) : ZMod base × S base :=
  let (x, sp) := squeeze spec.params s.sponge
  (x, ⟨sp, []⟩)

/-- Pack the next two buffered limbs into a 128-bit value, refilling the buffer from the
sponge as needed. Each refill adds two limbs, so one unit of fuel suffices even from empty. -/
private def squeezeLimbsPacked (spec : Spec base scalar) :
    ℕ → S base → Prechallenge × S base
  | 0, s => (⟨0, Nat.two_pow_pos _⟩, s)
  | fuel + 1, s =>
    match s.lastSqueezed with
    | l0 :: l1 :: rest =>
      (⟨l0.val + l1.val * 2 ^ 64, by have := l0.property; have := l1.property; omega⟩,
        ⟨s.sponge, rest⟩)
    | buf =>
      let (x, sp) := squeeze spec.params s.sponge
      squeezeLimbsPacked spec fuel ⟨sp, buf ++ lowLimbs x⟩

/-- Squeeze a 128-bit prechallenge. -/
def challengeNat (spec : Spec base scalar) (s : S base) : Prechallenge × S base :=
  squeezeLimbsPacked spec 2 s

omit [Field (ZMod scalar)] in
/-- A prechallenge from an empty limb buffer is one raw squeeze's value mod `2^128`, both
of its limbs consumed, the buffer left empty. -/
theorem challengeNat_fresh (spec : Spec base scalar) (s : State (ZMod base)) :
    challengeNat spec ⟨s, []⟩
      = (⟨(squeeze spec.params s).1.val % 2 ^ 128, Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
          ⟨(squeeze spec.params s).2, []⟩) := by
  rcases hsq : squeeze spec.params s with ⟨x, sp⟩
  simp only [challengeNat, squeezeLimbsPacked, lowLimbs, hsq, List.nil_append, Prod.mk.injEq,
    Subtype.mk.injEq, and_true]
  omega

/-- Squeeze a prechallenge cast into the scalar field. -/
def challenge (spec : Spec base scalar) (s : S base) : ZMod scalar × S base :=
  let (n, s) := challengeNat spec s
  ((n.val : ZMod scalar), s)

/-- The endomorphism expansion of a 128-bit prechallenge (Halo §6.2): fold its 2-bit windows
from the top into accumulators starting at `a = b = 2`; the result is `a·λ + b`. -/
def endoExpand {F : Type*} [Field F] (lam : F) (chal : ℕ) : F :=
  let (a, b) := (List.range 64).reverse.foldl
    (fun (ab : F × F) i =>
      let (a, b) := (2 * ab.1, 2 * ab.2)
      let s : F := if chal.testBit (2 * i) then 1 else -1
      if chal.testBit (2 * i + 1) then (a + s, b) else (a, b + s))
    (2, 2)
  a * lam + b

/-- Squeeze an effective scalar challenge: a prechallenge endo-expanded at the eigenvalue
`lam`. -/
def squeezeChallenge (spec : Spec base scalar) (lam : ZMod scalar) (s : S base) :
    ZMod scalar × S base :=
  let (n, s) := challengeNat spec s
  (endoExpand lam n.val, s)


end Poseidon.FqSponge

namespace Poseidon

/-! ## The Pasta instantiations -/

namespace FqVesta

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The Vesta side of the cycle: the sponge over the Vesta base field (`fqParams`). -/
def spec : FqSponge.Spec PALLAS_SCALAR_CARD PALLAS_BASE_CARD where
  params := fqParams
  hsize := by
    show (FqKimchi.roundConstants.map _).size = fullRounds
    rw [Array.size_map]
    rfl

end FqVesta

namespace FqPallas

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The Pallas side of the cycle: the sponge over the Pallas base field (`fpParams`). Its
scalar field is the larger, so `absorbFr` takes the high-bits/low-bit branch. -/
def spec : FqSponge.Spec PALLAS_BASE_CARD PALLAS_SCALAR_CARD where
  params := fpParams
  hsize := by
    show (FpKimchi.roundConstants.map _).size = fullRounds
    rw [Array.size_map]
    rfl

end FqPallas

end Poseidon
