import Kimchi.Sponge.Poseidon
import Kimchi.Pasta.Constants

/-!
# The kimchi Fq-sponge over Vesta

The consumer-facing sponge of kimchi's Fiat-Shamir transform for proofs over Vesta,
transcribed from proof-systems `mina_poseidon` `sponge.rs` (`DefaultFqSponge`) on top of the
duplex automaton of `Poseidon.lean`. The sponge state lives in the Vesta base field `Fq`;
challenges land in the Vesta scalar field `Fr`.

Alongside the Poseidon state, the sponge carries a buffer `lastSqueezed` of 64-bit limbs:
each raw squeeze contributes its two low limbs (128 high-entropy bits), and a scalar
challenge (`challenge`, 128 bits) is packed from the next two buffered limbs. Every
absorption clears the buffer. Field-element squeezes (`challengeFq`) bypass the buffer and
clear it.

A squeezed 128-bit prechallenge becomes an *effective* scalar through the endomorphism
expansion (`sponge.rs` `to_field_with_length`, Halo §6.2): accumulators `a = b = 2`, then for
each 2-bit window from the top, `a, b := 2a, 2b`, the low bit selects `s = ±1`, the high bit
routes `s` into `a` or `b`; the result is `a·λ + b` with `λ = Kimchi.Pasta.vesta_lam`, the
Vesta CM eigenvalue (= proof-systems `endos::<Vesta>().1`). This is the same recoding the
`EndoScalar` gate constrains in-circuit (`Kimchi.Gate.EndoScalar`, accumulator init
`(2, 2)`).

`shiftScalar` is the caller-side encoding of a scalar absorbed into the transcript
(`poly-commitment/src/commitment.rs` `shift_scalar`): for Vesta the scalar modulus is below
the base modulus, so `x ↦ (x − 2²⁵⁵ − 1) / 2` — the inverse of the pickles `Shifted_value`
Type1 map (`Kimchi.Shifted.shiftType1`). Points absorb as their two affine coordinates; the
point at infinity absorbs as a single `0` (`sponge.rs` `absorb_g`).

Validated against the challenge values of the production `SRS::verify` transcript by
`scripts/check_fq_sponge.lean`.

## Contents

* `FqVesta.S`, `init` — the sponge-plus-limb-buffer state.
* `absorbFq`, `absorbG`, `absorbGInfinity`, `absorbFr` — the absorption encodings.
* `challengeFq`, `challengeNat`, `challenge` — raw and 128-bit squeezes.
* `endoExpand`, `squeezeChallenge` — the effective-scalar expansion.
* `shiftScalar` — the absorbed-scalar encoding.
-/

namespace Kimchi.Sponge.FqVesta

open CompElliptic.Fields.Pasta

/-- The sponge field: the Vesta base field. -/
abbrev Fq := VestaBaseField

/-- The challenge field: the Vesta scalar field. -/
abbrev Fr := VestaScalarField

/-- Sponge state: the Poseidon automaton plus the 64-bit limb buffer `lastSqueezed`. -/
structure S where
  sponge : State Fq
  lastSqueezed : List ℕ

/-- The fresh sponge: fresh automaton, empty buffer. -/
def init : S := ⟨Kimchi.Sponge.init, []⟩

/-- The two low 64-bit limbs of a squeezed element — its 128 high-entropy bits
(`HIGH_ENTROPY_LIMBS = 2`). -/
def lowLimbs (x : Fq) : List ℕ :=
  [x.val % 2 ^ 64, x.val / 2 ^ 64 % 2 ^ 64]

/-- Absorb base-field elements (`absorb_fq`): clear the buffer, absorb each. -/
def absorbFq (s : S) (xs : List Fq) : S :=
  ⟨absorb Fq.params s.sponge xs, []⟩

/-- Absorb an affine point (`absorb_g`, non-infinity case): its `x` then its `y`
coordinate. -/
def absorbG (s : S) (p : Fq × Fq) : S :=
  absorbFq s [p.1, p.2]

/-- Absorb the point at infinity (`absorb_g`, infinity case): a single `0`. -/
def absorbGInfinity (s : S) : S :=
  absorbFq s [0]

/-- Absorb a scalar-field element (`absorb_fr`). The Vesta scalar modulus is smaller than
the base modulus, so the value embeds directly (the branch taken by
`DefaultFqSponge<VestaParameters>`; the other branch splits off the low bit). -/
def absorbFr (s : S) (x : Fr) : S :=
  absorbFq s [((x.val : ℕ) : Fq)]

/-- Squeeze a raw base-field element (`challenge_fq` / `squeeze_field`): bypass and clear
the limb buffer. -/
def challengeFq (s : S) : Fq × S :=
  let (x, sp) := squeeze Fq.params s.sponge
  (x, ⟨sp, []⟩)

/-- Take two 64-bit limbs from the buffer, refilling it from the sponge as needed
(`squeeze_limbs` at `CHALLENGE_LENGTH_IN_LIMBS = 2`); the packed 128-bit value. The fuel
argument bounds the refills (each adds two limbs, so one suffices from empty). -/
def squeezeLimbsPacked : ℕ → S → ℕ × S
  | 0, s => (0, s)
  | fuel + 1, s =>
    match s.lastSqueezed with
    | l0 :: l1 :: rest => (l0 + l1 * 2 ^ 64, ⟨s.sponge, rest⟩)
    | buf =>
      let (x, sp) := squeeze Fq.params s.sponge
      squeezeLimbsPacked fuel ⟨sp, buf ++ lowLimbs x⟩

/-- Squeeze a 128-bit prechallenge, as a natural number (`challenge`, before the field
cast). -/
def challengeNat (s : S) : ℕ × S :=
  squeezeLimbsPacked 2 s

/-- Squeeze a 128-bit prechallenge into the scalar field (`challenge`). -/
def challenge (s : S) : Fr × S :=
  let (n, s) := challengeNat s
  ((n : Fr), s)

/-- The endomorphism expansion of a 128-bit prechallenge into an effective scalar
(`to_field_with_length`, Halo §6.2): fold the 2-bit windows from the top into the
accumulators `a = b = 2`; the result is `a·λ + b`. -/
def endoExpand (lam : Fr) (chal : ℕ) : Fr :=
  let (a, b) := (List.range 64).reverse.foldl
    (fun (ab : Fr × Fr) i =>
      let (a, b) := (2 * ab.1, 2 * ab.2)
      let s : Fr := if chal.testBit (2 * i) then 1 else -1
      if chal.testBit (2 * i + 1) then (a + s, b) else (a, b + s))
    (2, 2)
  a * lam + b

/-- Squeeze an effective scalar challenge (`squeeze_challenge`,
`poly-commitment/src/commitment.rs`): a 128-bit prechallenge, endo-expanded at the Vesta
eigenvalue. -/
def squeezeChallenge (s : S) : Fr × S :=
  let (n, s) := challengeNat s
  (endoExpand ((Kimchi.Pasta.vesta_lam : ℤ) : Fr) n, s)

/-- The absorbed-scalar encoding (`shift_scalar`): the Vesta scalar modulus is below the
base modulus, so `x ↦ (x − 2²⁵⁵ − 1) / 2` — the inverse of the pickles `Shifted_value`
Type1 map (255 = the scalar modulus bit size). -/
def shiftScalar (x : Fr) : Fr :=
  (x - (2 ^ 255 + 1)) / 2

end Kimchi.Sponge.FqVesta
