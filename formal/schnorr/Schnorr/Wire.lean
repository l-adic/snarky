import Poseidon.FqSponge

/-!
# Schnorr identification over Vesta — the wire protocol

The verifier-faithfulness exemplar's wire side: non-interactive Schnorr identification
(https://www.zkdocs.com/docs/zkdocs/zero-knowledge-protocols/schnorr/) at the deployed
Pasta instantiation. A prover holding `x` with `pk = [x]·G` commits `u = [r]·G` and
responds `z = r + c·x`; the verifier derives the challenge from the transcript and
checks `[z]·G = u + [c]·pk`. `verify` below is that check as one executable function —
the specification the in-circuit implementation's laws terminate at, the way the
kimchi circuit laws terminate at the wire verifier's own definitions.

## The field layout

Points live on Vesta, so coordinates are Vesta base-field elements (`Fq`, the Pallas
scalar field) and the exponents `x`, `r`, `z`, `c` are Vesta scalar-field elements
(`Fp`, order `p = #Vesta`). The circuit implementing `verify` is therefore an
`Fq`-circuit with native Vesta group arithmetic, receiving `z` across the field
boundary (Type1: `p < q`, one shifted element).

## The challenge convention

The challenge is derived the way the kimchi verifier derives its scalar challenges,
not by zkdocs' `H(g, q, h, u) mod p`: absorb the generator and the statement's points
into the Vesta-side Fq-sponge, squeeze one 128-bit prechallenge, and let it act
through the endomorphism expansion (`FqSponge.squeezeChallenge`, the `a·λ + b` map
into `Fp`). Fixing this convention on the wire makes the in-circuit challenge — a
Poseidon squeeze, a 128-bit truncation, and the EndoScalar/EndoMul pair — agree with
the wire by the gadget laws alone. The group order is not absorbed: it is fixed by
the instantiation.
-/

namespace Schnorr

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon

/-- The exemplar's generator: CompElliptic's prime-order Vesta point `(-1, 2)`. A
protocol constant of this package, not a Zcash- or Mina-specified base. -/
def gen : SWPoint Vesta.curve := ⟨-1, 2, Or.inl (by decide)⟩

/-- The statement: the public key, the commitment, and the response. The witness —
`x` with `pk = [x]·G` and `r` with `u = [r]·G` — is what the honest prover holds;
`z = r + c·x` is its response to the derived challenge. -/
structure Statement where
  /-- The public key `[x]·G`. -/
  pk : SWPoint Vesta.curve
  /-- The prover's commitment `[r]·G`. -/
  u : SWPoint Vesta.curve
  /-- The response `r + c·x`, a Vesta scalar. -/
  z : Fp

/-- The Fiat–Shamir challenge: absorb the generator, the public key, and the
commitment into the Vesta-side sponge; squeeze one 128-bit prechallenge,
endo-expanded into the scalar field (the kimchi challenge convention). -/
def challenge (pk u : SWPoint Vesta.curve) : Fp :=
  let s := FqSponge.init
  let s := FqSponge.absorbG FqVesta.spec s gen
  let s := FqSponge.absorbG FqVesta.spec s pk
  let s := FqSponge.absorbG FqVesta.spec s u
  (FqSponge.squeezeChallenge FqVesta.spec s).1

/-- The wire verifier: `[z]·G = u + [c]·pk` with `c` the transcript challenge —
the whole protocol as one executable check, and the exemplar's specification. -/
def verify (st : Statement) : Bool :=
  decide (st.z.val • gen = st.u + (challenge st.pk st.u).val • st.pk)

end Schnorr
