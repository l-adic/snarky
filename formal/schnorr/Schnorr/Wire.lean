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

/-- The sponge state after the transcript: the generator and the statement's two
points absorbed, before the challenge squeeze. Factored so the circuit-alignment
lemma and the two verifiers all name the same object. -/
def squeezeState (pk u : SWPoint Vesta.curve) :
    FqSponge.S PALLAS_SCALAR_CARD :=
  let s := FqSponge.init
  let s := FqSponge.absorbG FqVesta.spec s gen
  let s := FqSponge.absorbG FqVesta.spec s pk
  FqSponge.absorbG FqVesta.spec s u

/-- The raw squeezed field element (`Fq`), before truncation — what the circuit's
`squeezeTranscript` reads from the last permutation's first rate slot, and what the
wire's `challengeNat` takes the low 128 bits of. -/
def squeezeFieldElement (pk u : SWPoint Vesta.curve) : Fq :=
  (Poseidon.squeeze FqVesta.spec.params (squeezeState pk u).sponge).1

/-- The wire's canonical 128-bit prechallenge: the low 128 bits of the CANONICAL
representative of the squeeze. `challengeNat` packs `lowLimbs`, which is exactly this
(`squeezeFieldElement.val < q < 2^255`) — this is `FqSponge.challengeNat` on
the transcript state, packed limb for limb. -/
def preChallenge (pk u : SWPoint Vesta.curve) : ℕ :=
  (squeezeFieldElement pk u).val % 2 ^ 128

/-- The wire verifier: `[z]·G = u + [c]·pk`, `c` the transcript's endo-expanded
128-bit challenge — the whole protocol as one executable check. -/
def verify (st : Statement) : Bool :=
  decide (st.z.val • gen
    = st.u + (FqSponge.endoExpand FqVesta.spec.lam (preChallenge st.pk st.u)).val • st.pk)

/-- The RELAXED verifier: the challenge is any 128-bit prechallenge that reconstructs
the squeeze in `Fq` — `c + 2^128·hi = squeeze` with both halves 128-bit — endo-expanded
and applied. This is what the circuit actually enforces: the range check pins `c` only
up to the squeeze's integer preimages (`0` has preimages `{0, q, 2q, 3q}` in
`[0, 2^256)`, each with different low bits), so soundness terminates here.
`verify` is the special case `c = ⌊squeeze⌋ mod 2^128` (`verify_imp_verifyRelaxed`).
The honest prover always witnesses that canonical `c`, so completeness targets
`verify`. -/
def verifyRelaxed (st : Statement) : Prop :=
  ∃ c hi : ℕ, c < 2 ^ 128 ∧ hi < 2 ^ 128 ∧
    (c : Fq) + (2 : Fq) ^ 128 * (hi : Fq) = squeezeFieldElement st.pk st.u ∧
    st.z.val • gen
      = st.u + (FqSponge.endoExpand FqVesta.spec.lam c).val • st.pk

/-- The wire verifier's acceptance is the relaxed verifier's canonical witness: the
free bridge. Soundness will land on `verifyRelaxed`; this closes the gap to `verify`
in the direction that always holds. -/
theorem verify_imp_verifyRelaxed (st : Statement) (h : verify st = true) :
    verifyRelaxed st := by
  simp only [verify, decide_eq_true_eq] at h
  refine ⟨preChallenge st.pk st.u, (squeezeFieldElement st.pk st.u).val / 2 ^ 128,
    Nat.mod_lt _ (by positivity), ?_, ?_, h⟩
  · have := (squeezeFieldElement st.pk st.u).val_lt
    have hq : PALLAS_SCALAR_CARD < 2 ^ 128 * 2 ^ 128 := by decide
    omega
  · have hrepr : preChallenge st.pk st.u
        + 2 ^ 128 * ((squeezeFieldElement st.pk st.u).val / 2 ^ 128)
        = (squeezeFieldElement st.pk st.u).val := by
      rw [preChallenge, Nat.mod_add_div]
    calc (preChallenge st.pk st.u : Fq)
          + (2 : Fq) ^ 128 * (((squeezeFieldElement st.pk st.u).val / 2 ^ 128 : ℕ) : Fq)
        = ((preChallenge st.pk st.u
            + 2 ^ 128 * ((squeezeFieldElement st.pk st.u).val / 2 ^ 128) : ℕ) : Fq) := by
          push_cast; ring
      _ = ((squeezeFieldElement st.pk st.u).val : Fq) := by rw [hrepr]
      _ = squeezeFieldElement st.pk st.u := ZMod.natCast_rightInverse _

end Schnorr
