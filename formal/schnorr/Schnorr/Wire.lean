import Poseidon.FqSponge
import Poseidon.RandomOracle

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
not by zkdocs' `H(g, q, h, u) mod p`: hash the generator and the statement's points
coordinate by coordinate with the Vesta-side random oracle (`transcriptHash` — a
single squeeze, so the block-mode `Poseidon.RandomOracle.hash` and the duplex
Fq-sponge's absorb-then-squeeze are the same element, `hash_eq_squeeze`), truncate to
a 128-bit prechallenge, and let it act through the endomorphism expansion
(`FqSponge.endoExpand`, the `a·λ + b` map into `Fp`). Fixing this convention on the
wire makes the in-circuit challenge — the hash gadget, a 128-bit truncation, and the
EndoScalar/EndoMul pair — agree with the wire by the gadget laws alone. The group
order is not absorbed: it is fixed by the instantiation.
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

/-- The transcript hash (`Fq`), before truncation: the generator and the statement's
two points, coordinate by coordinate, through the random oracle. The kimchi wire
verifier absorbs points into the duplex Fq-sponge and squeezes; a single squeeze is
the block-mode hash of the absorbed coordinates (`hash_eq_squeeze`), so the hash IS
that squeeze. -/
def transcriptHash (pk u : SWPoint Vesta.curve) : Fq :=
  Poseidon.RandomOracle.hash Poseidon.fqParams [gen.x, gen.y, pk.x, pk.y, u.x, u.y]

/-- The wire's canonical 128-bit prechallenge: the low 128 bits of the CANONICAL
representative of the transcript hash. This is the Fq-sponge `challenge` convention:
`FqSponge.challengeNat` packs a fresh squeeze's two low 64-bit limbs, which is exactly
this (`(transcriptHash pk u).val < q < 2^255`). -/
def preChallenge (pk u : SWPoint Vesta.curve) : ℕ :=
  (transcriptHash pk u).val % 2 ^ 128

/-- The wire verifier: `[z]·G = u + [c]·pk`, `c` the transcript's endo-expanded
128-bit challenge — the whole protocol as one executable check. -/
def verify (st : Statement) : Bool :=
  decide (st.z.val • gen
    = st.u + (FqSponge.endoExpand FqVesta.spec.lam (preChallenge st.pk st.u)).val • st.pk)

/-- The RELAXED verifier: the challenge is any 128-bit prechallenge that reconstructs
the transcript hash in `Fq` — `c + 2^128·hi = hash` with both halves 128-bit —
endo-expanded and applied. This is what the circuit actually enforces: the range check
pins `c` only up to the hash's integer preimages (`0` has preimages `{0, q, 2q, 3q}`
in `[0, 2^256)`, each with different low bits), so soundness terminates here.
`verify` is the special case `c = ⌊hash⌋ mod 2^128` (`verify_imp_verifyRelaxed`).
The honest prover always witnesses that canonical `c`, so completeness targets
`verify`. -/
def verifyRelaxed (st : Statement) : Prop :=
  ∃ c hi : ℕ, c < 2 ^ 128 ∧ hi < 2 ^ 128 ∧
    (c : Fq) + (2 : Fq) ^ 128 * (hi : Fq) = transcriptHash st.pk st.u ∧
    st.z.val • gen
      = st.u + (FqSponge.endoExpand FqVesta.spec.lam c).val • st.pk

/-- The wire verifier's acceptance is the relaxed verifier's canonical witness: the
free bridge. Soundness will land on `verifyRelaxed`; this closes the gap to `verify`
in the direction that always holds. -/
theorem verify_imp_verifyRelaxed (st : Statement) (h : verify st = true) :
    verifyRelaxed st := by
  simp only [verify, decide_eq_true_eq] at h
  refine ⟨preChallenge st.pk st.u, (transcriptHash st.pk st.u).val / 2 ^ 128,
    Nat.mod_lt _ (by positivity), ?_, ?_, h⟩
  · have := (transcriptHash st.pk st.u).val_lt
    have hq : PALLAS_SCALAR_CARD < 2 ^ 128 * 2 ^ 128 := by decide
    omega
  · have hrepr : preChallenge st.pk st.u
        + 2 ^ 128 * ((transcriptHash st.pk st.u).val / 2 ^ 128)
        = (transcriptHash st.pk st.u).val := by
      rw [preChallenge, Nat.mod_add_div]
    calc (preChallenge st.pk st.u : Fq)
          + (2 : Fq) ^ 128 * (((transcriptHash st.pk st.u).val / 2 ^ 128 : ℕ) : Fq)
        = ((preChallenge st.pk st.u
            + 2 ^ 128 * ((transcriptHash st.pk st.u).val / 2 ^ 128) : ℕ) : Fq) := by
          push_cast; ring
      _ = ((transcriptHash st.pk st.u).val : Fq) := by rw [hrepr]
      _ = transcriptHash st.pk st.u := ZMod.natCast_rightInverse _

end Schnorr
