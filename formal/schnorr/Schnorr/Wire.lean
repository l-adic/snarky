import Poseidon.FqSponge
import Poseidon.RandomOracle

/-!
# Schnorr identification over Vesta — the wire protocol

Non-interactive Schnorr identification
(https://www.zkdocs.com/docs/zkdocs/zero-knowledge-protocols/schnorr/) at the
deployed Pasta instantiation: a prover holding `x` with `pk = [x]·G` commits
`u = [r]·G` and responds `z = r + c·x`; the verifier checks `[z]·G = u + [c]·pk`.
`verify` is that check as one executable function — the specification the circuit
laws terminate at.

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

/-- The generator: the prime-order Vesta point `(-1, 2)` — a constant of this
package, not a Mina-specified base. -/
def gen : SWPoint Vesta.curve := ⟨-1, 2, Or.inl (by decide)⟩

/-- The statement: the public key `[x]·G`, the commitment `[r]·G`, and the response
`z = r + c·x`. -/
structure Statement where
  /-- The public key `[x]·G`. -/
  pk : SWPoint Vesta.curve
  /-- The prover's commitment `[r]·G`. -/
  u : SWPoint Vesta.curve
  /-- The response `r + c·x`, a Vesta scalar. -/
  z : Fp

/-- The transcript hash, before truncation: the generator and statement coordinates
through the random oracle. A single squeeze is the block-mode hash of the absorbed
coordinates (`hash_eq_squeeze`), so this IS the Fq-sponge's squeeze. -/
def transcriptHash (pk u : SWPoint Vesta.curve) : Fq :=
  Poseidon.RandomOracle.hash Poseidon.fqParams [gen.x, gen.y, pk.x, pk.y, u.x, u.y]

/-- The canonical 128-bit prechallenge: the low 128 bits of the transcript hash's
canonical representative — the Fq-sponge `challengeNat` convention. -/
def preChallenge (pk u : SWPoint Vesta.curve) : ℕ :=
  (transcriptHash pk u).val % 2 ^ 128

/-- The wire verifier: `[z]·G = u + [c]·pk`, `c` the transcript's endo-expanded
128-bit challenge — the whole protocol as one executable check. -/
def verify (st : Statement) : Bool :=
  decide (st.z.val • gen
    = st.u + (FqSponge.endoExpand FqVesta.spec.lam (preChallenge st.pk st.u)).val • st.pk)

/-- The RELAXED verifier: the challenge is any 128-bit split reconstructing the
transcript hash in `Fq`, endo-expanded and applied — all the range check pins (`0`
has preimages `{0, q, 2q, 3q}`, each with different low bits). Soundness terminates
here; `verify` is the canonical case, and completeness targets it. -/
def verifyRelaxed (st : Statement) : Prop :=
  ∃ c hi : ℕ, c < 2 ^ 128 ∧ hi < 2 ^ 128 ∧
    (c : Fq) + (2 : Fq) ^ 128 * (hi : Fq) = transcriptHash st.pk st.u ∧
    st.z.val • gen
      = st.u + (FqSponge.endoExpand FqVesta.spec.lam c).val • st.pk

/-- `verify` supplies the relaxed verifier's canonical witness — the free bridge. -/
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
