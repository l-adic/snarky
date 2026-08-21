import Poseidon.FqSponge
import Poseidon.RandomOracle
import Pasta.Basic
import Kimchi.Gate.Semantics.VarBaseMul

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

/-- **Protocol completeness.** The honest prover convinces the verifier: for any key
`x` and nonce `r`, the statement `⟨[x]·G, [r]·G, r + c·x⟩` — `c` its own challenge —
passes `verify`, unconditionally. Scalars act through their residues mod the prime
group order, so the check is `z = r + c·x` in `Fp`. This is also the exhibit that
`verify` accepts: the circuit laws' acceptance hypotheses are satisfiable. -/
theorem completeness (x r : Fp) :
    verify ⟨x.val • gen, r.val • gen,
      r + FqSponge.endoExpand FqVesta.spec.lam
        (preChallenge (x.val • gen) (r.val • gen)) * x⟩ = true := by
  simp only [verify, decide_eq_true_eq]
  set c : Fp := FqSponge.endoExpand FqVesta.spec.lam
    (preChallenge (x.val • gen) (r.val • gen)) with hc
  have hsmul : ∀ a b : ℤ, ((a : ZMod PALLAS_BASE_CARD) = (b : ZMod PALLAS_BASE_CARD)) →
      ∀ P : Vesta.curve.toAffine.Point, a • P = b • P := fun a b hab P =>
    Kimchi.Gate.VarBaseMul.smul_eq_smul_of_zmod_eq _ (by
      rw [ZMod.intCast_eq_intCast_iff] at hab ⊢
      rwa [Pasta.vesta_card])
  apply (SWPoint.equivPoint Vesta.curve).injective
  simp only [map_add, map_nsmul]
  rw [← mul_nsmul, ← add_nsmul, ← natCast_zsmul, ← natCast_zsmul]
  refine hsmul _ _ ?_ (SWPoint.equivPoint Vesta.curve gen)
  push_cast [ZMod.natCast_val, ZMod.cast_id]
  ring

end Schnorr
