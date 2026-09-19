import Pickles.TwoHalves

/-!
# The step circuit's group half, at an environment

`Step_verifier.verify` with the deployed Pallas constants, and the capstone that runs it: the
pallas counterpart of `wrapVerify_kimchiVerify_vesta`. Unlike the wrap block this one
computes `x_hat` itself, from the key's Lagrange tables (`XhatTable.Bound`), so the public
input is the packed statement's rather than a free argument.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- `verify` at the deployed step constants: the Pallas scalar ops, endomorphism, sponge and
group map. -/
def verifyProofAt {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {nc ks : ℕ}
    (endo : FVar Fp) (sqrtF : Fp → Option Fp) (blindingH : AffinePoint (FVar Fp))
    (tab : XhatTable Fp nc) (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    {k : ℕ}
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    CircuitM Fp c (BoolVar Fp) :=
  verifyProof IpaScalarOps.step IpaEndo.pallas IpaPallas.curve.sponge.params endo
    groupMapParamsPallas sqrtF blindingH tab spongeAfterIndex isBaseCase statement u cells

/-- **Running `Step_verifier.verify`, a wrap proof's remaining half makes `kimchiVerify`
accept.** `twoHalves_kimchiVerify_pallas` as a triple about the group circuit, with the next
wrap circuit's scalar half assumed. The public input is the packed statement's, bound to the
key by the `x_hat` tables. -/
theorem verifyProofAt_kimchiVerify_pallas
    (E : Env IpaPallas.curve)
    (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
    -- the step circuit: its valuation, its constants, its tables and cells
    (Vg : Valuation Fp)
    (endo : FVar Fp) (sqrtF : Fp → Option Fp) (blindingH : AffinePoint (FVar Fp))
    (tab : XhatTable Fp 1) (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    {ks : ℕ}
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (claimsG : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads Vg isBaseCase false)
    (htab : tab.Bound pastaShapePallas Vg E.σ E.cvk blindingH (packLeaves statement tab))
    (hivp : IvpHyps (stepSide Vg) E.σ E.cvk cp
      (pubOf IpaPallas.curve Vg (packLeaves statement tab)) false blindingH spongeAfterIndex
      (cells.withClaims claimsG) oldsW)
    (hguard : Guards IpaPallas.curve E.cvk cp
      (pubOf IpaPallas.curve Vg (packLeaves statement tab)))
    -- the next wrap circuit's scalar half
    (Vs : Valuation Fq)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : AllEvals (FVar Fq))
    (prevChallenges : Vector (Vector Fq E.σ.k) MaxProofsVerified)
    (outS : FopOutput Fq)
    (hs : FopVerifyReads (p := IpaPallas.curve.scalar)
      (FopParams.ofEnv E Linearization.fqTokens) false E.cvk.n E.cvk.omega
      (recDigest IpaPallas.curve (cp.olds.map (·.u)))
      (Vector.replicate MaxProofsVerified true).toList
      (prevChallenges.toList.map Vector.toList) claimsS evals IpaPallas.curve.lam
      (fopWrap Vs).read (fopWrap Vs).unshiftV Vs outS)
    -- across the two, at whichever bit the circuit returns
    (ht : ∀ v : BoolVar Fp, HalvesTies E cp
      (pubOf IpaPallas.curve Vg (packLeaves statement tab))
      (GroupHalf.step Vg claimsG v) (ScalarHalf.wrap Vs claimsS evals prevChallenges outS)) :
    ⦃⌜True⌝⦄
    verifyProofAt (c := Builder Vg (KimchiConstraint Fp)) endo sqrtF blindingH tab
      spongeAfterIndex isBaseCase statement claimsG cells
    ⦃⇓ v _ => ⌜((↑v : CVar Fp).val Vg = 1 ∧ (↑outS.finalized : CVar Fq).val Vs = 1)
        ∧ SgOk E cp (pubOf IpaPallas.curve Vg (packLeaves statement tab))
      → kimchiVerify IpaPallas.curve E.σ E.cvk cp
          (pubOf IpaPallas.curve Vg (packLeaves statement tab)) = true ∧
        (ScalarHalf.wrap Vs claimsS evals prevChallenges outS).ClaimsHonest E cp
          (pubOf IpaPallas.curve Vg (packLeaves statement tab))⌝⦄ := by
  refine builder_spec_imp _ _ _
    (verifyProof_step_reads (V := Vg) E.σ E.cvk cp endo sqrtF blindingH tab spongeAfterIndex
      isBaseCase statement claimsG cells false oldsW hbase htab hivp) ?_
  intro v hv
  exact twoHalves_kimchiVerify_pallas E cp _ hguard Vg claimsG v hv Vs claimsS evals
    prevChallenges outS hs (ht v)

end Pickles
