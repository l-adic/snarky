import Pickles.Encoding
import Pickles.TwoHalves

/-!
# The claims across the two circuits

A wrap proof's verification runs in two circuits over two fields: the step circuit checks its
group half and the next wrap circuit's finalize block its scalar half. The step statement carries
the deferred claims between them, each of the wrap circuit's claim cells the step circuit's value
lifted into the wrap field (`SplitClaimsCast`); from that cast, the two halves read one set of
claims (`halvesTies_of_splitCast`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open Kimchi.Protocol.Linearization Poseidon.FqSponge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The claims the step statement carries across: each of the wrap circuit's claim cells holds
the step circuit's matching value lifted into the wrap field, a split shifted claim as
`2·sDiv2 + sOdd`. -/
def SplitClaimsCast {k : ℕ} (Vg : Valuation Fp)
    (claimsG : UnfinalizedProof k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (Vs : Valuation Fq) (claimsS : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq))) :
    Prop :=
  let g := claimsG.deferredValues
  let w := claimsS.deferredValues
  let join (x : Type2 (SplitField (FVar Fp) (BoolVar Fp))) : Fq :=
    2 * redFq (x.val.sDiv2.val Vg) + redFq ((↑x.val.sOdd : CVar Fp).val Vg)
  [w.plonk.alpha.val, w.plonk.beta.val, w.plonk.gamma.val, w.plonk.zeta.val, w.xi.val,
    claimsS.spongeDigestBeforeEvaluations].map (·.val Vs)
    = [g.plonk.alpha.val, g.plonk.beta.val, g.plonk.gamma.val, g.plonk.zeta.val, g.xi.val,
      claimsG.spongeDigestBeforeEvaluations].map (fun x => redFq (x.val Vg)) ∧
  [w.plonk.perm, w.plonk.zetaToSrsLength, w.plonk.zetaToDomainSize, w.combinedInnerProduct,
    w.b].map (·.val.val Vs)
    = [g.plonk.perm, g.plonk.zetaToSrsLength, g.plonk.zetaToDomainSize, g.combinedInnerProduct,
      g.b].map join ∧
  ∀ i : Fin k,
    w.bulletproofChallenges[i].val.val Vs = redFq (g.bulletproofChallenges[i].val.val Vg)

/-- The step digest crosses into the wrap field through `castDigest` as its representative. -/
private theorem castDigest_pallas (x : Fp) : castDigest IpaPallas.curve x = redFq x := by
  have h : x.val < IpaPallas.curve.scalar := (ZMod.val_lt x).trans fp_lt_fq
  simp only [castDigest, if_pos h]

/-- **The claims cast across make the two halves hold one set of claims.** With the wrap
circuit's claim cells the step circuit's lifted (`SplitClaimsCast`), `β`, `γ` reading as
prechallenges on the step side (the group read) and `α`, `ζ`, `ξ` and the round challenges on the
wrap side (the finalize read), both halves read one deferred-values record. -/
theorem halvesTies_of_splitCast {k nc : ℕ} (Vg : Valuation Fp)
    (claimsG : UnfinalizedProof k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (Vs : Valuation Fq) (claimsS : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : ChunkedEvals nc (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) k) MaxProofsVerified)
    (hc : SplitClaimsCast Vg claimsG Vs claimsS)
    (hβ : ∃ m, Reads128 Vg claimsG.deferredValues.plonk.beta m)
    (hγ : ∃ m, Reads128 Vg claimsG.deferredValues.plonk.gamma m)
    (hα : ∃ m, Reads128 Vs claimsS.deferredValues.plonk.alpha m)
    (hζ : ∃ m, Reads128 Vs claimsS.deferredValues.plonk.zeta m)
    (hξ : ∃ m, Reads128 Vs claimsS.deferredValues.xi m)
    (hch : ∃ ms : Vector Prechallenge k,
      ∀ i : Fin k, Reads128 Vs claimsS.deferredValues.bulletproofChallenges[i] ms[i]) :
    HalvesTies (GroupHalf.step Vg claimsG) (ScalarHalf.wrap Vs claimsS evals prevChallenges) := by
  obtain ⟨hl, hsh, hbp⟩ := hc
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hl hsh
  obtain ⟨cα, cβ, cγ, cζ, cξ, cdig, -⟩ := hl
  obtain ⟨cperm, czm, czn, ccip, cb, -⟩ := hsh
  obtain ⟨b, hb⟩ := hβ
  obtain ⟨g, hg⟩ := hγ
  obtain ⟨a, ha⟩ := hα
  obtain ⟨z, hz⟩ := hζ
  obtain ⟨ξ, hxi⟩ := hξ
  obtain ⟨ms, hms⟩ := hch
  let s := claimsS.deferredValues
  let dec := (fopWrap Vs).decode
  let dv : DeferredValues k Prechallenge Fq :=
    { plonk := { alpha := ⟨a⟩, beta := ⟨b⟩, gamma := ⟨g⟩, zeta := ⟨z⟩, perm := dec s.plonk.perm
                 zetaToSrsLength := dec s.plonk.zetaToSrsLength
                 zetaToDomainSize := dec s.plonk.zetaToDomainSize }
      combinedInnerProduct := dec s.combinedInnerProduct, xi := ⟨ξ⟩
      bulletproofChallenges := ms.map SizedF.mk
      b := dec s.b }
  -- a split claim decodes, on the step side, as its joined cell on the wrap side
  have hdec : ∀ (x : Type2 (SplitField (FVar Fp) (BoolVar Fp))) (y : Type2 (FVar Fq)),
      y.val.val Vs = 2 * redFq (x.val.sDiv2.val Vg) + redFq ((↑x.val.sOdd : CVar Fp).val Vg) →
      (stepSide Vg).decode x = dec y := by
    intro x y hxy
    simp only [dec, FopSide.decode, fopWrap, wrapShiftOps.reading, Type2.fromShifted, hxy,
      stepSide, stepDecode, Pasta.Shifted.unshiftType2]
  refine ⟨⟨dv, ⟨reads128_of_redFq cα ha, hb, hg, reads128_of_redFq cζ hz, hdec _ _ cperm,
      hdec _ _ czm, hdec _ _ czn, hdec _ _ ccip, reads128_of_redFq cξ hxi,
      fun i => by simpa [dv] using reads128_of_redFq (hbp i) (hms i), hdec _ _ cb⟩,
    ⟨ha, reads128_redFq cβ hb, reads128_redFq cγ hg, hz, rfl, rfl, rfl, rfl, hxi,
      fun i => by simpa [dv] using hms i, rfl⟩⟩, ?_⟩
  show claimsS.spongeDigestBeforeEvaluations.val Vs
    = castDigest IpaPallas.curve (claimsG.spongeDigestBeforeEvaluations.val Vg)
  rw [cdig, castDigest_pallas]

end Pickles

