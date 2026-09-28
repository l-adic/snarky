import Pickles.Encoding
import Pickles.TwoHalves

/-!
# The wrap circuit's scalar half, at an environment

`finalizeOtherProofWrap` with its parameters fixed to the verifier key's (`FopParams.ofEnv`),
the deployed `Fq` linearization and the key's own domain, and the capstone that runs it: the
wrap-side twin of `finalizeOtherProofStepAt_kimchiVerify_vesta`. The two halves of a wrap
proof's verification run in different circuits over different fields, so no one triple covers
both; each side gets a triple about its own circuit, with the other half assumed.

The domain is a constant of the circuit — the generator the key's, `ζⁿ − 1` by `pow2PowMul` at
the key's `log2` — so what the gadget's read owes about it (the generator's order, room for the
zero-knowledge rows) is the environment's, and there is no domain cell to tie. The wrap side
keeps every previous-challenge slot. Like the step side's, the capstone is an equivalence.

`WrapProof.scalarCircuit` is the gadget as a circuit of its input (`WrapProof.ScalarIn`) with
`finalized` asserted: what the wrap proof's top-level statement compiles
(`wrapProof_kimchiVerify_pallas`). Nothing in that input is checked on allocation — the wrap
side has no branch data — so compiling fixes the cells and derives nothing.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open Kimchi.Protocol.Linearization Poseidon.FqSponge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The wrap side's input at `k` rounds and `nc` chunks, as values. -/
abbrev WrapFop (k nc : ℕ) : Type := FopInput k nc Fq Bool (Type2 Fq)

/-- The wrap side's input at `k` rounds and `nc` chunks, as cells. -/
abbrev WrapFopVar (k nc : ℕ) : Type := FopInput k nc (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq))

/-- The wrap circuit's scalar half at an environment: `finalizeOtherProofWrap` with the
verifier key's parameters and domain — its generator a constant, `ζⁿ − 1` by `pow2PowMul`
at the key's `log2` — the `Fq` token stream, and the previous-challenge cells at their static
size. -/
def finalizeOtherProofWrapAt {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c] {k nc : ℕ}
    (E : Env IpaPallas.curve nc)
    (u : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (w : ChunkedEvals nc (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) k) MaxProofsVerified) :
    CircuitM Fq c (FopOutput Fq) :=
  finalizeOtherProofWrap (FopParams.ofEnv E Linearization.fqTokens) (.const E.cvk.omega)
    (fun z => do
      let t ← pow2PowMul z E.cvk.domainLog2
      pure (CVar.sub_ t (.const 1)))
    u w (prevChallenges.toList.map Vector.toList)

/-- `ζ^{2^log2} − 1` by `pow2PowMul`: the vanishing polynomial of a constant domain. -/
private theorem vanishingAt_spec {V : Valuation Fq} (log2 : ℕ) (z : FVar Fq) :
    ⦃⌜True⌝⦄
    (do let t ← pow2PowMul (c := Builder V (KimchiConstraint Fq)) z log2
        pure (CVar.sub_ t (.const 1)))
    ⦃⇓ v _ => ⌜v.val V = z.val V ^ 2 ^ log2 - 1⌝⦄ := by
  have hp := pow2PowMul_spec (V := V) (c := KimchiConstraint Fq) z log2
  mvcgen [hp]
  rename_i t _ ht
  simp [ht]

/-! ## The claims across the two circuits -/

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
  w.bulletproofChallenges.toList.map (·.val.val Vs)
    = g.bulletproofChallenges.toList.map fun c => redFq (c.val.val Vg)

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
    (hch : ∃ ms, List.Forall₂ (Reads128 Vs) claimsS.deferredValues.bulletproofChallenges.toList
      ms) :
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
  have hlen : ms.length = k := by simpa using hms.length_eq.symm
  let s := claimsS.deferredValues
  let dec := (fopWrap Vs).decode
  let dv : DeferredValues k Prechallenge Fq :=
    { plonk := { alpha := ⟨a⟩, beta := ⟨b⟩, gamma := ⟨g⟩, zeta := ⟨z⟩, perm := dec s.plonk.perm
                 zetaToSrsLength := dec s.plonk.zetaToSrsLength
                 zetaToDomainSize := dec s.plonk.zetaToDomainSize }
      combinedInnerProduct := dec s.combinedInnerProduct, xi := ⟨ξ⟩
      bulletproofChallenges := ⟨(ms.map SizedF.mk).toArray, by simp [hlen]⟩
      b := dec s.b }
  have hchals : dv.bulletproofChallenges.toList.map (·.val) = ms := by
    simp [dv, Function.comp_def]
  -- a split claim decodes, on the step side, as its joined cell on the wrap side
  have hdec : ∀ (x : Type2 (SplitField (FVar Fp) (BoolVar Fp))) (y : Type2 (FVar Fq)),
      y.val.val Vs = 2 * redFq (x.val.sDiv2.val Vg) + redFq ((↑x.val.sOdd : CVar Fp).val Vg) →
      (stepSide Vg).decode x = dec y := by
    intro x y hxy
    simp only [dec, FopSide.decode, fopWrap, wrapShiftOps.reading, Type2.fromShifted, hxy,
      stepSide, stepDecode, Pasta.Shifted.unshiftType2]
  refine ⟨⟨dv, ⟨reads128_of_redFq cα ha, hb, hg, reads128_of_redFq cζ hz, hdec _ _ cperm,
      hdec _ _ czm, hdec _ _ czn, hdec _ _ ccip, reads128_of_redFq cξ hxi,
      hchals ▸ forall₂_reads128_of_redFq hms _ hbp, hdec _ _ cb⟩,
    ⟨ha, reads128_redFq cβ hb, reads128_redFq cγ hg, hz, rfl, rfl, rfl, rfl, hxi,
      hchals ▸ hms, rfl⟩⟩, ?_⟩
  show claimsS.spongeDigestBeforeEvaluations.val Vs
    = castDigest IpaPallas.curve (claimsG.spongeDigestBeforeEvaluations.val Vg)
  rw [cdig, castDigest_pallas]

/-- **Running the wrap circuit's scalar half, a wrap proof's remaining half decides
`kimchiVerify`.** `twoHalves_kimchiVerify` at a wrap proof as a triple about the scalar circuit,
with the step circuit's group half assumed (`verifyProof_step_reads` produces it). What the
circuit's parameters and domain owe is the environment's; what is left is the ties. -/
theorem finalizeOtherProofWrapAt_kimchiVerify_pallas {nc : ℕ}
    (E : Env IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc E.σ.k)
    (pub : Array Fq)
    (hguard : Guards IpaPallas.curve E.cvk cp pub)
    -- the wrap circuit: its valuation and its cells
    (Vs : Valuation Fq)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : ChunkedEvals nc (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) E.σ.k) MaxProofsVerified)
    -- the step circuit's group half, and its asserted bit
    (Vg : Valuation Fp)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (successG : BoolVar Fp)
    (hg : (GroupHalf.step Vg claimsG).Reads E cp pub successG)
    (hgbit : (↑successG : CVar Fp).val Vg = 1)
    -- across the two
    (hc : SplitClaimsCast Vg claimsG Vs claimsS)
    (hf : FopTies E cp pub (ScalarHalf.wrap Vs claimsS evals prevChallenges)) :
    ⦃⌜True⌝⦄
    finalizeOtherProofWrapAt (c := Builder Vs (KimchiConstraint Fq)) E claimsS evals
      prevChallenges
    ⦃⇓ o _ => ⌜SgOk E.σ E.cvk cp pub ∧ (↑o.finalized : CVar Fq).val Vs = 1
      ↔ kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true ∧
        (ScalarHalf.wrap Vs claimsS evals prevChallenges).ClaimsHonest E cp pub⌝⦄ := by
  have hP : (FopParams.ofEnv E Linearization.fqTokens).endo = Pasta.vestaEndo ∧
      (FopParams.ofEnv E Linearization.fqTokens).mds = Reflect.symMdsQ ∧
      (FopParams.ofEnv E Linearization.fqTokens).toks = Linearization.fqTokens :=
    ⟨E.endo_eq, by rfl, rfl⟩
  -- the vanishing polynomial at the key's domain
  have hvan : ∀ z : FVar Fq, ⦃⌜True⌝⦄
      (do let t ← pow2PowMul (c := Builder Vs (KimchiConstraint Fq)) z E.cvk.domainLog2
          pure (CVar.sub_ t (.const 1)))
      ⦃⇓ v _ => ⌜v.val Vs = z.val Vs ^ E.cvk.n - 1⌝⦄ :=
    fun z => vanishingAt_spec E.cvk.domainLog2 z
  -- the cells read as their own values
  have hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads Vs))
      (prevChallenges.toList.map Vector.toList)
      (ScalarHalf.wrap Vs claimsS evals prevChallenges).prevVals := by
    refine List.forall₂_map_right_iff.2 (List.forall₂_map_left_iff.2
      (List.forall₂_same.2 fun cs _ => ?_))
    exact List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun x _ => CircuitType.reads_fvar.2 rfl)
  have hspec := finalizeOtherProofWrap_spec_fq (V := Vs)
    (FopParams.ofEnv E Linearization.fqTokens) hP IpaPallas.curve.frSponge.hsize E.zkRows_ge
    (.const E.cvk.omega) E.cvk.n E.zkRows_le E.omega_prim.pow_eq_one _ hvan claimsS evals
    (prevChallenges.toList.map Vector.toList) _ hprev
  simp only [finalizeOtherProofWrapAt]
  refine builder_spec_imp _ _ _ hspec ?_
  intro o hread
  -- the two halves hold one set of claims: `β`, `γ` read on the step side, the rest here
  have ht : HalvesTies (GroupHalf.step Vg claimsG)
      (ScalarHalf.wrap Vs claimsS evals prevChallenges) := by
    obtain ⟨og, hivp, -⟩ := hg
    obtain ⟨a₀, z₀, hα, hζ, ξ₀, -, ĉ, hξ, -, -, -, -, hĉ, -⟩ := hread
    exact halvesTies_of_splitCast Vg claimsG Vs claimsS evals prevChallenges hc
      ⟨_, hivp.2.1⟩ ⟨_, hivp.2.2.1⟩ ⟨a₀, hα⟩ ⟨z₀, hζ⟩ ⟨ξ₀, hξ⟩ ⟨ĉ, hĉ⟩
  -- the circuit absorbs every previous-challenge cell; their values are the proof's accumulators
  have holds : (ScalarHalf.wrap Vs claimsS evals prevChallenges).prevVals
      = (cp.olds.map (·.u.toList)).toList :=
    (ScalarHalf.wrap_olds Vs claimsS evals prevChallenges _).mp hf.olds
  have hdv : (Poseidon.squeeze (FopParams.ofEnv E Linearization.fqTokens).sponge
        (Poseidon.absorb (FopParams.ofEnv E Linearization.fqTokens).sponge Poseidon.init
          ((prevChallenges.toList.map Vector.toList).flatten.map (·.val Vs)))).1
      = recDigest IpaPallas.curve (cp.olds.map (·.u)) := by
    have habs : (prevChallenges.toList.map Vector.toList).flatten.map (·.val Vs)
        = ((cp.olds.map (·.u)).toList.map Vector.toList).flatten := by
      have h1 : (prevChallenges.toList.map Vector.toList).flatten.map (·.val Vs)
          = ((ScalarHalf.wrap Vs claimsS evals prevChallenges).prevVals).flatten := by
        simp [ScalarHalf.prevVals, ScalarHalf.wrap, List.map_flatten, List.map_map,
          Function.comp_def]
      rw [h1, holds]
      simp [Function.comp_def]
    rw [habs]
    rfl
  have hmask : (List.map (fun _ => true) (prevChallenges.toList.map Vector.toList))
      = (ScalarHalf.wrap Vs claimsS evals prevChallenges).maskVals := by
    rw [ScalarHalf.wrap_maskVals]
    simp
  rw [hdv, hmask] at hread
  rw [← twoHalves_kimchiVerify E (by norm_num [PALLAS_BASE_CARD])
    (by norm_num [PALLAS_SCALAR_CARD]) cp pub hguard _ successG hg _ o hread ht hf]
  exact ⟨fun h => ⟨⟨hgbit, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

/-! ## The circuit of its input -/

namespace WrapProof

variable {k nc : ℕ}

/-- The scalar circuit's input: the slot's claims, the evaluations, the previous challenges.
Nothing in it is checked on input. -/
abbrev ScalarIn (k nc : ℕ) : Type := UnChecked (WrapFop k nc)
/-- `ScalarIn`, as cells. -/
abbrev ScalarVar (k nc : ℕ) : Type := UnChecked (WrapFopVar k nc)

/-- The slot's deferred claims. -/
def ScalarVar.claims (s : ScalarVar k nc) :
    UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)) := s.val.claims
/-- The evaluation cells. -/
def ScalarVar.evals (s : ScalarVar k nc) : ChunkedEvals nc (FVar Fq) := s.val.evals
/-- The previous challenges, one vector per slot. -/
def ScalarVar.prev (s : ScalarVar k nc) : Vector (Vector (FVar Fq) k) MaxProofsVerified :=
  s.val.prev
/-- The scalar circuit as a `ScalarHalf`. -/
abbrev ScalarVar.half (V : Valuation Fq) (s : ScalarVar k nc) :
    ScalarHalf IpaPallas.curve (Type2 (FVar Fq)) k nc MaxProofsVerified :=
  ScalarHalf.wrap V s.claims s.evals s.prev

/-- The wrap circuit's scalar half as a circuit of its input, `finalized` asserted, as at a
slot whose `shouldFinalize` is set. -/
def scalarCircuit {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c]
    (E : Env IpaPallas.curve nc) (s : ScalarVar E.σ.k nc) : CircuitM Fq c Unit := do
  let o ← finalizeOtherProofWrapAt E s.claims s.evals s.prev
  assert o.finalized

/-- **The scalar circuit's read.** With the step circuit's group half and the ties, a valuation
satisfying the body makes `kimchiVerify` accept once `SgOk` holds. -/
theorem scalarCircuit_reads (E : Env IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc E.σ.k) (pub : Array Fq)
    (hguard : Guards IpaPallas.curve E.cvk cp pub)
    (Vs : Valuation Fq) (s : ScalarVar E.σ.k nc)
    (Vg : Valuation Fp)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (successG : BoolVar Fp)
    (hg : (GroupHalf.step Vg claimsG).Reads E cp pub successG)
    (hgbit : (↑successG : CVar Fp).val Vg = 1)
    (hc : SplitClaimsCast Vg claimsG Vs s.claims)
    (hf : FopTies E cp pub (s.half Vs))
    (hsg : SgOk E.σ E.cvk cp pub) :
    ⦃⌜True⌝⦄
    scalarCircuit (c := Builder Vs (KimchiConstraint Fq)) E s
    ⦃⇓ _ _ => ⌜kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true⌝⦄ := by
  have hAt := finalizeOtherProofWrapAt_kimchiVerify_pallas E cp pub hguard Vs s.claims s.evals
    s.prev Vg claimsG successG hg hgbit hc hf
  simp only [scalarCircuit]
  mvcgen [hAt]
  rename_i o _ hiff _ _
  intro hfin
  exact (hiff.mp ⟨hsg, hfin⟩).1

end WrapProof

end Pickles

