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
keeps every previous-challenge slot and does not constrain the low half of the `ξ` split, so
the capstone is an implication where the step side's is an equivalence
(`twoHalves_kimchiVerify_pallas_converse` is the converse, under `ScalarHalf.XiExact`).

`WrapProof.scalarCircuit` is the gadget as a circuit of its input (`WrapProof.ScalarIn`) with
`finalized` asserted: what the wrap proof's top-level statement compiles
(`wrapProof_kimchiVerify_pallas`). Nothing in that input is checked on allocation — the wrap
side has no branch data — so compiling fixes the cells and derives nothing.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open Kimchi.Protocol.Linearization Poseidon.FqSponge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The wrap side's input at `k` rounds, as values. -/
abbrev WrapFop (k : ℕ) : Type :=
  UnfinalizedProof k Fq Bool (Type2 Fq) × AllEvals Fq ×
    Vector (Vector Fq k) MaxProofsVerified

/-- The wrap side's input at `k` rounds, as cells. -/
abbrev WrapFopVar (k : ℕ) : Type :=
  UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)) × AllEvals (FVar Fq) ×
    Vector (Vector (FVar Fq) k) MaxProofsVerified

/-- The wrap circuit's scalar half at an environment: `finalize_other_proof`'s wrap side with
the verifier key's parameters and domain — its generator a constant, `ζⁿ − 1` by `pow2PowMul`
at the key's `log2` — the `Fq` token stream, and the previous-challenge cells at their static
size. -/
def finalizeOtherProofWrapAt {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c] {k : ℕ}
    (E : Env IpaPallas.curve)
    (u : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq))) (w : AllEvals (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) k) MaxProofsVerified) :
    CircuitM Fq c (FopOutput Fq) :=
  finalizeOtherProofWrap (FopParams.ofEnv E Linearization.fqTokens) E.cvk.omega
    E.cvk.domainLog2
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

/-- **Running the wrap circuit's scalar half, a wrap proof's remaining half makes
`kimchiVerify` accept.** `twoHalves_kimchiVerify_pallas` as a triple about the scalar circuit,
with the step circuit's group half assumed (`verifyProof_step_reads` produces it). What the
circuit's parameters and domain owe is the environment's; what is left is the ties. -/
theorem finalizeOtherProofWrapAt_kimchiVerify_pallas
    (E : Env IpaPallas.curve)
    (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
    (pub : Array Fq)
    (hguard : Guards IpaPallas.curve E.cvk cp pub)
    -- the wrap circuit: its valuation and its cells
    (Vs : Valuation Fq)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : AllEvals (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) E.σ.k) MaxProofsVerified)
    -- the step circuit's group half, and its asserted bit
    (Vg : Valuation Fp)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (successG : BoolVar Fp)
    (hg : (GroupHalf.step Vg claimsG).Reads E cp pub successG)
    (hgbit : (↑successG : CVar Fp).val Vg = 1)
    -- across the two
    (ht : HalvesTies (GroupHalf.step Vg claimsG)
      (ScalarHalf.wrap Vs claimsS evals prevChallenges))
    (hf : FopTies E cp pub (ScalarHalf.wrap Vs claimsS evals prevChallenges))
    -- the `ζ` powers `ft_comm` scales by, which no circuit compares
    (hzetaM : (stepSide Vg).decode claimsG.deferredValues.plonk.zetaToSrsLength
      = runZetaM IpaPallas.curve E.σ E.cvk cp pub)
    (hzetaN : (stepSide Vg).decode claimsG.deferredValues.plonk.zetaToDomainSize
      = runZetaN IpaPallas.curve E.σ E.cvk cp pub) :
    ⦃⌜True⌝⦄
    finalizeOtherProofWrapAt (c := Builder Vs (KimchiConstraint Fq)) E claimsS evals
      prevChallenges
    ⦃⇓ o _ => ⌜SgOk E cp pub ∧ (↑o.finalized : CVar Fq).val Vs = 1
      → kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true ∧
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
    E.cvk.omega E.cvk.n E.zkRows_le E.omega_prim.pow_eq_one E.cvk.domainLog2 _ hvan claimsS evals
    (prevChallenges.toList.map Vector.toList) _ hprev
  simp only [finalizeOtherProofWrapAt]
  refine builder_spec_imp _ _ _ hspec ?_
  intro o hread
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
  rintro ⟨hsg, hfin⟩
  exact twoHalves_kimchiVerify_pallas E cp pub hguard Vg claimsG successG hg Vs claimsS evals
    prevChallenges o hread ht hf hzetaM hzetaN ⟨⟨hgbit, hfin⟩, hsg⟩

/-! ## The circuit of its input -/

namespace WrapProof

variable {k : ℕ}

/-- The scalar circuit's input: the slot's claims, the evaluations, the previous challenges.
Nothing in it is checked on input. -/
abbrev ScalarIn (k : ℕ) : Type := UnChecked (WrapFop k)
/-- `ScalarIn`, as cells. -/
abbrev ScalarVar (k : ℕ) : Type := UnChecked (WrapFopVar k)

/-- The slot's deferred claims. -/
def ScalarVar.claims (s : ScalarVar k) :
    UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)) := s.val.1
/-- The evaluation cells. -/
def ScalarVar.evals (s : ScalarVar k) : AllEvals (FVar Fq) := s.val.2.1
/-- The previous challenges, one vector per slot. -/
def ScalarVar.prev (s : ScalarVar k) : Vector (Vector (FVar Fq) k) MaxProofsVerified :=
  s.val.2.2
/-- The scalar circuit as a `ScalarHalf`. -/
abbrev ScalarVar.half (V : Valuation Fq) (s : ScalarVar k) :
    ScalarHalf IpaPallas.curve (Type2 (FVar Fq)) k :=
  ScalarHalf.wrap V s.claims s.evals s.prev

/-- The wrap circuit's scalar half as a circuit of its input, `finalized` asserted: the
deployed `finalized ∨ ¬should_finalize` at a slot that is finalized. -/
def scalarCircuit {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c]
    (E : Env IpaPallas.curve) (s : ScalarVar E.σ.k) : CircuitM Fq c Unit := do
  let o ← finalizeOtherProofWrapAt E s.claims s.evals s.prev
  assert o.finalized

/-- **The scalar circuit's read.** With the step circuit's group half and the ties, a valuation
satisfying the body makes `kimchiVerify` accept once `SgOk` holds. -/
theorem scalarCircuit_reads (E : Env IpaPallas.curve)
    (cp : KimchiProof IpaPallas.curve 1 E.σ.k) (pub : Array Fq)
    (hguard : Guards IpaPallas.curve E.cvk cp pub)
    (Vs : Valuation Fq) (s : ScalarVar E.σ.k)
    (Vg : Valuation Fp)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (successG : BoolVar Fp)
    (hg : (GroupHalf.step Vg claimsG).Reads E cp pub successG)
    (hgbit : (↑successG : CVar Fp).val Vg = 1)
    (ht : HalvesTies (GroupHalf.step Vg claimsG) (s.half Vs))
    (hf : FopTies E cp pub (s.half Vs))
    (hzetaM : (stepSide Vg).decode claimsG.deferredValues.plonk.zetaToSrsLength
      = runZetaM IpaPallas.curve E.σ E.cvk cp pub)
    (hzetaN : (stepSide Vg).decode claimsG.deferredValues.plonk.zetaToDomainSize
      = runZetaN IpaPallas.curve E.σ E.cvk cp pub)
    (hsg : SgOk E cp pub) :
    ⦃⌜True⌝⦄
    scalarCircuit (c := Builder Vs (KimchiConstraint Fq)) E s
    ⦃⇓ _ _ => ⌜kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true⌝⦄ := by
  have hAt := finalizeOtherProofWrapAt_kimchiVerify_pallas E cp pub hguard Vs s.claims s.evals
    s.prev Vg claimsG successG hg hgbit ht hf hzetaM hzetaN
  clear hzetaM hzetaN
  simp only [scalarCircuit]
  mvcgen [hAt]
  rename_i himp
  intro hfin
  exact (himp hsg hfin).1

end WrapProof

end Pickles

