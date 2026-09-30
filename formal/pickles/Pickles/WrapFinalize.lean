import Pickles.FinalizeOtherProof
import Pickles.Domain
import Pickles.WrapScalarHalf

set_option mvcgen.warning false

/-!
# The wrap circuit's finalize block

Transcribes the finalize block of `wrap_main.ml`. Each previous proof's slot carries a wrap
domain index as advice. The block pins each index to the domain the active branch was compiled
for, selects each slot's domain from its index, then finalizes each slot's deferred values
against that domain and asserts the slot finalized or was not to be.

## Main definitions

* `pinWrapDomainIndex`: one slot's pin against the branches' compile-time indices.
* `WrapFinalizeSlot`: one slot's cells and compile-time pins.
* `wrapDomainLog2s`: the wrap domains a slot can be finalized at.
* `wrapFinalizePrevProofs`: the pins, left to right; the domains, right to left; the finalize
  bodies with their assertions, left to right.

## Implementation notes

A slot whose predecessor is side-loaded in some branch has no compile-time domain there. That
branch's term is zero on both sides of the pin, so while it is active the index is
unconstrained.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Pickles.Linearization

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]

/-- One slot's pin. `atSlot` holds each branch's compile-time domain index for the slot, `none`
for a side-loaded predecessor. When every branch knows it, the index equals the one-hot choice;
otherwise the known branches' bits scale the index to that choice. -/
def pinWrapDomainIndex [ConstraintHolds F c] {n : ℕ} (whichBranch : Vector (BoolVar F) n)
    (atSlot : Vector (Option ℕ) n) (index : FVar F) : CircuitM F c PUnit := do
  let chosen ← Pseudo.choose whichBranch.toList atSlot.toList
    fun k => .const (k.elim 0 fun j => (j : F))
  if atSlot.all Option.isSome then
    assertEqual index chosen
  else
    let knownBranch ← Pseudo.choose whichBranch.toList atSlot.toList
      fun k => .const (k.elim 0 fun _ => 1)
    let pinned ← mul knownBranch index
    assertEqual pinned chosen

/-- One slot of the finalize block: its wrap domain index cell, its column of compile-time
domain indices over the branches (`none` for a side-loaded predecessor), and the finalized
proof's unfinalized claims, evaluations and padded previous challenges. -/
structure WrapFinalizeSlot (branches k nc : ℕ) (F : Type) where
  /-- The wrap domain index cell. -/
  domainIndex : FVar F
  /-- Each branch's compile-time domain index for this slot. -/
  pins : Vector (Option ℕ) branches
  /-- The finalized proof's unfinalized claims. -/
  unfinalized : UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (FVar F))
  /-- Its evaluations. -/
  evals : ChunkedEvals nc (FVar F)
  /-- Its padded previous challenges. -/
  prevChallenges : Vector (Vector (FVar F) k) MaxProofsVerified

/-- The wrap domains a slot's index selects among, by `log2`: those of the wrap circuits
verifying 0, 1 and 2 previous proofs. -/
def wrapDomainLog2s : List ℕ := [13, 14, 15]

/-! ## The read -/

section Reads

variable [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}

omit [ToNat F] [KimchiSystem F c] in
/-- Under any valuation satisfying the emitted constraints, with the branch bits reading as the
indicator of `b` and branch `b` compiled for index `j` at this slot, the index reads as `j`. -/
theorem pinWrapDomainIndex_spec {n : ℕ} (whichBranch : Vector (BoolVar F) n)
    (atSlot : Vector (Option ℕ) n) (index : FVar F) (b : Fin n) (j : ℕ)
    (hbits : CircuitType.Reads V whichBranch (Vector.ofFn fun l => decide (l = b)))
    (hj : atSlot[b] = some j) :
    ⦃⌜True⌝⦄ pinWrapDomainIndex (c := Builder V c) whichBranch atSlot index
    ⦃⇓ _ _ => ⌜index.val V = (j : F)⌝⦄ := by
  have hj' : atSlot[(b : ℕ)] = some j := by rwa [Fin.getElem_fin] at hj
  have hind := fun (f : Option ℕ → F) => sum_oneHot f whichBranch atSlot.toList (by simp) b hbits
  have hsel := hind fun k => (CVar.const (k.elim 0 fun i => (i : F)) : CVar F).val V
  have hone := hind fun k => (CVar.const (k.elim 0 fun _ => (1 : F)) : CVar F).val V
  rw [Vector.getElem_toList, hj'] at hsel hone
  have hc := Pseudo.choose_spec (c := c) (V := V) whichBranch.toList atSlot.toList
    fun k => .const (k.elim 0 fun i => (i : F))
  have hk := Pseudo.choose_spec (c := c) (V := V) whichBranch.toList atSlot.toList
    fun k => .const (k.elim 0 fun _ => (1 : F))
  simp only [pinWrapDomainIndex]
  mvcgen [hc, hk]
  · rename_i chosen _ _ hchosen _ _
    intro hidx
    rw [hidx, hchosen, hsel]
    rfl
  · rename_i chosen _ _ hchosen known _ hknown pinned _ hpinned _ _
    intro hassert
    rw [hpinned, hchosen, hknown, hsel, hone] at hassert
    simpa using hassert

end Reads

/-! ## At a wrap proof -/

section Capstone

open Bulletproof Bulletproof.Ipa Kimchi.Protocol.Linearization Poseidon.FqSponge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The wrap circuit's finalize block over its slots: the pins, left to right; the domains, right
to left, among `wrapDomainLog2s` with the scalar field's generators (`domainGenerator`); the
finalize bodies with their assertions, left to right. Returns each slot's finalize output. -/
def wrapFinalizePrevProofs {c : Type} [BasicSystem Fq c] [ConstraintHolds Fq c] [KimchiSystem Fq c]
    {branches mpv k nc : ℕ} (P : FopParams Fq) (whichBranch : Vector (BoolVar Fq) branches)
    (slots : Vector (WrapFinalizeSlot branches k nc Fq) mpv) :
    CircuitM Fq c (Vector (FopOutput Fq k) mpv) := do
  slots.toList.forM fun sl => pinWrapDomainIndex whichBranch sl.pins sl.domainIndex
  let rev ← (slots.map (·.domainIndex)).reverse.mapM
    (selectDomain (domainGenerator IpaPallas.curve) wrapDomainLog2s)
  (rev.reverse.zip slots).mapM fun (d, sl) => do
    let o ← finalizeOtherProofWrap P d.generator d.vanishingPolynomial sl.unfinalized sl.evals
      sl.prevChallenges
    assertAny [o.finalized, Snarky.not sl.unfinalized.shouldFinalize]
    pure o

variable {nc : ℕ}

/-- A finalize slot reads as a wrap proof's scalar half, `expanded` being its finalize's
expanded challenges: for any wrap proof and public input, with a step circuit's group half
accepting it at asserted success and the ties, `expanded` reads as the proof's wire challenges,
and under the guards the deferred `sg` equation makes `kimchiVerify` accept. -/
def WrapFinalizeSlot.ScalarReads (σ : SRS IpaPallas.curve.Point)
    (cvk : KimchiVK IpaPallas.curve nc) (Vs : Valuation Fq)
    {branches : ℕ} (sl : WrapFinalizeSlot branches σ.k nc Fq)
    (expanded : Vector (FVar Fq) σ.k) : Prop :=
  ∀ (cp : KimchiProof IpaPallas.curve nc σ.k) (pub : Array Fq) (Vg : Valuation Fp)
    (claimsG : UnfinalizedProof σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) (successG : BoolVar Fp),
    (GroupHalf.step Vg claimsG).Reads σ cvk cp pub successG → (↑successG : CVar Fp).val Vg = 1 →
    SplitClaimsCast Vg claimsG Vs sl.unfinalized →
    FopTies σ cvk cp pub (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
    expanded.map (·.val Vs) = wireChallenges σ cvk cp pub ∧
      (Guards IpaPallas.curve cvk cp pub →
        SgOk σ cvk cp pub → kimchiVerify IpaPallas.curve σ cvk cp pub = true)

/-- One slot's finalize body: under any valuation satisfying the emitted constraints, with the
slot's domain reading as the key's (its generator `ω`, its vanishing polynomial `ζⁿ − 1`) and
`shouldFinalize` set, the slot reads as its scalar half at the body's expanded challenges. -/
theorem wrapFinalizeBody_spec (σ : SRS IpaPallas.curve.Point) (K : Key IpaPallas.curve nc)
    (Vs : Valuation Fq)
    (d : PlonkDomain Fq (Builder Vs (KimchiConstraint Fq))) {branches : ℕ}
    (sl : WrapFinalizeSlot branches σ.k nc Fq) :
    ⦃⌜True⌝⦄
    (do
      let o ← finalizeOtherProofWrap (c := Builder Vs (KimchiConstraint Fq))
        (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens) d.generator
          d.vanishingPolynomial
        sl.unfinalized sl.evals sl.prevChallenges
      assertAny [o.finalized, Snarky.not sl.unfinalized.shouldFinalize]
      pure o)
    ⦃⇓ o _ => ⌜d.generator.val Vs = K.cvk.omega →
      (∀ z, ⦃⌜True⌝⦄ d.vanishingPolynomial z ⦃⇓ v _ => ⌜v.val Vs = z.val Vs ^ K.cvk.n - 1⌝⦄) →
      (↑sl.unfinalized.shouldFinalize : CVar Fq).val Vs = 1 →
      sl.ScalarReads σ K.cvk Vs o.expandedChallenges⌝⦄ := by
  by_cases h : d.generator.val Vs = K.cvk.omega ∧
      ∀ z, ⦃⌜True⌝⦄ d.vanishingPolynomial z ⦃⇓ v _ => ⌜v.val Vs = z.val Vs ^ K.cvk.n - 1⌝⦄
  · obtain ⟨hgen, hvan⟩ := h
    have hsr : ⦃⌜True⌝⦄
        finalizeOtherProofWrap (c := Builder Vs (KimchiConstraint Fq))
          (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens) d.generator
            d.vanishingPolynomial
          sl.unfinalized sl.evals sl.prevChallenges
        ⦃⇓ o _ => ⌜(↑o.finalized : CVar Fq).val Vs = 1 →
          sl.ScalarReads σ K.cvk Vs o.expandedChallenges⌝⦄ := by
      have hP :
          (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens).endo = Pasta.vestaEndo ∧
          (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens).mds = Reflect.symMdsQ ∧
          (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens).toks =
            Linearization.fqTokens :=
        ⟨rfl, by rfl, rfl⟩
      have hprev : CircuitType.Reads Vs sl.prevChallenges
          (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges).prevVals :=
        CircuitType.reads_vector.mpr fun i hi => CircuitType.reads_vector.mpr fun j hj =>
          CircuitType.reads_fvar.mpr (by simp [ScalarHalf.prevVals, ScalarHalf.wrap])
      have hspec := finalizeOtherProofWrap_spec_fq (V := Vs)
        (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens) hP
          IpaPallas.curve.frSponge.hsize
        (three_le_zkRowsOf K.cvk.nc_pos)
        d.generator K.cvk.n (show zkRowsOf nc ≤ K.cvk.n from K.zkRows_eq ▸ K.zkRows_le)
          (by rw [hgen]; exact K.omega_prim.pow_eq_one) _ hvan
        sl.unfinalized sl.evals sl.prevChallenges _ hprev
      refine builder_spec_imp _ _ _ hspec ?_
      intro o hread hfin cp pub Vg claimsG successG hg hgbit hc hf
      rw [hgen] at hread
      -- the two halves hold one set of claims: `β`, `γ` read on the step side, the rest here
      have ht : HalvesTies (GroupHalf.step Vg claimsG)
          (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) := by
        obtain ⟨og, hivp, -⟩ := hg
        obtain ⟨a₀, z₀, hα, hζ, ξ₀, _r, ĉ, hξ, -, -, -, -, hĉ, -⟩ := hread
        exact halvesTies_of_splitCast Vg claimsG Vs sl.unfinalized sl.evals sl.prevChallenges
          hc ⟨_, hivp.2.1⟩ ⟨_, hivp.2.2.1⟩ ⟨a₀, hα⟩ ⟨z₀, hζ⟩ ⟨ξ₀, hξ⟩ ⟨ĉ, hĉ⟩
      have holds : (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges).prevVals.toList
          = (cp.olds.map (·.u)).toList :=
        (ScalarHalf.wrap_olds Vs sl.unfinalized sl.evals sl.prevChallenges _).mp hf.olds
      have hdv :
          (Poseidon.squeeze (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens).sponge
            (Poseidon.absorb (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens).sponge
              Poseidon.init (sl.prevChallenges.flatten.toList.map (·.val Vs)))).1
          = recDigest IpaPallas.curve (cp.olds.map (·.u)) := by
        have habs : sl.prevChallenges.flatten.toList.map (·.val Vs)
            = ((cp.olds.map (·.u)).toList.map Vector.toList).flatten := by
          have h1 : sl.prevChallenges.flatten.toList.map (·.val Vs)
              = ((ScalarHalf.wrap Vs sl.unfinalized sl.evals
                  sl.prevChallenges).prevVals.toList.map Vector.toList).flatten := by
            simp [toList_flatten', ScalarHalf.prevVals, ScalarHalf.wrap, List.map_flatten,
              List.map_map, Function.comp_def, Vector.toList_map]
          rw [h1, holds]
        rw [habs]
        rfl
      have hmask : (sl.prevChallenges.map fun _ => true)
          = (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges).maskVals := by
        rw [ScalarHalf.wrap_maskVals]
        exact Vector.ext fun i hi => by simp
      rw [hdv, hmask] at hread
      refine ⟨(twoHalves_schnorr σ K (by norm_num [PALLAS_BASE_CARD])
        (by norm_num [PALLAS_SCALAR_CARD]) cp pub _ successG hg _ o hread ht hf).2 ⟨hgbit, hfin⟩,
        fun hguard hsg => ?_⟩
      exact ((twoHalves_kimchiVerify σ K (by norm_num [PALLAS_BASE_CARD])
        (by norm_num [PALLAS_SCALAR_CARD]) cp pub hguard _ successG hg _ o hread ht hf).mp
        ⟨⟨hgbit, hfin⟩, hsg⟩).1
    have hf := builder_spec_and _ _ _ hsr
      (finalizeOtherProofWrap_finalized_bit (V := Vs)
        (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens)
        d.generator d.vanishingPolynomial sl.unfinalized sl.evals
        sl.prevChallenges)
    mvcgen [hf]
    rename_i o _ ho _ _ hany
    intro _ _ hsf
    obtain ⟨hread, bb, hbb⟩ := ho
    have hnot := not_val (b := sl.unfinalized.shouldFinalize) (bb := true)
      (by simpa [bit] using hsf)
    obtain ⟨x, hx, hx1⟩ := hany fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [hbb]; cases bb <;> simp [bit]
      · rw [hnot]; simp [bit]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hread hx1
    · rw [hnot] at hx1; simp [bit] at hx1
  · refine builder_spec_imp _ _ _ (builder_spec_true _) ?_
    intro _ _ hg hv
    exact absurd ⟨hg, hv⟩ h

/-- **The wrap circuit's finalize block reads as each finalized proof's scalar half.** Under any
valuation satisfying the emitted constraints, with the branch bits reading as the indicator of
`b`, every slot that branch `b` compiled for the key's domain (index `j` of `wrapDomainLog2s`,
generator `ω`, size `n`) and whose `shouldFinalize` is set reads as its scalar half at its
output's expanded challenges. -/
theorem wrapFinalizePrevProofs_reads
    {branches mpv : ℕ}
    (σ : SRS IpaPallas.curve.Point) (K : Key IpaPallas.curve nc)
    (Vs : Valuation Fq)
    (whichBranch : Vector (BoolVar Fq) branches)
    (slots : Vector (WrapFinalizeSlot branches σ.k nc Fq) mpv)
    (b : Fin branches) (j : ℕ)
    (hbits : CircuitType.Reads Vs whichBranch (Vector.ofFn fun l => decide (l = b)))
    (hdom : wrapDomainLog2s[j]? = some K.cvk.domainLog2) :
    ⦃⌜True⌝⦄
    wrapFinalizePrevProofs (c := Builder Vs (KimchiConstraint Fq))
      (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens) whichBranch slots
    ⦃⇓ outs _ => ⌜∀ i : Fin mpv, slots[i].pins[b] = some j →
      (↑slots[i].unfinalized.shouldFinalize : CVar Fq).val Vs = 1 →
      slots[i].ScalarReads σ K.cvk Vs outs[i].expandedChallenges⌝⦄ := by
  -- the key's domain is candidate `j` of the table
  obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hdom
  have hn : 2 ^ wrapDomainLog2s[j] = K.cvk.n := by rw [hjv]; rfl
  have hgen' : domainGenerator IpaPallas.curve wrapDomainLog2s[j] = K.cvk.omega := by
    rw [hjv]; exact K.omega_eq.symm
  have hinj : ∀ l < wrapDomainLog2s.length, (j : Fq) = l → j = l := by
    intro l hl h
    have hj3 : j < 3 := hj
    have hl3 : l < 3 := hl
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (by norm_num [PALLAS_SCALAR_CARD]; omega),
      ZMod.val_natCast_of_lt (by norm_num [PALLAS_SCALAR_CARD]; omega)] at this
  simp only [wrapFinalizePrevProofs]
  -- each slot's pin: on a slot branch `b` compiled for `j`, the index reads as `j`
  have hpin := forM_spec (V := Vs) (c := KimchiConstraint Fq)
    (fun sl : WrapFinalizeSlot branches σ.k nc Fq =>
      pinWrapDomainIndex whichBranch sl.pins sl.domainIndex)
    (fun sl => sl.pins[b] = some j → sl.domainIndex.val Vs = (j : Fq))
    (fun sl => by
      by_cases h : sl.pins[b] = some j
      · refine builder_spec_imp _ _ _ (pinWrapDomainIndex_spec whichBranch sl.pins
          sl.domainIndex b j hbits h) ?_
        intro _ hr _
        exact hr
      · refine builder_spec_imp _ _ _ (builder_spec_true _) ?_
        intro _ _ h'
        exact absurd h' h)
  -- each slot's domain: an index reading as `j` selects the key's domain
  have hdom := builder_spec_vector_mapM_get (V := Vs) (c := KimchiConstraint Fq)
    (selectDomain (domainGenerator IpaPallas.curve) wrapDomainLog2s)
    (fun (index : FVar Fq) (d : PlonkDomain Fq (Builder Vs (KimchiConstraint Fq))) =>
      index.val Vs = (j : Fq) →
        d.generator.val Vs = domainGenerator IpaPallas.curve wrapDomainLog2s[j] ∧
          ∀ zeta : FVar Fq, ⦃⌜True⌝⦄ d.vanishingPolynomial zeta
            ⦃⇓ r _ => ⌜r.val Vs = zeta.val Vs ^ 2 ^ wrapDomainLog2s[j] - 1⌝⦄)
    (fun index => by
      by_cases h : index.val Vs = (j : Fq)
      · refine builder_spec_imp _ _ _
          (selectDomain_spec (domainGenerator IpaPallas.curve) wrapDomainLog2s index j hj h hinj) ?_
        intro _ hr _
        exact hr
      · refine builder_spec_imp _ _ _ (builder_spec_true _) ?_
        intro _ _ h'
        exact absurd h' h) ((slots.map (·.domainIndex)).reverse)
  -- each slot's body
  have hbody := builder_spec_vector_mapM_get (V := Vs) (c := KimchiConstraint Fq) (m := mpv)
    (fun (p : PlonkDomain Fq (Builder Vs (KimchiConstraint Fq)) ×
        WrapFinalizeSlot branches σ.k nc Fq) =>
      do
        let o ← finalizeOtherProofWrap (c := Builder Vs (KimchiConstraint Fq))
          (FopParams.of IpaPallas.curve nc σ.k Linearization.fqTokens) p.1.generator
          p.1.vanishingPolynomial p.2.unfinalized p.2.evals
          p.2.prevChallenges
        assertAny [o.finalized, Snarky.not p.2.unfinalized.shouldFinalize]
        pure o)
    (fun p o => p.1.generator.val Vs = K.cvk.omega →
      (∀ z, ⦃⌜True⌝⦄ p.1.vanishingPolynomial z ⦃⇓ v _ => ⌜v.val Vs = z.val Vs ^ K.cvk.n - 1⌝⦄) →
      (↑p.2.unfinalized.shouldFinalize : CVar Fq).val Vs = 1 →
      p.2.ScalarReads σ K.cvk Vs o.expandedChallenges)
    (fun p => wrapFinalizeBody_spec σ K Vs p.1 p.2)
  mvcgen [hpin, hdom, hbody]
  rename_i hpinP rev _ hrev _ _
  intro hos i hpb hsf
  have hsl : slots[i] ∈ slots.toList := by simp
  have hidx := hpinP _ hsl (by simpa using hpb)
  -- slot `i`'s domain is the `(mpv − 1 − i)`-th of the right-to-left run
  have hd := hrev ⟨mpv - 1 - i, by omega⟩
  simp only [Fin.getElem_fin, Vector.getElem_reverse, Vector.getElem_map] at hd
  simp only [show mpv - 1 - (mpv - 1 - i) = i.val by omega] at hd
  obtain ⟨hg, hv⟩ := hd hidx
  have hR := hos i
  simp only [Fin.getElem_fin, Vector.getElem_zip, Vector.getElem_reverse] at hR
  exact hR (hg.trans hgen') (fun z => builder_spec_imp _ _ _ (hv z) fun r hr => by rw [hr, hn])
    hsf

end Capstone

end Pickles
