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
* `wrapFinalizeCircuit`: the block as a circuit of its input (`WrapFinalizeIn`).
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
def pinWrapDomainIndex (whichBranch : List (BoolVar F)) (atSlot : List (Option ℕ))
    (index : FVar F) : CircuitM F c PUnit :=
  match atSlot.allSome with
  | some ks => do
    let chosen ← Pseudo.choose whichBranch ks fun j => .const (j : F)
    assertEqual index chosen
  | none => do
    let chosen ← Pseudo.choose whichBranch atSlot fun k => .const (k.elim 0 fun j => (j : F))
    let knownBranch ← Pseudo.choose whichBranch atSlot fun k => .const (k.elim 0 fun _ => 1)
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

/-- The wrap circuit's finalize block over its slots: the pins, left to right; the domains, right
to left, among `wrapDomainLog2s` with generators `gen`; the finalize bodies with their
assertions, left to right. Returns each slot's finalize output. -/
def wrapFinalizePrevProofs {branches mpv k nc : ℕ} (P : FopParams F) (gen : ℕ → F)
    (whichBranch : Vector (BoolVar F) branches)
    (slots : Vector (WrapFinalizeSlot branches k nc F) mpv) :
    CircuitM F c (List (FopOutput F)) := do
  slots.toList.forM fun sl =>
    pinWrapDomainIndex whichBranch.toList sl.pins.toList sl.domainIndex
  let rev ← (slots.toList.map (·.domainIndex)).reverse.mapM (selectDomain gen wrapDomainLog2s)
  (rev.reverse.zip slots.toList).mapM fun (d, sl) => do
    let o ← finalizeOtherProofWrap P d.generator d.vanishingPolynomial sl.unfinalized sl.evals
      (sl.prevChallenges.toList.map Vector.toList)
    assertAny [o.finalized, Snarky.not sl.unfinalized.shouldFinalize]
    pure o

/-! ## The read -/

section Reads

variable [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}

/-- A list whose entries are all `some` is the `some`s of `List.allSome`'s result. -/
private theorem allSome_eq_some {α : Type} :
    ∀ {l : List (Option α)} {ks : List α}, l.allSome = some ks → l = ks.map some
  | [], ks, h => by
    simp only [List.allSome, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | a :: l, ks, h => by
    cases a with
    | none => simp [List.allSome] at h
    | some x =>
      cases hl : l.allSome with
      | none =>
        simp only [List.allSome] at hl
        simp [List.allSome, hl] at h
      | some ks' =>
        simp only [List.allSome] at hl
        simp only [List.allSome, List.mapM_cons, hl] at h
        simp only [id_eq, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp [allSome_eq_some (l := l) (by simpa [List.allSome] using hl)]

omit [ToNat F] [KimchiSystem F c] in
/-- Under any valuation satisfying the emitted constraints, with the branch bits reading as the
indicator of `b` and branch `b` compiled for index `j` at this slot, the index reads as `j`. -/
theorem pinWrapDomainIndex_spec (whichBranch : List (BoolVar F)) (atSlot : List (Option ℕ))
    (index : FVar F) (b j : ℕ)
    (hbits : whichBranch.map (fun x : BoolVar F => (↑x : CVar F).val V)
      = (List.range atSlot.length).map fun l => if l = b then (1 : F) else 0)
    (hj : atSlot[b]? = some (some j)) :
    ⦃⌜True⌝⦄ pinWrapDomainIndex (c := Builder V c) whichBranch atSlot index
    ⦃⇓ _ _ => ⌜index.val V = (j : F)⌝⦄ := by
  obtain ⟨hb, hbj⟩ := List.getElem?_eq_some_iff.mp hj
  simp only [pinWrapDomainIndex]
  split
  · rename_i ks hks
    have hks' := allSome_eq_some hks
    subst hks'
    have hc := Pseudo.choose_spec (c := c) (V := V) whichBranch ks fun i => .const (i : F)
    mvcgen [hc]
    rename_i chosen _ hchosen _ _
    intro hidx
    rw [hidx, hchosen]
    rw [sum_zip_bits whichBranch ks fun i => (CVar.const (i : F) : CVar F).val V,
      sum_indicator (fun i : ℕ => (CVar.const (i : F) : CVar F).val V) ks _ b
        (by simpa using hbits) (by simpa using hb)]
    simp only [List.getElem_map, Option.some.injEq] at hbj
    rw [hbj]
    rfl
  · rename_i hnone
    have hc := Pseudo.choose_spec (c := c) (V := V) whichBranch atSlot
      fun k => .const (k.elim 0 fun i => (i : F))
    have hk := Pseudo.choose_spec (c := c) (V := V) whichBranch atSlot
      fun k => .const (k.elim 0 fun _ => (1 : F))
    mvcgen [hc, hk]
    rename_i chosen _ hchosen known _ hknown pinned _ hpinned _ _
    intro hassert
    have hind := fun (f : Option ℕ → F) =>
      (sum_zip_bits whichBranch atSlot f).trans (sum_indicator f atSlot _ b hbits hb)
    rw [hpinned, hchosen, hknown, hind (fun k => (CVar.const (k.elim 0 fun i => (i : F)) :
      CVar F).val V), hind (fun k => (CVar.const (k.elim 0 fun _ => (1 : F)) : CVar F).val V),
      hbj] at hassert
    simpa using hassert

end Reads

/-! ## At a wrap proof -/

section Capstone

open Bulletproof Bulletproof.Ipa Kimchi.Protocol.Linearization Poseidon.FqSponge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

variable {nc : ℕ}

/-- The finalize block's input, as values: the branch bits and, per slot, its wrap domain index
and its finalize input. Nothing in it is checked on input. -/
abbrev WrapFinalizeIn (branches w k nc : ℕ) : Type :=
  UnChecked (Vector Bool branches × Vector (Fq × WrapFop k nc) w)

/-- `WrapFinalizeIn`, as cells. -/
abbrev WrapFinalizeInVar (branches w k nc : ℕ) : Type :=
  UnChecked (Vector (BoolVar Fq) branches × Vector (FVar Fq × WrapFopVar k nc) w)

/-- The input's slots, each with its column of compile-time pins. -/
def WrapFinalizeInVar.slots {branches w k : ℕ} (x : WrapFinalizeInVar branches w k nc)
    (pins : Vector (Vector (Option ℕ) branches) w) : Vector (WrapFinalizeSlot branches k nc Fq) w :=
  Vector.zipWith (fun s p => ⟨s.1, p, s.2.claims, s.2.evals, s.2.prev⟩) x.val.2 pins

/-- The finalize block as a circuit of its input, at compile-time pins `pins`. -/
def wrapFinalizeCircuit {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c] {branches w k : ℕ}
    (P : FopParams Fq) (gen : ℕ → Fq) (pins : Vector (Vector (Option ℕ) branches) w)
    (x : WrapFinalizeInVar branches w k nc) : CircuitM Fq c Unit := do
  let _ ← wrapFinalizePrevProofs P gen x.val.1 (x.slots pins)

/-- A finalize slot reads as a wrap proof's scalar half: for any wrap proof and public input
under the guards, a step circuit's group half accepting it at asserted success, the ties and
the deferred `sg` equation make `kimchiVerify` accept. -/
def WrapFinalizeSlot.ScalarReads (E : Env IpaPallas.curve nc) (Vs : Valuation Fq)
    {branches : ℕ} (sl : WrapFinalizeSlot branches E.σ.k nc Fq) : Prop :=
  ∀ (cp : KimchiProof IpaPallas.curve nc E.σ.k) (pub : Array Fq),
    Guards IpaPallas.curve E.cvk cp pub →
    ∀ (Vg : Valuation Fp)
      (claimsG : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
        (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) (successG : BoolVar Fp),
      (GroupHalf.step Vg claimsG).Reads E cp pub successG → (↑successG : CVar Fp).val Vg = 1 →
      SplitClaimsCast Vg claimsG Vs sl.unfinalized →
      FopTies E cp pub (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
      SgOk E.σ E.cvk cp pub → kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true

/-- One slot's finalize body: under any valuation satisfying the emitted constraints, with the
slot's domain reading as the key's (its generator `ω`, its vanishing polynomial `ζⁿ − 1`) and
`shouldFinalize` set, the slot reads as its scalar half. -/
theorem wrapFinalizeBody_spec (E : Env IpaPallas.curve nc) (Vs : Valuation Fq)
    (d : PlonkDomain Fq (Builder Vs (KimchiConstraint Fq))) {branches : ℕ}
    (sl : WrapFinalizeSlot branches E.σ.k nc Fq) :
    ⦃⌜True⌝⦄
    (do
      let o ← finalizeOtherProofWrap (c := Builder Vs (KimchiConstraint Fq))
        (FopParams.ofEnv E Linearization.fqTokens) d.generator d.vanishingPolynomial
        sl.unfinalized sl.evals (sl.prevChallenges.toList.map Vector.toList)
      assertAny [o.finalized, Snarky.not sl.unfinalized.shouldFinalize]
      pure o)
    ⦃⇓ _ _ => ⌜d.generator.val Vs = E.cvk.omega →
      (∀ z, ⦃⌜True⌝⦄ d.vanishingPolynomial z ⦃⇓ v _ => ⌜v.val Vs = z.val Vs ^ E.cvk.n - 1⌝⦄) →
      (↑sl.unfinalized.shouldFinalize : CVar Fq).val Vs = 1 → sl.ScalarReads E Vs⌝⦄ := by
  by_cases h : d.generator.val Vs = E.cvk.omega ∧
      ∀ z, ⦃⌜True⌝⦄ d.vanishingPolynomial z ⦃⇓ v _ => ⌜v.val Vs = z.val Vs ^ E.cvk.n - 1⌝⦄
  · obtain ⟨hgen, hvan⟩ := h
    have hsr : ⦃⌜True⌝⦄
        finalizeOtherProofWrap (c := Builder Vs (KimchiConstraint Fq))
          (FopParams.ofEnv E Linearization.fqTokens) d.generator d.vanishingPolynomial
          sl.unfinalized sl.evals (sl.prevChallenges.toList.map Vector.toList)
        ⦃⇓ o _ => ⌜(↑o.finalized : CVar Fq).val Vs = 1 → sl.ScalarReads E Vs⌝⦄ := by
      have hP : (FopParams.ofEnv E Linearization.fqTokens).endo = Pasta.vestaEndo ∧
          (FopParams.ofEnv E Linearization.fqTokens).mds = Reflect.symMdsQ ∧
          (FopParams.ofEnv E Linearization.fqTokens).toks = Linearization.fqTokens :=
        ⟨E.endo_eq, by rfl, rfl⟩
      have hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads Vs))
          (sl.prevChallenges.toList.map Vector.toList)
          (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges).prevVals := by
        refine List.forall₂_map_right_iff.2 (List.forall₂_map_left_iff.2
          (List.forall₂_same.2 fun cs _ => ?_))
        exact List.forall₂_map_right_iff.2
          (List.forall₂_same.2 fun x _ => CircuitType.reads_fvar.2 rfl)
      have hspec := finalizeOtherProofWrap_spec_fq (V := Vs)
        (FopParams.ofEnv E Linearization.fqTokens) hP IpaPallas.curve.frSponge.hsize E.zkRows_ge
        d.generator E.cvk.n E.zkRows_le (by rw [hgen]; exact E.omega_prim.pow_eq_one) _ hvan
        sl.unfinalized sl.evals (sl.prevChallenges.toList.map Vector.toList) _ hprev
      refine builder_spec_imp _ _ _ hspec ?_
      intro o hread hfin cp pub hguard Vg claimsG successG hg hgbit hc hf hsg
      rw [hgen] at hread
      -- the two halves hold one set of claims: `β`, `γ` read on the step side, the rest here
      have ht : HalvesTies (GroupHalf.step Vg claimsG)
          (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) := by
        obtain ⟨og, hivp, -⟩ := hg
        obtain ⟨a₀, z₀, hα, hζ, ξ₀, -, ĉ, hξ, -, -, -, -, hĉ, -⟩ := hread
        exact halvesTies_of_splitCast Vg claimsG Vs sl.unfinalized sl.evals sl.prevChallenges
          hc ⟨_, hivp.2.1⟩ ⟨_, hivp.2.2.1⟩ ⟨a₀, hα⟩ ⟨z₀, hζ⟩ ⟨ξ₀, hξ⟩ ⟨ĉ, hĉ⟩
      have holds : (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges).prevVals
          = (cp.olds.map (·.u.toList)).toList :=
        (ScalarHalf.wrap_olds Vs sl.unfinalized sl.evals sl.prevChallenges _).mp hf.olds
      have hdv : (Poseidon.squeeze (FopParams.ofEnv E Linearization.fqTokens).sponge
            (Poseidon.absorb (FopParams.ofEnv E Linearization.fqTokens).sponge Poseidon.init
              ((sl.prevChallenges.toList.map Vector.toList).flatten.map (·.val Vs)))).1
          = recDigest IpaPallas.curve (cp.olds.map (·.u)) := by
        have habs : (sl.prevChallenges.toList.map Vector.toList).flatten.map (·.val Vs)
            = ((cp.olds.map (·.u)).toList.map Vector.toList).flatten := by
          have h1 : (sl.prevChallenges.toList.map Vector.toList).flatten.map (·.val Vs)
              = ((ScalarHalf.wrap Vs sl.unfinalized sl.evals
                  sl.prevChallenges).prevVals).flatten := by
            simp [ScalarHalf.prevVals, ScalarHalf.wrap, List.map_flatten, List.map_map,
              Function.comp_def]
          rw [h1, holds]
          simp [Function.comp_def]
        rw [habs]
        rfl
      have hmask : (List.map (fun _ => true) (sl.prevChallenges.toList.map Vector.toList))
          = (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges).maskVals := by
        rw [ScalarHalf.wrap_maskVals]
        simp
      rw [hdv, hmask] at hread
      exact ((twoHalves_kimchiVerify E (by norm_num [PALLAS_BASE_CARD])
        (by norm_num [PALLAS_SCALAR_CARD]) cp pub hguard _ successG hg _ o hread ht hf).mp
        ⟨⟨hgbit, hfin⟩, hsg⟩).1
    have hf := builder_spec_and _ _ _ hsr
      (finalizeOtherProofWrap_finalized_bit (V := Vs) (FopParams.ofEnv E Linearization.fqTokens)
        d.generator d.vanishingPolynomial sl.unfinalized sl.evals
        (sl.prevChallenges.toList.map Vector.toList))
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

/-- A list related entrywise to a mapped list pairs each entry of the original with one of its
own entries, related to the entry's image. -/
private theorem forall₂_map_zip {α β δ : Type} {R : δ → β → Prop} {f : α → β} :
    ∀ {ds : List δ} {l : List α}, List.Forall₂ R ds (l.map f) →
      ∀ a ∈ l, ∃ d, (d, a) ∈ ds.zip l ∧ R d (f a)
  | _, [], _, a, ha => absurd ha List.not_mem_nil
  | [], _ :: _, h, _, _ => by simp at h
  | d :: ds, x :: l, h, a, ha => by
    rw [List.map_cons, List.forall₂_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨d, by simp, h.1⟩
    · obtain ⟨d', hd', hR⟩ := forall₂_map_zip h.2 a ha
      exact ⟨d', by simp [hd'], hR⟩

/-- **The wrap circuit's finalize block reads as each finalized proof's scalar half.** Under any
valuation satisfying the emitted constraints, with the branch bits reading as the indicator of
`b`, every slot that branch `b` compiled for the key's domain (index `j` of `wrapDomainLog2s`,
generator `ω`, size `n`) and whose `shouldFinalize` is set reads as its scalar half. -/
theorem wrapFinalizePrevProofs_reads
    {branches mpv : ℕ}
    (E : Env IpaPallas.curve nc)
    (Vs : Valuation Fq)
    (gen : ℕ → Fq)
    (whichBranch : Vector (BoolVar Fq) branches)
    (slots : Vector (WrapFinalizeSlot branches E.σ.k nc Fq) mpv)
    (b : Fin branches) (j : ℕ)
    (hbits : CircuitType.Reads Vs whichBranch (Vector.ofFn fun l => decide (l = b)))
    (hdom : wrapDomainLog2s[j]? = some E.cvk.domainLog2)
    (hgen : gen E.cvk.domainLog2 = E.cvk.omega) :
    ⦃⌜True⌝⦄
    wrapFinalizePrevProofs (c := Builder Vs (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen whichBranch slots
    ⦃⇓ _ _ => ⌜∀ i : Fin mpv, slots[i].pins[b] = some j →
      (↑slots[i].unfinalized.shouldFinalize : CVar Fq).val Vs = 1 →
      slots[i].ScalarReads E Vs⌝⦄ := by
  -- the branch bits, as readings
  have hbits' : whichBranch.toList.map (fun x : BoolVar Fq => (↑x : CVar Fq).val Vs)
      = (List.range branches).map fun l => if l = b.val then (1 : Fq) else 0 := by
    refine List.ext_getElem (by simp) fun l h1 h2 => ?_
    have hl : l < branches := by simpa using h2
    have hr := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp hbits l hl)
    simp only [Vector.getElem_ofFn] at hr
    simp only [List.getElem_map, Vector.getElem_toList, List.getElem_range, hr]
    by_cases h : l = b.val <;> simp [h, bit, Fin.ext_iff]
  -- the key's domain is candidate `j` of the table
  obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hdom
  have hn : 2 ^ wrapDomainLog2s[j] = E.cvk.n := by rw [hjv]; rfl
  have hgen' : gen wrapDomainLog2s[j] = E.cvk.omega := by rw [hjv]; exact hgen
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
    (fun sl : WrapFinalizeSlot branches E.σ.k nc Fq =>
      pinWrapDomainIndex whichBranch.toList sl.pins.toList sl.domainIndex)
    (fun sl => sl.pins.toList[b.val]? = some (some j) → sl.domainIndex.val Vs = (j : Fq))
    (fun sl => by
      by_cases h : sl.pins.toList[b.val]? = some (some j)
      · refine builder_spec_imp _ _ _ (pinWrapDomainIndex_spec whichBranch.toList sl.pins.toList
          sl.domainIndex b j (by simpa using hbits') h) ?_
        intro _ hr _
        exact hr
      · refine builder_spec_imp _ _ _ (builder_spec_true _) ?_
        intro _ _ h'
        exact absurd h' h)
  -- each slot's domain: an index reading as `j` selects the key's domain
  have hdom := builder_spec_mapM (V := Vs) (c := KimchiConstraint Fq)
    (selectDomain gen wrapDomainLog2s)
    (fun (d : PlonkDomain Fq (Builder Vs (KimchiConstraint Fq))) (index : FVar Fq) =>
      index.val Vs = (j : Fq) → d.generator.val Vs = gen wrapDomainLog2s[j] ∧ ∀ zeta : FVar Fq,
        ⦃⌜True⌝⦄ d.vanishingPolynomial zeta
        ⦃⇓ r _ => ⌜r.val Vs = zeta.val Vs ^ 2 ^ wrapDomainLog2s[j] - 1⌝⦄) id
    (fun index => by
      by_cases h : index.val Vs = (j : Fq)
      · refine builder_spec_imp _ _ _ (selectDomain_spec gen wrapDomainLog2s index j hj h hinj) ?_
        intro _ hr _
        exact hr
      · refine builder_spec_imp _ _ _ (builder_spec_true _) ?_
        intro _ _ h'
        exact absurd h' h)
  -- each slot's body
  have hbody := builder_spec_mapM (V := Vs) (c := KimchiConstraint Fq)
    (fun (p : PlonkDomain Fq (Builder Vs (KimchiConstraint Fq)) ×
        WrapFinalizeSlot branches E.σ.k nc Fq) =>
      do
        let o ← finalizeOtherProofWrap (c := Builder Vs (KimchiConstraint Fq))
          (FopParams.ofEnv E Linearization.fqTokens) p.1.generator p.1.vanishingPolynomial
          p.2.unfinalized p.2.evals (p.2.prevChallenges.toList.map Vector.toList)
        assertAny [o.finalized, Snarky.not p.2.unfinalized.shouldFinalize]
        pure o)
    (fun _ p => p.1.generator.val Vs = E.cvk.omega →
      (∀ z, ⦃⌜True⌝⦄ p.1.vanishingPolynomial z ⦃⇓ v _ => ⌜v.val Vs = z.val Vs ^ E.cvk.n - 1⌝⦄) →
      (↑p.2.unfinalized.shouldFinalize : CVar Fq).val Vs = 1 → p.2.ScalarReads E Vs) id
    (fun p => wrapFinalizeBody_spec E Vs p.1 p.2)
  mvcgen [hpin, hdom, hbody]
  rename_i hpinP rev _ hrev _ _
  intro hos i hpb hsf
  have hsl : slots[i] ∈ slots.toList := by simp
  have hidx := hpinP _ hsl (by simpa using hpb)
  rw [List.map_id] at hrev
  rw [← List.reverse_reverse rev] at hrev
  have hrev' := List.forall₂_reverse_iff.mp hrev
  obtain ⟨d, hdz, hd⟩ := forall₂_map_zip hrev' _ hsl
  obtain ⟨hg, hv⟩ := hd hidx
  obtain ⟨_, -, hR⟩ := forall₂_map_zip (f := id) hos (d, slots[i]) hdz
  exact hR (hg.trans hgen') (fun z => builder_spec_imp _ _ _ (hv z) fun r hr => by rw [hr, hn])
    hsf

end Capstone

end Pickles
