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
* `selectDomain`: one slot's domain from its index.
* `WrapFinalizeSlot`: one slot's cells and compile-time pins.
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

/-- The domain a slot's index selects among `log2s`: its one-hot bits, then `toDomain`. -/
def selectDomain (gen : ℕ → F) (log2s : List ℕ) (index : FVar F) :
    CircuitM F c (PlonkDomain F c) := do
  let which ← oneHotVector log2s.length index
  toDomain gen which log2s

/-- One slot of the finalize block: its wrap domain index cell, its column of compile-time
domain indices over the branches (`none` for a side-loaded predecessor), and the finalized
proof's unfinalized claims, evaluations and padded previous challenges. -/
structure WrapFinalizeSlot (k nc : ℕ) (F : Type) where
  /-- The wrap domain index cell. -/
  domainIndex : FVar F
  /-- Each branch's compile-time domain index for this slot. -/
  pins : List (Option ℕ)
  /-- The finalized proof's unfinalized claims. -/
  unfinalized : UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (FVar F))
  /-- Its evaluations. -/
  evals : ChunkedEvals nc (FVar F)
  /-- Its padded previous challenges. -/
  prevChallenges : Vector (Vector (FVar F) k) MaxProofsVerified

/-- The wrap circuit's finalize block over its slots: the pins, left to right; the domains, right
to left, among `log2s` with generators `gen`; the finalize bodies with their assertions, left
to right. Returns each slot's finalize output. -/
def wrapFinalizePrevProofs {k nc : ℕ} (P : FopParams F) (gen : ℕ → F) (log2s : List ℕ)
    (whichBranch : List (BoolVar F)) (slots : List (WrapFinalizeSlot k nc F)) :
    CircuitM F c (List (FopOutput F)) := do
  slots.forM fun sl => pinWrapDomainIndex whichBranch sl.pins sl.domainIndex
  let rev ← (slots.map (·.domainIndex)).reverse.mapM (selectDomain gen log2s)
  (rev.reverse.zip slots).mapM fun (d, sl) => do
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

omit [DecidableEq F] [ToNat F] in
/-- Weights reading as the indicator of `b` pick a list's `b`-th entry. -/
theorem sum_indicator {α : Type} (f : α → F) :
    ∀ (xs : List α) (ws : List F) (b : ℕ),
      ws = (List.range xs.length).map (fun l => if l = b then (1 : F) else 0) →
      (hb : b < xs.length) → ((ws.zip xs).map fun e => e.1 * f e.2).sum = f xs[b]
  | [], _, _, _, hb => absurd hb (Nat.not_lt_zero _)
  | x :: xs, ws, b, hws, hb => by
    rw [List.length_cons, List.range_succ_eq_map] at hws
    subst hws
    cases b with
    | zero =>
      simp only [List.map_cons, List.map_map, List.zip_cons_cons, List.sum_cons,
        List.getElem_cons_zero]
      rw [if_pos trivial, one_mul, add_eq_left]
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      obtain ⟨l, -, hl⟩ := List.mem_map.mp (List.of_mem_zip he).1
      rw [← hl]
      simp
    | succ b =>
      simp only [List.map_cons, List.map_map, List.zip_cons_cons, List.sum_cons,
        List.getElem_cons_succ]
      rw [if_neg (Nat.succ_ne_zero b).symm, zero_mul, zero_add]
      refine sum_indicator f xs _ b ?_ (by simpa using hb)
      simp [Function.comp_def]

omit [DecidableEq F] [ToNat F] in
/-- A sum over bits zipped with values is the sum over the bits' readings zipped with them. -/
private theorem sum_zip_bits {α : Type} (bits : List (BoolVar F)) (xs : List α) (g : α → F) :
    ((bits.zip xs).map fun e => (↑e.1 : CVar F).val V * g e.2).sum
      = (((bits.map fun x : BoolVar F => (↑x : CVar F).val V).zip xs).map
          fun e => e.1 * g e.2).sum := by
  rw [List.zip_map_left, List.map_map]
  rfl

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

omit [ToNat F] [KimchiSystem F c] in
/-- Under any valuation satisfying the emitted constraints, with the index reading as
`j < log2s.length` and the casts of the candidate indices distinct from `j`'s, the selected
domain's generator reads as `gen log2s[j]` and its vanishing polynomial as `ζ^(2^log2s[j]) − 1`. -/
theorem selectDomain_spec (gen : ℕ → F) (log2s : List ℕ) (index : FVar F) (j : ℕ)
    (hj : j < log2s.length) (hidx : index.val V = (j : F))
    (hinj : ∀ l < log2s.length, (j : F) = l → j = l) :
    ⦃⌜True⌝⦄ selectDomain (c := Builder V c) gen log2s index
    ⦃⇓ d _ => ⌜d.generator.val V = gen log2s[j] ∧ ∀ zeta : FVar F,
      ⦃⌜True⌝⦄ d.vanishingPolynomial zeta
      ⦃⇓ r _ => ⌜r.val V = zeta.val V ^ 2 ^ log2s[j] - 1⌝⦄⌝⦄ := by
  simp only [selectDomain]
  have hw := oneHotVector_spec (c := c) (V := V) log2s.length index
  have hd := fun which => toDomain_spec (c := c) (V := V) gen which log2s
  mvcgen [hw, hd]
  rename_i bits _ hbits d _
  intro hg hv
  have hind : bits.map (fun x : BoolVar F => (↑x : CVar F).val V)
      = (List.range log2s.length).map fun l => if l = j then (1 : F) else 0 := by
    rw [hbits.1]
    refine List.map_congr_left fun l hl => ?_
    rw [hidx]
    by_cases h : l = j
    · simp [h]
    · rw [if_neg h, if_neg fun h' => h (hinj l (List.mem_range.mp hl) h').symm]
  have hpick := fun f : ℕ → F =>
    (sum_zip_bits bits log2s f).trans (sum_indicator f log2s _ j hind hj)
  refine ⟨hg.trans (hpick gen), fun zeta => builder_spec_imp _ _ _ (hv zeta) ?_⟩
  intro r hr
  rw [hr, hpick fun l => zeta.val V ^ 2 ^ l]

end Reads

/-! ## At a wrap proof -/

section Capstone

open Bulletproof Bulletproof.Ipa Kimchi.Protocol.Linearization Poseidon.FqSponge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

variable {nc : ℕ}

/-- A finalize slot reads as a wrap proof's scalar half: for any wrap proof and public input
under the guards, a step circuit's group half accepting it at asserted success, the ties and
the deferred `sg` equation make `kimchiVerify` accept. -/
def WrapFinalizeSlot.ScalarReads (E : Env IpaPallas.curve nc) (Vs : Valuation Fq)
    (sl : WrapFinalizeSlot E.σ.k nc Fq) : Prop :=
  ∀ (cp : KimchiProof IpaPallas.curve nc E.σ.k) (pub : Array Fq),
    Guards IpaPallas.curve E.cvk cp pub →
    ∀ (Vg : Valuation Fp)
      (claimsG : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
        (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) (successG : BoolVar Fp),
      (GroupHalf.step Vg claimsG).Reads E cp pub successG → (↑successG : CVar Fp).val Vg = 1 →
      HalvesTies (GroupHalf.step Vg claimsG)
        (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
      FopTies E cp pub (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
      SgOk E.σ E.cvk cp pub → kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true

/-- Under any valuation satisfying the emitted constraints, a slot's finalize at a generator
cell reading as the key's and a vanishing polynomial reading `ζⁿ − 1` at the key's size reads,
once `finalized` is `1`, as the slot's scalar half. -/
theorem finalizeOtherProofWrap_scalarReads (E : Env IpaPallas.curve nc) (Vs : Valuation Fq)
    (sl : WrapFinalizeSlot E.σ.k nc Fq) (gen : FVar Fq) (hgen : gen.val Vs = E.cvk.omega)
    (vanishing : FVar Fq → CircuitM Fq (Builder Vs (KimchiConstraint Fq)) (FVar Fq))
    (hvan : ∀ z, ⦃⌜True⌝⦄ vanishing z ⦃⇓ v _ => ⌜v.val Vs = z.val Vs ^ E.cvk.n - 1⌝⦄) :
    ⦃⌜True⌝⦄
    finalizeOtherProofWrap (c := Builder Vs (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen vanishing sl.unfinalized sl.evals
      (sl.prevChallenges.toList.map Vector.toList)
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
    gen E.cvk.n E.zkRows_le (by rw [hgen]; exact E.omega_prim.pow_eq_one) _ hvan
    sl.unfinalized sl.evals (sl.prevChallenges.toList.map Vector.toList) _ hprev
  refine builder_spec_imp _ _ _ hspec ?_
  intro o hread hfin cp pub hguard Vg claimsG successG hg hgbit ht hf hsg
  rw [hgen] at hread
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
          = ((ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges).prevVals).flatten := by
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

/-- One slot's finalize body: under any valuation satisfying the emitted constraints, with the
slot's domain reading as the key's (its generator `ω`, its vanishing polynomial `ζⁿ − 1`) and
`shouldFinalize` set, the slot reads as its scalar half. -/
theorem wrapFinalizeBody_spec (E : Env IpaPallas.curve nc) (Vs : Valuation Fq)
    (d : PlonkDomain Fq (Builder Vs (KimchiConstraint Fq))) (sl : WrapFinalizeSlot E.σ.k nc Fq) :
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
  · have hf := builder_spec_and _ _ _
      (finalizeOtherProofWrap_scalarReads E Vs sl d.generator h.1 d.vanishingPolynomial h.2)
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
`b`, every slot that branch `b` compiled for the key's domain (index `j` of `log2s`, generator
`ω`, size `n`) and whose `shouldFinalize` is set reads as its scalar half. -/
theorem wrapFinalizePrevProofs_reads (E : Env IpaPallas.curve nc) (Vs : Valuation Fq)
    (gen : ℕ → Fq) (log2s : List ℕ) (whichBranch : List (BoolVar Fq))
    (slots : List (WrapFinalizeSlot E.σ.k nc Fq)) (b j : ℕ)
    (hbits : whichBranch.map (fun x : BoolVar Fq => (↑x : CVar Fq).val Vs)
      = (List.range whichBranch.length).map fun l => if l = b then (1 : Fq) else 0)
    (hpins : ∀ sl ∈ slots, sl.pins.length = whichBranch.length)
    (hj : j < log2s.length) (hgen : gen log2s[j] = E.cvk.omega) (hn : 2 ^ log2s[j] = E.cvk.n)
    (hinj : ∀ l < log2s.length, (j : Fq) = l → j = l) :
    ⦃⌜True⌝⦄
    wrapFinalizePrevProofs (c := Builder Vs (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen log2s whichBranch slots
    ⦃⇓ _ _ => ⌜∀ sl ∈ slots, sl.pins[b]? = some (some j) →
      (↑sl.unfinalized.shouldFinalize : CVar Fq).val Vs = 1 → sl.ScalarReads E Vs⌝⦄ := by
  simp only [wrapFinalizePrevProofs]
  -- each slot's pin: on a slot branch `b` compiled for `j`, the index reads as `j`
  have hpin := forM_spec (V := Vs) (c := KimchiConstraint Fq)
    (fun sl : WrapFinalizeSlot E.σ.k nc Fq => pinWrapDomainIndex whichBranch sl.pins sl.domainIndex)
    (fun sl => sl.pins.length = whichBranch.length → sl.pins[b]? = some (some j) →
      sl.domainIndex.val Vs = (j : Fq))
    (fun sl => by
      by_cases h : sl.pins.length = whichBranch.length ∧ sl.pins[b]? = some (some j)
      · refine builder_spec_imp _ _ _ (pinWrapDomainIndex_spec whichBranch sl.pins
          sl.domainIndex b j (by rw [h.1]; exact hbits) h.2) ?_
        intro _ hr _ _
        exact hr
      · refine builder_spec_imp _ _ _ (builder_spec_true _) ?_
        intro _ _ h1 h2
        exact absurd ⟨h1, h2⟩ h)
  -- each slot's domain: an index reading as `j` selects the key's domain
  have hdom := builder_spec_mapM (V := Vs) (c := KimchiConstraint Fq)
    (selectDomain gen log2s)
    (fun (d : PlonkDomain Fq (Builder Vs (KimchiConstraint Fq))) (index : FVar Fq) =>
      index.val Vs = (j : Fq) → d.generator.val Vs = gen log2s[j] ∧ ∀ zeta : FVar Fq,
        ⦃⌜True⌝⦄ d.vanishingPolynomial zeta
        ⦃⇓ r _ => ⌜r.val Vs = zeta.val Vs ^ 2 ^ log2s[j] - 1⌝⦄) id
    (fun index => by
      by_cases h : index.val Vs = (j : Fq)
      · refine builder_spec_imp _ _ _ (selectDomain_spec gen log2s index j hj h hinj) ?_
        intro _ hr _
        exact hr
      · refine builder_spec_imp _ _ _ (builder_spec_true _) ?_
        intro _ _ h'
        exact absurd h' h)
  -- each slot's body
  have hbody := builder_spec_mapM (V := Vs) (c := KimchiConstraint Fq)
    (fun (p : PlonkDomain Fq (Builder Vs (KimchiConstraint Fq)) × WrapFinalizeSlot E.σ.k nc Fq) =>
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
  intro hos sl hsl hpb hsf
  have hidx := hpinP sl hsl (hpins sl hsl) hpb
  rw [List.map_id] at hrev
  rw [← List.reverse_reverse rev] at hrev
  have hrev' := List.forall₂_reverse_iff.mp hrev
  obtain ⟨d, hdz, hd⟩ := forall₂_map_zip hrev' sl hsl
  obtain ⟨hg, hv⟩ := hd hidx
  obtain ⟨_, -, hR⟩ := forall₂_map_zip (f := id) hos (d, sl) hdz
  exact hR (hg.trans hgen) (fun z => builder_spec_imp _ _ _ (hv z) fun r hr => by rw [hr, hn])
    hsf

end Capstone

end Pickles
