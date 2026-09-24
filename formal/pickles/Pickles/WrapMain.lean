import Pickles.WrapFinalize
import Pickles.VkComms

set_option mvcgen.warning false

/-!
# The wrap circuit

Transcribes `wrap_main.ml`. The wrap circuit verifies one step proof, chosen among the tag's
branches, and finalizes the previous wrap proofs that step proof verified.

## Main definitions

* `onesVector`: the slot mask, `true` up to the branch's first unused slot.
* `wrapBranchBlock`: the branch bits, the slot mask, the branch's step domain, and the
  statement's branch data asserted to pack them.
* `splitUnfinalized`: a previous proof's claims with their shifted scalars split.
* `chooseKey`: the active branch's step key, the branches' keys summed under the one-hot bits
  and sealed.

## Main results

* `onesVector_spec`: with the first unused slot reading as `w`, slot `i` reads as `[i < w]`.
* `wrapBranchBlock_spec`: the branch data reads as `4·log2s[b] + Σᵢ 2^(1−i)·[i < widths[b]]`
  for the branch `b` the bits name.
* `splitUnfinalized_spec`: each split scalar joins to its original (`SplitReads`).
-/

namespace Pickles

open Snarky Snarky.Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- The slot mask over `mpv` slots: slot `i` is set while no slot up to `i` equals
`firstZero`, one `equals` and one `and` per slot, in slot order. -/
def onesVector (firstZero : FVar F) (mpv : ℕ) : CircuitM F c (List (BoolVar F)) :=
  go true_ 0 mpv
where
  /-- The slots from `i` on, `value` the mask so far. -/
  go (value : BoolVar F) (i : ℕ) : ℕ → CircuitM F c (List (BoolVar F))
    | 0 => pure []
    | m + 1 => do
      let eq ← equals firstZero (.const (i : F))
      let v ← Snarky.and value (Snarky.not eq)
      let rest ← go v (i + 1) m
      pure (v :: rest)

/-- The branch block: the one-hot bits of `whichBranch` over the branches, the branch's slot
count among `widths`, the slot mask, the branch's step domain among `log2s`, and the
assertion that `branchData` packs the domain and the mask as `4·domainLog2 + Σᵢ 2^(1−i)·maskᵢ`.
Returns the bits and the mask. -/
def wrapBranchBlock (branches mpv : ℕ) (widths log2s : List ℕ) (whichBranch branchData : FVar F) :
    CircuitM F c (List (BoolVar F) × List (BoolVar F)) := do
  let bits ← oneHotVector branches whichBranch
  let firstZero ← Pseudo.choose bits widths fun w => .const (w : F)
  let mask ← onesVector firstZero mpv
  let domainLog2 ← Pseudo.choose bits log2s fun d => .const (d : F)
  let packedMask := ((List.range mpv).zip mask).foldl
    (fun acc im => CVar.add_ acc (CVar.scale_ ((2 ^ (1 - im.1) : ℕ) : F) ↑im.2)) (.const 0)
  assertEqual branchData (CVar.add_ packedMask (CVar.scale_ 4 domainLog2))
  pure (bits, mask)

/-- One shifted scalar split into its halved representative and parity bit. -/
def splitShifted [ToNat F] (x : Type2 (FVar F)) :
    CircuitM F c (Type2 (SplitField (FVar F) (BoolVar F))) := do
  let r ← splitFieldVar x.val
  pure ⟨⟨r.1, r.2⟩⟩

/-- A previous proof's claims with its five shifted scalars split, in the order combined inner
product, `b`, `ζ^(srs length)`, `ζⁿ`, permutation scalar. -/
def splitUnfinalized [ToNat F] {k : ℕ}
    (u : UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (FVar F))) :
    CircuitM F c
      (UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (SplitField (FVar F) (BoolVar F)))) := do
  let cip ← splitShifted u.deferredValues.combinedInnerProduct
  let b ← splitShifted u.deferredValues.b
  let ztSrs ← splitShifted u.deferredValues.plonk.zetaToSrsLength
  let ztDom ← splitShifted u.deferredValues.plonk.zetaToDomainSize
  let perm ← splitShifted u.deferredValues.plonk.perm
  pure
    { deferredValues :=
        { plonk := { u.deferredValues.plonk with
            perm := perm, zetaToSrsLength := ztSrs, zetaToDomainSize := ztDom }
          combinedInnerProduct := cip
          xi := u.deferredValues.xi
          bulletproofChallenges := u.deferredValues.bulletproofChallenges
          b := b }
      shouldFinalize := u.shouldFinalize
      spongeDigestBeforeEvaluations := u.spongeDigestBeforeEvaluations }

section ChooseKey

variable {nc : ℕ}

/-- A point's coordinates multiplied by a bit, `y` before `x`: one branch's term of the
coordinate-wise selection. -/
private def scalePt (b : FVar F) (p : AffinePoint (FVar F)) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let y ← mul b p.y
  let x ← mul b p.x
  pure ⟨x, y⟩

/-- `f` over a vector's entries, last to first, the results in entry order. -/
private def vecMapMRev {α β : Type} {n : ℕ} (f : α → CircuitM F c β) (v : Vector α n) :
    CircuitM F c (Vector β n) := do
  let rev ← v.reverse.mapM f
  pure rev.reverse

/-- `f` over a key's commitments: the selectors from endo-mul-scalar back to generic, then the
coefficients and `σ` each last to first; each commitment's chunks first to last. -/
private def VkComms.mapMRev (f : AffinePoint (FVar F) → CircuitM F c (AffinePoint (FVar F)))
    (k : VkComms nc (AffinePoint (FVar F))) : CircuitM F c (VkComms nc (AffinePoint (FVar F))) := do
  let endomulScalarComm ← k.endomulScalarComm.mapM f
  let emulComm ← k.emulComm.mapM f
  let mulComm ← k.mulComm.mapM f
  let completeAddComm ← k.completeAddComm.mapM f
  let poseidonComm ← k.poseidonComm.mapM f
  let genericComm ← k.genericComm.mapM f
  let coefficientsComm ← vecMapMRev (·.mapM f) k.coefficientsComm
  let sigmaComm ← vecMapMRev (·.mapM f) k.sigmaComm
  pure ⟨sigmaComm, coefficientsComm, genericComm, poseidonComm, completeAddComm, mulComm,
    emulComm, endomulScalarComm⟩

/-- Two keys' commitments added point by point. -/
private def VkComms.add (a b : VkComms nc (AffinePoint (FVar F))) :
    VkComms nc (AffinePoint (FVar F)) :=
  let pt (p q : AffinePoint (FVar F)) : AffinePoint (FVar F) :=
    ⟨CVar.add_ p.x q.x, CVar.add_ p.y q.y⟩
  let ch (u v : Vector (AffinePoint (FVar F)) nc) := Vector.zipWith pt u v
  ⟨Vector.zipWith ch a.sigmaComm b.sigmaComm,
    Vector.zipWith ch a.coefficientsComm b.coefficientsComm, ch a.genericComm b.genericComm,
    ch a.poseidonComm b.poseidonComm, ch a.completeAddComm b.completeAddComm,
    ch a.mulComm b.mulComm, ch a.emulComm b.emulComm, ch a.endomulScalarComm b.endomulScalarComm⟩

/-- The active branch's key, selected coordinate by coordinate: each branch's commitments
multiplied by its bit, branches last to first, the products summed and each sum sealed. With
one-hot bits, every inactive branch contributes zero to each coordinate. -/
def chooseKey {branches : ℕ} (bits : Vector (BoolVar F) (branches + 1))
    (keys : Vector (VkComms nc (AffinePoint (FVar F))) (branches + 1)) :
    CircuitM F c (VkComms nc (AffinePoint (FVar F))) := do
  let scaled ← vecMapMRev (fun (e : BoolVar F × VkComms nc (AffinePoint (FVar F))) =>
    VkComms.mapMRev (scalePt (↑e.1 : FVar F)) e.2) (bits.zip keys)
  let sum := scaled.tail.toList.foldl VkComms.add scaled.head
  VkComms.mapMRev sealPoint sum

end ChooseKey

/-! ## The reads -/

section Reads

open Std.Do

variable [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}

/-- From slot `i` on, with `firstZero` reading as `w` and the mask so far as `[i ≤ w]`, each
slot reads as `[slot < w]`. -/
private theorem onesVector.go_spec (firstZero : FVar F) :
    ∀ (m i : ℕ) (value : BoolVar F),
      ⦃⌜True⌝⦄ onesVector.go (c := Builder V c) firstZero value i m
      ⦃⇓ r _ => ⌜∀ w : ℕ, firstZero.val V = (w : F) →
        (∀ j, i ≤ j → j < i + m → (j : F) = w → j = w) →
        (↑value : CVar F).val V = bit (decide (i ≤ w)) →
        r.map (fun b : BoolVar F => (↑b : CVar F).val V)
          = (List.range m).map fun j => bit (decide (i + j < w))⌝⦄
  | 0, i, value => by
    simp only [onesVector.go]
    mvcgen
    simp
  | m + 1, i, value => by
    simp only [onesVector.go]
    have heq := equals_spec (V := V) (c := c) firstZero (.const (i : F))
    have ih := fun v => onesVector.go_spec firstZero m (i + 1) v
    mvcgen [heq, ih]
    rename_i eq _ heq' v _ hv rest _ hrest
    intro w hw hinj hval
    have heqb : (↑eq : CVar F).val V = bit (decide (i = w)) := by
      rw [heq', hw]
      by_cases h : i = w
      · subst h; simp [bit]
      · have : ¬ ((w : F) = (i : F)) := fun h' => h (hinj i le_rfl (by omega) h'.symm)
        simp [bit, h, this]
    have hvb := hv _ _ hval (not_val heqb)
    have hlt : (decide (i ≤ w) && !decide (i = w)) = decide (i + 1 ≤ w) := by
      by_cases h1 : i ≤ w <;> by_cases h2 : i = w <;> simp [h1, h2] <;> omega
    rw [hlt] at hvb
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, hvb,
      hrest w hw (fun j h1 h2 => hinj j (by omega) (by omega)) hvb]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [show i + 1 + j = i + (j + 1) by omega]

/-- **The slot mask.** Under any valuation satisfying the emitted constraints, with `firstZero`
reading as `w` and the slot indices below `mpv` distinct from `w` in the field unless equal,
slot `i` reads as `[i < w]`: the first `w` slots are set. -/
theorem onesVector_spec (firstZero : FVar F) (mpv : ℕ) :
    ⦃⌜True⌝⦄ onesVector (c := Builder V c) firstZero mpv
    ⦃⇓ r _ => ⌜∀ w : ℕ, firstZero.val V = (w : F) → (∀ j < mpv, (j : F) = w → j = w) →
      r.map (fun b : BoolVar F => (↑b : CVar F).val V)
        = (List.range mpv).map fun i => bit (decide (i < w))⌝⦄ := by
  unfold onesVector
  refine builder_spec_imp _ _ _ (onesVector.go_spec firstZero mpv 0 true_) fun r hr w hw hinj => ?_
  simpa using hr w hw (fun j _ hj h => hinj j (by omega) h) (by simp [true_, bit])

omit [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] in
/-- The packed mask's fold reads as the weighted sum of the mask's readings. -/
private theorem packedMask_val (f : ℕ → F) :
    ∀ (xs : List ℕ) (ms : List (BoolVar F)) (acc : CVar F),
      ms.map (fun b : BoolVar F => (↑b : CVar F).val V) = xs.map f →
      ((xs.zip ms).foldl (fun acc im => CVar.add_ acc
          (CVar.scale_ ((2 ^ (1 - im.1) : ℕ) : F) ↑im.2)) acc).val V
        = acc.val V + (xs.map fun i => ((2 ^ (1 - i) : ℕ) : F) * f i).sum
  | [], _, acc, _ => by simp
  | x :: xs, [], acc, h => by simp at h
  | x :: xs, m :: ms, acc, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons, List.sum_cons]
    rw [packedMask_val f xs ms _ h.2, CVar.val_add_, CVar.val_scale_, h.1]
    ring

/-- **The branch block.** Under any valuation satisfying the emitted constraints, `whichBranch`
names a branch `b`: the bits read as the indicator of `b`, the mask as `[i < widths[b]]`, and
`branchData` as `4·log2s[b] + Σᵢ 2^(1−i)·[i < widths[b]]`, given the branch indices and the slot
counts up to `mpv` distinct in the field. -/
theorem wrapBranchBlock_spec (branches mpv : ℕ) (widths log2s : List ℕ)
    (whichBranch branchData : FVar F) (hwl : widths.length = branches)
    (hll : log2s.length = branches) (hw : ∀ w ∈ widths, w ≤ mpv)
    (hinjB : ∀ j k : ℕ, j < branches → k < branches → (j : F) = k → j = k)
    (hinj : ∀ j k : ℕ, j ≤ mpv → k ≤ mpv → (j : F) = k → j = k) :
    ⦃⌜True⌝⦄ wrapBranchBlock (c := Builder V c) branches mpv widths log2s whichBranch branchData
    ⦃⇓ r _ => ⌜∃ (b : ℕ) (hb : b < branches), whichBranch.val V = (b : F) ∧
      r.1.map (fun x : BoolVar F => (↑x : CVar F).val V)
        = (List.range branches).map (fun l => if l = b then (1 : F) else 0) ∧
      r.2.map (fun x : BoolVar F => (↑x : CVar F).val V)
        = (List.range mpv).map (fun i => bit (decide (i < widths[b]'(by omega)))) ∧
      branchData.val V = 4 * (log2s[b]'(by omega) : F)
        + ((List.range mpv).map fun i =>
            ((2 ^ (1 - i) : ℕ) : F) * bit (decide (i < widths[b]'(by omega)))).sum⌝⦄ := by
  simp only [wrapBranchBlock]
  have hOH := oneHotVector_spec (c := c) (V := V) branches whichBranch
  have hFZ := fun bits => Pseudo.choose_spec (c := c) (V := V) bits widths
    fun w => (.const (w : F) : FVar F)
  have hOV := fun fz => onesVector_spec (c := c) (V := V) fz mpv
  have hDL := fun bits => Pseudo.choose_spec (c := c) (V := V) bits log2s
    fun d => (.const (d : F) : FVar F)
  have hAE := fun x y => assertEqual_spec (c := c) (V := V) x y
  mvcgen [hOH, hFZ, hOV, hDL, hAE]
  rename_i bits _ hbits fz _ hfz mask _ hmask dom _ hdom _ _ hbd
  obtain ⟨hbits, j, hj, hjv⟩ := hbits
  -- the bits, as the indicator of `j`
  have hind : bits.map (fun x : BoolVar F => (↑x : CVar F).val V)
      = (List.range branches).map (fun l => if l = j then (1 : F) else 0) := by
    rw [hbits]
    refine List.map_congr_left fun l hl => ?_
    rw [hjv]
    by_cases h : l = j
    · simp [h]
    · rw [if_neg h, if_neg fun h' => h (hinjB l j (List.mem_range.mp hl) hj h'.symm)]
  have hpick := fun (xs : List ℕ) (hxs : xs.length = branches) =>
    (sum_zip_bits (V := V) bits xs fun w => ((w : ℕ) : F)).trans
      (sum_indicator (fun w : ℕ => (w : F)) xs _ j (by rw [hxs]; exact hind) (by omega))
  have hfz' : fz.val V = (widths[j]'(by omega) : F) := by
    rw [hfz]; simpa using hpick widths hwl
  have hdom' : dom.val V = (log2s[j]'(by omega) : F) := by
    rw [hdom]; simpa using hpick log2s hll
  have hwj : widths[j]'(by omega) ≤ mpv := hw _ (List.getElem_mem _)
  have hmask' := hmask _ hfz' fun i hi h => hinj i _ (by omega) hwj h
  refine ⟨j, hj, hjv, hind, hmask', ?_⟩
  rw [hbd, CVar.val_add_, CVar.val_scale_, hdom',
    packedMask_val (V := V) (fun i => bit (decide (i < widths[j]'(by omega)))) _ mask _ hmask']
  simp only [CVar.val]
  ring

/-- A split shifted scalar joins to the original: its parity cell reads as a bit `bb` and
`x = 2·sDiv2 + bb`. -/
def SplitReads (V : Valuation F) (x : Type2 (FVar F))
    (y : Type2 (SplitField (FVar F) (BoolVar F))) : Prop :=
  ∃ bb : Bool, (↑y.val.sOdd : CVar F).val V = bit bb ∧ x.val.val V = 2 * y.val.sDiv2.val V + bit bb

/-- Under any valuation satisfying the emitted constraints, the split reads as the scalar. -/
theorem splitShifted_spec [ToNat F] (x : Type2 (FVar F)) :
    ⦃⌜True⌝⦄ splitShifted (c := Builder V c) x ⦃⇓ y _ => ⌜SplitReads V x y⌝⦄ := by
  unfold splitShifted
  have h := splitFieldVar_spec (V := V) (c := c) x.val
  mvcgen [h]

/-- **The split claims.** Under any valuation satisfying the emitted constraints, the split
claims keep every unshifted field and each split scalar joins to its original. -/
theorem splitUnfinalized_spec [ToNat F] {k : ℕ}
    (u : UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (FVar F))) :
    ⦃⌜True⌝⦄ splitUnfinalized (c := Builder V c) u
    ⦃⇓ r _ => ⌜r.deferredValues.plonk.alpha = u.deferredValues.plonk.alpha ∧
      r.deferredValues.plonk.beta = u.deferredValues.plonk.beta ∧
      r.deferredValues.plonk.gamma = u.deferredValues.plonk.gamma ∧
      r.deferredValues.plonk.zeta = u.deferredValues.plonk.zeta ∧
      r.deferredValues.xi = u.deferredValues.xi ∧
      r.deferredValues.bulletproofChallenges = u.deferredValues.bulletproofChallenges ∧
      r.shouldFinalize = u.shouldFinalize ∧
      r.spongeDigestBeforeEvaluations = u.spongeDigestBeforeEvaluations ∧
      SplitReads V u.deferredValues.combinedInnerProduct r.deferredValues.combinedInnerProduct ∧
      SplitReads V u.deferredValues.b r.deferredValues.b ∧
      SplitReads V u.deferredValues.plonk.perm r.deferredValues.plonk.perm ∧
      SplitReads V u.deferredValues.plonk.zetaToSrsLength r.deferredValues.plonk.zetaToSrsLength ∧
      SplitReads V u.deferredValues.plonk.zetaToDomainSize
        r.deferredValues.plonk.zetaToDomainSize⌝⦄ := by
  unfold splitUnfinalized
  have h := fun x => splitShifted_spec (V := V) (c := c) x
  mvcgen [h]

end Reads

end Pickles
