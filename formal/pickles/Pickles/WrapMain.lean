import Pickles.WrapFinalize
import Pickles.WrapVerify
import Pickles.StepSlot
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
* `wrapMain`: the wrap circuit over its statement, allocating its advice in the order the
  deployed circuit does: `wrapMainHead` up to the finalize block, then `wrapMainTail`.
* `chooseKey`: the active branch's step key, the branches' keys summed under the one-hot bits
  and sealed.

## Main results

* `onesVector_spec`: with the first unused slot reading as `w`, slot `i` reads as `[i < w]`.
* `chooseKey_spec`: with the bits reading as branch `b`, the chosen key reads as branch `b`'s.
* `vkReads_of_reads`: key cells reading as a key's constant cells read as its commitments
  (`VkReads`), the sponge after them squeezing to its digest.
* `wrapBranchBlock_spec`: the branch data reads as `4·log2s[b] + Σᵢ 2^(1−i)·[i < widths[b]]`
  for the branch `b` the bits name.
* `splitUnfinalized_spec`: each split scalar joins to its original (`SplitReads`).
* `wrapMain_reads`: the branch index names a branch whose domain and slot count the branch
  data packs, and every slot that branch compiled for the key's wrap domain, once
  `shouldFinalize` is set, reads as its scalar half.
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
def chooseKey {branches : ℕ} [NeZero branches] (bits : Vector (BoolVar F) branches)
    (keys : Vector (VkComms nc (AffinePoint (FVar F))) branches) :
    CircuitM F c (VkComms nc (AffinePoint (FVar F))) := do
  let scaled ← vecMapMRev (fun (e : BoolVar F × VkComms nc (AffinePoint (FVar F))) =>
    VkComms.mapMRev (scalePt (↑e.1 : FVar F)) e.2) (bits.zip keys)
  let sum := scaled.toList.tail.foldl VkComms.add (scaled[0]'(Nat.pos_of_neZero branches))
  VkComms.mapMRev sealPoint sum

end ChooseKey

/-! ## The circuit -/

section Main

open CompElliptic.Fields.Pasta Bulletproof Bulletproof.Ipa Kimchi.Verifier
open scoped Kimchi

/-- A Vesta point whose allocation checks it lies on `y² = x³ + 5`. -/
abbrev VestaPt (α : Type) : Type := CheckedPoint (F := Fq) 0 5 α

/-- The wrap proof's opening as allocated: the `(L, R)` pairs, the shifted `z₁`, `z₂`, `δ`,
`sg`. -/
abbrev WrapOpeningVal : Type :=
  Vector (VestaPt Fq × VestaPt Fq) StepIPARounds × Fq × Fq × VestaPt Fq × VestaPt Fq

/-- The step proof's commitments as allocated, `nc` chunks each: the witness columns, `z`,
the quotient pieces. -/
abbrev WrapMessagesVal (nc : ℕ) : Type :=
  Vector (Vector (VestaPt Fq) nc) wCols × Vector (VestaPt Fq) nc ×
    Vector (Vector (VestaPt Fq) nc) quotChunks

/-- The prover's values for every allocation of the wrap circuit, over `mpv` slots at `k`
rounds whose challenge stacks hold `wsum` vectors in all. -/
structure WrapMainAdvice (mpv nc k wsum : ℕ) where
  /-- The branch index. -/
  whichBranch : AsProver Fq Fq
  /-- The previous proofs' claims and the step-side message digest. -/
  proofState : AsProver Fq (Vector (AllocUnfinalized k Fq Bool (Type2 Fq)) mpv × Fq)
  /-- The step proof's accumulators. -/
  stepAccs : AsProver Fq (Vector (VestaPt Fq) mpv)
  /-- The slots' old challenge stacks, slot after slot. -/
  oldChallenges : AsProver Fq (Vector Fq (k * wsum))
  /-- The previous proofs' evaluations. -/
  evals : AsProver Fq (Vector (AllocEvals 1 Fq) mpv)
  /-- The previous proofs' wrap domain indices. -/
  domainIndices : AsProver Fq (Vector Fq mpv)
  /-- The step proof's opening. -/
  opening : AsProver Fq WrapOpeningVal
  /-- The step proof's commitments. -/
  messages : AsProver Fq (WrapMessagesVal nc)

/-- The wrap circuit's cells up to its finalize block: the branch index and bits, the slot
mask, the previous proofs' claims and step-side digest, the chosen key, the accumulators, each
slot's real challenge stacks, the finalize slots and their outputs. -/
structure WrapMainHead (branches mpv nc k : ℕ) where
  /-- The branch index cell. -/
  whichBranch : FVar Fq
  /-- The branch bits. -/
  bits : List (BoolVar Fq)
  /-- The slot mask. -/
  mask : List (BoolVar Fq)
  /-- The previous proofs' claims, as allocated, and the step-side message digest. -/
  proofState : Vector (AllocUnfinalized k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq))) mpv × FVar Fq
  /-- The chosen step key. -/
  key : VkComms nc (AffinePoint (FVar Fq))
  /-- The step proof's accumulators. -/
  stepAccs : Vector (VestaPt (FVar Fq)) mpv
  /-- Each slot's real challenge stacks. -/
  real : Fin mpv → List (List (FVar Fq))
  /-- The finalize slots. -/
  slots : Vector (WrapFinalizeSlot branches k 1 Fq) mpv
  /-- Their finalize outputs. -/
  outs : List (FopOutput Fq)

variable {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c]

/-- The wrap circuit up to its finalize block: the branch block over the statement's branch
data, the proof state, the key choice, the accumulators, the old challenge stacks, the
evaluations and wrap domain indices, then the finalize block over the slots. -/
def wrapMainHead {branches mpv nc k : ℕ} [NeZero branches] (P : FopParams Fq) (gen : ℕ → Fq)
    (widths log2s : List ℕ)
    (stepKeys : Vector (VkComms nc (AffinePoint (FVar Fq))) branches)
    (pins : Vector (Vector (Option ℕ) branches) mpv) (dummy : List Fq)
    (slotWidths : Vector ℕ mpv) (adv : WrapMainAdvice mpv nc k slotWidths.toList.sum)
    (branchData : FVar Fq) : CircuitM Fq c (WrapMainHead branches mpv nc k) := do
  let whichBranch ← witness (val := Fq) adv.whichBranch
  let (bits, mask) ← wrapBranchBlock branches mpv widths log2s whichBranch branchData
  let bitsV : Vector (BoolVar Fq) branches := Vector.ofFn fun i => bits.getD i.val true_
  let ps ← witness (val := Vector (AllocUnfinalized k Fq Bool (Type2 Fq)) mpv × Fq)
    adv.proofState
  let key ← chooseKey bitsV stepKeys
  let stepAccs ← witness (val := Vector (VestaPt Fq) mpv) adv.stepAccs
  let oldChals ← witness (val := Vector Fq (k * slotWidths.toList.sum)) adv.oldChallenges
  let evals ← witness (val := UnChecked (Vector (AllocEvals 1 Fq) mpv))
    (UnChecked.mk <$> adv.evals)
  let domainIndices ← witness (val := Vector Fq mpv) adv.domainIndices
  -- each slot's real challenge stacks, and front-padded to `MaxProofsVerified`
  let real (j : Fin mpv) : List (List (FVar Fq)) :=
    let off := (slotWidths.toList.take j.val).sum
    (List.range slotWidths[j]).map fun e =>
      (List.range k).map fun r => oldChals.toList.getD (k * (off + e) + r) (.const 0)
  let padded (j : Fin mpv) : Vector (Vector (FVar Fq) k) MaxProofsVerified :=
    let stack := List.replicate (MaxProofsVerified - slotWidths[j]) (dummy.map CVar.const)
      ++ real j
    Vector.ofFn fun a => Vector.ofFn fun r => (stack.getD a.val []).getD r.val (.const 0)
  let slots : Vector (WrapFinalizeSlot branches k 1 Fq) mpv :=
    Vector.ofFn fun j =>
      { domainIndex := domainIndices[j], pins := pins[j]
        unfinalized := ps.1[j].toUnfinalized, evals := evals.val[j].toChunked
        prevChallenges := padded j }
  let outs ← wrapFinalizePrevProofs P gen bitsV slots
  pure ⟨whichBranch, bits, mask, ps, key, stepAccs, real, slots, outs⟩

/-- The wrap circuit after its finalize block: the per-slot accumulator digests right to left,
the step-side digest's equality, the opening and messages, the claim split, and the verify
block over the public-input commitment masked across branches. -/
def wrapMainTail {branches mpv nc k : ℕ} (log2s : List ℕ)
    (lagrange : ℕ → List (Vector IpaVesta.curve.Point nc)) (h : IpaVesta.curve.Point)
    (dummy : List Fq) (slotWidths : Vector ℕ mpv)
    (adv : WrapMainAdvice mpv nc k slotWidths.toList.sum) (stmt : Vector (FVar Fq) 40)
    (hd : WrapMainHead branches mpv nc k) : CircuitM Fq c PUnit := do
  let get (i : ℕ) : FVar Fq := stmt[i]?.getD (.const 0)
  let sp := IpaVesta.curve.sponge.params
  let rev ← (List.finRange mpv).reverse.mapM fun j =>
    hashMessagesForNextWrapProof sp (wrapPaddingSponge sp dummy (MaxProofsVerified - slotWidths[j]))
      (hd.real j) hd.stepAccs[j].pt
  let msgs := rev.reverse
  assertEqual (get 12) hd.proofState.2
  let opening ← witness (val := WrapOpeningVal) adv.opening
  let messages ← witness (val := WrapMessagesVal nc) adv.messages
  let splits ← hd.proofState.1.mapM fun a => splitUnfinalized a.toUnfinalized
  let statement : StepStatement k mpv (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))) :=
    { proofState := { unfinalizedProofs := splits, messagesForNextStepProof := hd.proofState.2 }
      messagesForNextWrapProof := Vector.ofFn fun j => msgs.getD j.val (.const 0) }
  let dv : DeferredValues StepIPARounds (FVar Fq) (Type1 (FVar Fq)) :=
    { plonk := { alpha := ⟨get 7⟩, beta := ⟨get 5⟩, gamma := ⟨get 6⟩, zeta := ⟨get 8⟩,
                 perm := ⟨get 4⟩, zetaToSrsLength := ⟨get 2⟩, zetaToDomainSize := ⟨get 3⟩ }
      combinedInnerProduct := ⟨get 0⟩, b := ⟨get 1⟩, xi := ⟨get 9⟩
      bulletproofChallenges := Vector.ofFn fun j => ⟨get (13 + j)⟩ }
  let pr : IvpProof StepIPARounds nc (FVar Fq) (Type1 (FVar Fq)) :=
    { wComm := messages.1.map (·.map (·.pt))
      zComm := messages.2.1.map (·.pt)
      tComm := (messages.2.2.map (·.map (·.pt))).flatten
      opening := { lr := opening.1.map fun e => (e.1.pt, e.2.pt), z1 := ⟨opening.2.1⟩
                   z2 := ⟨opening.2.2.1⟩, delta := opening.2.2.2.1.pt
                   sg := opening.2.2.2.2.pt } }
  let maskRev := hd.mask.reverse
  let sgOld := (List.finRange mpv).map fun j =>
    (some (maskRev.getD j.val true_), hd.stepAccs[j].pt)
  let shared := log2s.all (· == log2s.headD 0)
  let sv ← spongeAfterIndex sp hd.key
  wrapVerify IpaScalarOps.wrap IpaEndo.vesta sp (.const ((Pasta.pallasLam : ℤ) : Fq))
    groupMapParamsVesta vestaBase.sqrt? (constPt h) sv
    (Vector.toList <$> publicInputCommitMasked (C := IpaVesta.curve) shared (constPt h) hd.bits
      statement.packed (log2s.map lagrange))
    (wrapPaddingSponge sp dummy (MaxProofsVerified - mpv))
    (hd.outs.map (·.expandedChallenges)) (get 11)
    { deferredValues := dv, shouldFinalize := true_, spongeDigestBeforeEvaluations := get 10 }
    (ivpInputOf dv sgOld hd.key pr)

/-- The wrap circuit over its 40-cell statement, at `k` rounds. The branches' slot counts
`widths`, step domains `log2s`, step keys and wrap domain pins are the tag's; `lagrange` gives
the Lagrange bases at a step domain, `h` the blinding base, `dummy` the padding challenge
vector, `slotWidths` each slot's challenge-stack height. Returns its cells up to the finalize
block. -/
def wrapMain {branches mpv nc k : ℕ} [NeZero branches] (P : FopParams Fq) (gen : ℕ → Fq)
    (widths log2s : List ℕ)
    (stepKeys : Vector (VkComms nc (AffinePoint (FVar Fq))) branches)
    (pins : Vector (Vector (Option ℕ) branches) mpv)
    (lagrange : ℕ → List (Vector IpaVesta.curve.Point nc)) (h : IpaVesta.curve.Point)
    (dummy : List Fq) (slotWidths : Vector ℕ mpv)
    (adv : WrapMainAdvice mpv nc k slotWidths.toList.sum) (stmt : Vector (FVar Fq) 40) :
    CircuitM Fq c (WrapMainHead branches mpv nc k) := do
  let hd ← wrapMainHead P gen widths log2s stepKeys pins dummy slotWidths adv
    (stmt[29]?.getD (.const 0))
  wrapMainTail log2s lagrange h dummy slotWidths adv stmt hd
  pure hd

/-- The wrap circuit as a circuit of its statement: `wrapMain`, its cells dropped. -/
def wrapMainCircuit {branches mpv nc k : ℕ} [NeZero branches] (P : FopParams Fq) (gen : ℕ → Fq)
    (widths log2s : List ℕ)
    (stepKeys : Vector (VkComms nc (AffinePoint (FVar Fq))) branches)
    (pins : Vector (Vector (Option ℕ) branches) mpv)
    (lagrange : ℕ → List (Vector IpaVesta.curve.Point nc)) (h : IpaVesta.curve.Point)
    (dummy : List Fq) (slotWidths : Vector ℕ mpv)
    (adv : WrapMainAdvice mpv nc k slotWidths.toList.sum) (stmt : Vector (FVar Fq) 40) :
    CircuitM Fq c Unit := do
  let _ ← wrapMain P gen widths log2s stepKeys pins lagrange h dummy slotWidths adv stmt
  pure ()

end Main

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

section ChooseKeyRead

open Kimchi

variable {nc : ℕ}

/-- A point of a key: a commitment and one of its chunks. -/
private inductive VkPos (nc : ℕ) where
  | sigma (i : Fin permCols) (c : Fin nc)
  | coeff (i : Fin coeffCols) (c : Fin nc)
  | generic (c : Fin nc)
  | poseidon (c : Fin nc)
  | completeAdd (c : Fin nc)
  | mul (c : Fin nc)
  | emul (c : Fin nc)
  | endomulScalar (c : Fin nc)

/-- A key's point at a position. -/
private def VkComms.at {f : Type} (k : VkComms nc f) : VkPos nc → f
  | .sigma i c => k.sigmaComm[i][c]
  | .coeff i c => k.coefficientsComm[i][c]
  | .generic c => k.genericComm[c]
  | .poseidon c => k.poseidonComm[c]
  | .completeAdd c => k.completeAddComm[c]
  | .mul c => k.mulComm[c]
  | .emul c => k.emulComm[c]
  | .endomulScalar c => k.endomulScalarComm[c]

omit [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] in
/-- A key reads as a value key exactly when every point does. -/
private theorem VkComms.reads_iff (k : VkComms nc (AffinePoint (FVar F)))
    (kv : VkComms nc (AffinePoint F)) :
    CircuitType.Reads V k kv ↔
      ∀ p, (k.at p).x.val V = (kv.at p).x ∧ (k.at p).y.val V = (kv.at p).y := by
  rw [CircuitType.reads_ofEquiv]
  simp only [VkComms.equivProd, Equiv.coe_fn_mk, CircuitType.reads_prod,
    CircuitType.reads_vector, reads_affinePoint]
  constructor
  · rintro ⟨hs, hc, hg, hp, hca, hm, he, hes⟩ p
    cases p with
    | sigma i c => exact hs i i.isLt c c.isLt
    | coeff i c => exact hc i i.isLt c c.isLt
    | generic c => exact hg c c.isLt
    | poseidon c => exact hp c c.isLt
    | completeAdd c => exact hca c c.isLt
    | mul c => exact hm c c.isLt
    | emul c => exact he c c.isLt
    | endomulScalar c => exact hes c c.isLt
  · intro h
    exact ⟨fun i hi c hc => h (.sigma ⟨i, hi⟩ ⟨c, hc⟩),
      fun i hi c hc => h (.coeff ⟨i, hi⟩ ⟨c, hc⟩), fun c hc => h (.generic ⟨c, hc⟩),
      fun c hc => h (.poseidon ⟨c, hc⟩), fun c hc => h (.completeAdd ⟨c, hc⟩),
      fun c hc => h (.mul ⟨c, hc⟩), fun c hc => h (.emul ⟨c, hc⟩),
      fun c hc => h (.endomulScalar ⟨c, hc⟩)⟩

/-- `f` over a vector last to first relates each entry to its result. -/
private theorem vecMapMRev_spec {α β : Type} {n : ℕ} (f : α → CircuitM F (Builder V c) β)
    (Q : α → β → Prop) (hf : ∀ a, ⦃⌜True⌝⦄ f a ⦃⇓ r _ => ⌜Q a r⌝⦄) (v : Vector α n) :
    ⦃⌜True⌝⦄ vecMapMRev f v ⦃⇓ rs _ => ⌜∀ i : Fin n, Q v[i] rs[i]⌝⦄ := by
  simp only [vecMapMRev]
  have h := builder_spec_vector_mapM_get f Q hf v.reverse
  mvcgen [h]
  rename_i rev _ hrev
  intro i
  have := hrev ⟨n - 1 - i, by omega⟩
  simp only [Vector.getElem_reverse] at this ⊢
  have hi : n - 1 - (n - 1 - i.val) = i.val := by omega
  simpa [hi] using this

/-- `f` over a key's commitments relates each point to its result. -/
private theorem VkComms.mapMRev_spec (f : AffinePoint (FVar F) → CircuitM F (Builder V c)
      (AffinePoint (FVar F))) (Q : AffinePoint (FVar F) → AffinePoint (FVar F) → Prop)
    (hf : ∀ p, ⦃⌜True⌝⦄ f p ⦃⇓ r _ => ⌜Q p r⌝⦄) (k : VkComms nc (AffinePoint (FVar F))) :
    ⦃⌜True⌝⦄ VkComms.mapMRev f k ⦃⇓ r _ => ⌜∀ p, Q (k.at p) (r.at p)⌝⦄ := by
  simp only [VkComms.mapMRev]
  have hv := fun (v : Vector (AffinePoint (FVar F)) nc) => builder_spec_vector_mapM_get f Q hf v
  have hvv := fun {m : ℕ} (vv : Vector (Vector (AffinePoint (FVar F)) nc) m) =>
    vecMapMRev_spec (fun v => v.mapM f) (fun v w => ∀ c : Fin nc, Q v[c] w[c]) (fun v => hv v) vv
  mvcgen [hv, hvv]
  rename_i _ _ hes _ _ he _ _ hm _ _ hca _ _ hp _ _ hg _ _ hc _ _ hs
  intro p
  cases p with
  | sigma i c => exact hs i c
  | coeff i c => exact hc i c
  | generic c => exact hg c
  | poseidon c => exact hp c
  | completeAdd c => exact hca c
  | mul c => exact hm c
  | emul c => exact he c
  | endomulScalar c => exact hes c

/-- A point scaled by a bit reads as the bit times each coordinate. -/
private theorem scalePt_spec (b : FVar F) (p : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ scalePt (c := Builder V c) b p
    ⦃⇓ r _ => ⌜r.x.val V = b.val V * p.x.val V ∧ r.y.val V = b.val V * p.y.val V⌝⦄ := by
  simp only [scalePt]
  mvcgen

omit [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] in
/-- Two keys added point by point read as the sums. -/
private theorem VkComms.add_at_val (a b : VkComms nc (AffinePoint (FVar F))) (p : VkPos nc) :
    ((VkComms.add a b).at p).x.val V = (a.at p).x.val V + (b.at p).x.val V ∧
      ((VkComms.add a b).at p).y.val V = (a.at p).y.val V + (b.at p).y.val V := by
  cases p <;> simp [VkComms.add, VkComms.at, CVar.val_add_]

omit [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] in
/-- A fold of `add` reads, point by point, as the sum of the keys' readings. -/
private theorem VkComms.foldl_add_at_val (p : VkPos nc) :
    ∀ (L : List (VkComms nc (AffinePoint (FVar F)))) (h : VkComms nc (AffinePoint (FVar F))),
      ((L.foldl VkComms.add h).at p).x.val V
          = ((h :: L).map fun k => (k.at p).x.val V).sum ∧
        ((L.foldl VkComms.add h).at p).y.val V
          = ((h :: L).map fun k => (k.at p).y.val V).sum
  | [], h => by simp
  | k :: L, h => by
    obtain ⟨hx, hy⟩ := VkComms.foldl_add_at_val p L (VkComms.add h k)
    obtain ⟨ax, ay⟩ := VkComms.add_at_val (V := V) h k p
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at hx hy ⊢
    rw [hx, hy, ax, ay]
    constructor <;> ring

/-- **The chosen key.** Under any valuation satisfying the emitted constraints, with the bits
reading as branch `b`'s one-hot vector, the chosen key reads as `keys[b]` does. -/
theorem chooseKey_spec {branches : ℕ} [NeZero branches] (bits : Vector (BoolVar F) branches)
    (keys : Vector (VkComms nc (AffinePoint (FVar F))) branches) (b : Fin branches)
    (hbits : CircuitType.Reads V bits (Vector.ofFn fun l => decide (l = b))) :
    ⦃⌜True⌝⦄ chooseKey (c := Builder V c) bits keys
    ⦃⇓ r _ => ⌜∀ kv : VkComms nc (AffinePoint F), CircuitType.Reads V keys[b] kv →
      CircuitType.Reads V r kv⌝⦄ := by
  simp only [chooseKey]
  have hs := fun e : BoolVar F × VkComms nc (AffinePoint (FVar F)) =>
    VkComms.mapMRev_spec (scalePt (↑e.1 : FVar F))
      (fun p r => r.x.val V = (↑e.1 : CVar F).val V * p.x.val V ∧
        r.y.val V = (↑e.1 : CVar F).val V * p.y.val V)
      (fun p => scalePt_spec (c := c) _ p) e.2
  have hscaled := vecMapMRev_spec (fun e : BoolVar F × VkComms nc (AffinePoint (FVar F)) =>
      VkComms.mapMRev (scalePt (↑e.1 : FVar F)) e.2)
    (fun e r => ∀ p, (r.at p).x.val V = (↑e.1 : CVar F).val V * (e.2.at p).x.val V ∧
      (r.at p).y.val V = (↑e.1 : CVar F).val V * (e.2.at p).y.val V) hs (bits.zip keys)
  have hseal := fun k : VkComms nc (AffinePoint (FVar F)) => VkComms.mapMRev_spec sealPoint
    (fun p r => r.x.val V = p.x.val V ∧ r.y.val V = p.y.val V)
    (fun p => sealPoint_spec (c := c) p) k
  mvcgen [hscaled, hseal]
  rename_i scaled _ hsc r _
  intro hr kv hk
  rw [VkComms.reads_iff] at hk ⊢
  intro p
  -- each bit reads as `[l = b]`
  have hbit : ∀ l : Fin branches, (↑bits[l] : CVar F).val V = if l = b then 1 else 0 := by
    intro l
    have h := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp hbits l l.isLt)
    simpa [bit, Fin.ext_iff] using h
  -- the sum over the branches picks branch `b`
  have hsum : ∀ g : VkComms nc (AffinePoint (FVar F)) → AffinePoint (FVar F) → F,
      (∀ i : Fin branches, g scaled[i] (scaled[i].at p)
        = (↑bits[i] : CVar F).val V * g keys[i] (keys[i].at p)) →
      ((scaled[0]'(Nat.pos_of_neZero branches) :: scaled.toList.tail).map
          fun k => g k (k.at p)).sum = g keys[b] (keys[b].at p) := by
    intro g hg
    have hl : scaled[0]'(Nat.pos_of_neZero branches) :: scaled.toList.tail = scaled.toList := by
      obtain ⟨⟨l⟩, hl⟩ := scaled
      cases l with
      | nil => exact absurd hl (by simpa using (NeZero.ne branches).symm)
      | cons a l => rfl
    rw [hl]
    have hof : scaled.toList.map (fun k => g k (k.at p))
        = List.ofFn fun i : Fin branches => g scaled[i] (scaled[i].at p) := by
      apply List.ext_getElem <;> simp
    rw [hof, List.sum_ofFn]
    simp only [hg, hbit, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  obtain ⟨hfx, hfy⟩ := VkComms.foldl_add_at_val (V := V) p scaled.toList.tail
    (scaled[0]'(Nat.pos_of_neZero branches))
  obtain ⟨hrx, hry⟩ := hr p
  refine ⟨?_, ?_⟩
  · rw [hrx, hfx, hsum (fun _ q => q.x.val V) fun i => by simpa using (hsc i p).1]
    exact (hk p).1
  · rw [hry, hfy, hsum (fun _ q => q.y.val V) fun i => by simpa using (hsc i p).2]
    exact (hk p).2

end ChooseKeyRead

end Reads

/-! ## A chosen key reads as a verifier key -/

section KeyRead

open Std.Do Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.CurveForms.ShortWeierstrass

variable {C : KimchiCurve} {nc : ℕ} {V : Valuation C.BaseField}

/-- A key's commitments as values, each point by its coordinates. -/
private def keyValsOf (cvk : KimchiVK C nc) : VkComms nc (AffinePoint C.BaseField) :=
  ⟨cvk.sigmaComm.map (·.map fun P => ⟨P.x, P.y⟩),
   cvk.coefficientsComm.map (·.map fun P => ⟨P.x, P.y⟩),
   cvk.genericComm.map (fun P => ⟨P.x, P.y⟩), cvk.poseidonComm.map (fun P => ⟨P.x, P.y⟩),
   cvk.completeAddComm.map (fun P => ⟨P.x, P.y⟩), cvk.mulComm.map (fun P => ⟨P.x, P.y⟩),
   cvk.emulComm.map (fun P => ⟨P.x, P.y⟩), cvk.endomulScalarComm.map (fun P => ⟨P.x, P.y⟩)⟩

/-- A key's constant cells read as its values. -/
private theorem reads_keyCellsOf (cvk : KimchiVK C nc) :
    CircuitType.Reads V (keyCellsOf constPt cvk) (keyValsOf cvk) := by
  rw [VkComms.reads_iff]
  intro p
  cases p <;> simp [keyCellsOf, keyValsOf, VkComms.at, constPt, CVar.val]

/-- The values' points are the key's commitments' coordinates. -/
private theorem keyValsOf_at (cvk : KimchiVK C nc) (p : VkPos nc) :
    (keyValsOf cvk).at p = ⟨(cvk.comms.at p).x, (cvk.comms.at p).y⟩ := by
  cases p <;> simp [keyValsOf, VkComms.at, KimchiVK.comms]

/-- **A key read as a verifier key's commitments.** Key cells reading as the constant cells of
`cvk` (`keyCellsOf constPt`) read as its commitments (`KeyReads`), once they are finite points,
and a sponge reading as the fresh sponge after their coordinates squeezes to its digest. -/
theorem vkReads_of_reads (E : Env C nc) (k : VkComms nc (AffinePoint (FVar C.BaseField)))
    (sv : SpongeVar C.BaseField)
    (hk : ∀ kv : VkComms nc (AffinePoint C.BaseField),
      CircuitType.Reads V (keyCellsOf constPt E.cvk) kv → CircuitType.Reads V k kv)
    (hnz : ∀ P ∈ E.cvk.comms.indexPoints, P ≠ 0)
    (hsv : SpongeVar.ReadsAt V sv (Poseidon.absorb C.sponge.params Poseidon.init
      (k.indexPoints.flatMap fun P => [P.x.val V, P.y.val V]))) :
    VkReads E.cvk V sv k := by
  have hpt := (VkComms.reads_iff k _).mp (hk _ (reads_keyCellsOf E.cvk))
  -- each cell reads as its commitment's coordinates
  have hat : ∀ p, (k.at p).x.val V = (E.cvk.comms.at p).x ∧
      (k.at p).y.val V = (E.cvk.comms.at p).y := by
    intro p
    simpa [keyValsOf_at] using hpt p
  have hnz' : ∀ p, E.cvk.comms.at p ≠ 0 := fun p => hnz _ (by
    cases p <;> simp only [VkComms.indexPoints, VkComms.selectors, KimchiVK.comms, VkComms.at,
      List.mem_flatMap, List.mem_append, List.mem_cons, Vector.mem_toList_iff] <;>
      exact ⟨_, by simp [Vector.getElem_mem], Vector.getElem_mem _⟩)
  have honc : ∀ p, OnCurveAt C.E.toAffine V (k.at p) (SWPoint.equivPoint C.E (E.cvk.comms.at p)) :=
    fun p => by
      have h := onCurveAt_constPt (V := V) _ (hnz' p)
      unfold OnCurveAt at h ⊢
      rw [(hat p).1, (hat p).2]
      simpa [constPt, CVar.val] using h
  have hvec : ∀ {m : ℕ} (cells : Vector (AffinePoint (FVar C.BaseField)) m)
      (Ps : Vector C.Point m), (∀ c : Fin m, OnCurveAt C.E.toAffine V cells[c]
        (SWPoint.equivPoint C.E Ps[c])) → CommReads C V cells.toList Ps.toList := by
    intro m cells Ps h
    exact List.forall₂_iff_get.mpr ⟨by simp, fun i h1 h2 => by simpa using h ⟨i, by simpa using h1⟩⟩
  have hkey : KeyReads C V k E.cvk := ⟨fun i => hvec _ _ fun c => honc (.sigma i c),
    fun i => hvec _ _ fun c => honc (.coeff i c), hvec _ _ fun c => honc (.generic c),
    hvec _ _ fun c => honc (.poseidon c), hvec _ _ fun c => honc (.completeAdd c),
    hvec _ _ fun c => honc (.mul c), hvec _ _ fun c => honc (.emul c),
    hvec _ _ fun c => honc (.endomulScalar c)⟩
  -- the absorbed coordinates are the key's (`KeyReads.indexCoords`)
  refine ⟨⟨_, hsv, ?_⟩, hkey⟩
  rw [hkey.indexCoords, E.digest_eq]
  rfl

end KeyRead

/-! ## The wrap circuit's read -/

section MainReads

open Std.Do CompElliptic.Fields.Pasta Bulletproof Bulletproof.Ipa Kimchi.Verifier

/-- **The wrap circuit's finalize read.** Under any valuation satisfying the emitted constraints,
the branch index names a branch `b`: the statement's branch data reads as
`4·log2s[b] + Σᵢ 2^(1−i)·[i < widths[b]]`, and every slot branch `b` compiled for the key's wrap
domain (index `j`) whose `shouldFinalize` is set reads as its scalar half. -/
theorem wrapMainHead_reads {branches mpv nc : ℕ} [NeZero branches] (E : Env IpaPallas.curve 1)
    (Vs : Valuation Fq)
    (gen : ℕ → Fq) (widths log2s : List ℕ)
    (stepKeys : Vector (VkComms nc (AffinePoint (FVar Fq))) branches)
    (pins : Vector (Vector (Option ℕ) branches) mpv) (dummy : List Fq)
    (slotWidths : Vector ℕ mpv) (adv : WrapMainAdvice mpv nc E.σ.k slotWidths.toList.sum)
    (branchData : FVar Fq)
    (hwl : widths.length = branches) (hll : log2s.length = branches) (hw : ∀ w ∈ widths, w ≤ mpv)
    (hmpv : mpv ≤ MaxProofsVerified) (hbr : branches ≤ PALLAS_SCALAR_CARD)
    (j : ℕ) (hdom : wrapDomainLog2s[j]? = some E.cvk.domainLog2)
    (hgen : gen E.cvk.domainLog2 = E.cvk.omega) :
    ⦃⌜True⌝⦄
    wrapMainHead (c := Builder Vs (KimchiConstraint Fq)) (FopParams.ofEnv E Linearization.fqTokens)
      gen widths log2s stepKeys pins dummy slotWidths adv branchData
    ⦃⇓ hd _ => ⌜∃ (b : ℕ) (hb : b < branches), hd.whichBranch.val Vs = (b : Fq) ∧
      branchData.val Vs = 4 * (log2s[b]'(by omega) : Fq)
        + ((List.range mpv).map fun i =>
            ((2 ^ (1 - i) : ℕ) : Fq) * bit (decide (i < widths[b]'(by omega)))).sum ∧
      ∀ i : Fin mpv, hd.slots[i].pins[(⟨b, hb⟩ : Fin branches)] = some j →
        (↑hd.slots[i].unfinalized.shouldFinalize : CVar Fq).val Vs = 1 →
        hd.slots[i].ScalarReads E Vs⌝⦄ := by
  -- branch indices and slot counts are below the field's characteristic
  have hcast := CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
  have hinjB : ∀ a a' : ℕ, a < branches → a' < branches → (a : Fq) = a' → a = a' :=
    fun a a' ha ha' => hcast (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega))
  have hmax : MaxProofsVerified < PALLAS_SCALAR_CARD := by
    norm_num [MaxProofsVerified, PALLAS_SCALAR_CARD]
  have hinj : ∀ a a' : ℕ, a ≤ mpv → a' ≤ mpv → (a : Fq) = a' → a = a' :=
    fun a a' ha ha' => hcast (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega))
  simp only [wrapMainHead]
  have hbb := fun wb => wrapBranchBlock_spec (V := Vs) (c := KimchiConstraint Fq) branches mpv
    widths log2s wb branchData hwl hll hw hinjB hinj
  have hck := fun bs => builder_spec_true (V := Vs) (c := KimchiConstraint Fq)
    (chooseKey bs stepKeys)
  have hfin := fun bs (sl : Vector (WrapFinalizeSlot branches E.σ.k 1 Fq) mpv) =>
    builder_spec_forall _ (fun b : Fin branches =>
      CircuitType.Reads Vs bs (Vector.ofFn fun l => decide (l = b))) _
      fun b hbits => wrapFinalizePrevProofs_reads E Vs gen bs sl b j hbits hdom hgen
  mvcgen [hbb, hck, hfin]
  rename_i bits _ hbb' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfin'
  obtain ⟨b, hb, hwb, hbits, -, hbd⟩ := hbb'
  refine ⟨b, hb, hwb, hbd, hfin' ⟨b, hb⟩ ?_⟩
  -- the bits vector reads as `b`'s one-hot vector
  have hlen : bits.1.length = branches := by simpa using congrArg List.length hbits
  refine CircuitType.reads_vector.mpr fun l hl => CircuitType.reads_boolVar.mpr ?_
  have hl' : l < bits.1.length := by omega
  have h := congrArg (fun xs => xs[l]?) hbits
  simp only [List.getElem?_map, List.getElem?_eq_getElem hl', List.getElem?_range hl,
    Option.map_some, Option.some.injEq] at h
  simp only [Vector.getElem_ofFn, List.getD_eq_getElem _ _ hl', h, bit, Fin.mk.injEq]
  by_cases hlb : l = b <;> simp [hlb]

/-- **The wrap circuit's finalize read**, over the whole circuit: `wrapMainHead_reads` at the
statement's branch data (cell `29`). -/
theorem wrapMain_reads {branches mpv nc : ℕ} [NeZero branches] (E : Env IpaPallas.curve 1)
    (Vs : Valuation Fq)
    (gen : ℕ → Fq) (widths log2s : List ℕ)
    (stepKeys : Vector (VkComms nc (AffinePoint (FVar Fq))) branches)
    (pins : Vector (Vector (Option ℕ) branches) mpv)
    (lagrange : ℕ → List (Vector IpaVesta.curve.Point nc)) (h : IpaVesta.curve.Point)
    (dummy : List Fq) (slotWidths : Vector ℕ mpv)
    (adv : WrapMainAdvice mpv nc E.σ.k slotWidths.toList.sum) (stmt : Vector (FVar Fq) 40)
    (hwl : widths.length = branches) (hll : log2s.length = branches) (hw : ∀ w ∈ widths, w ≤ mpv)
    (hmpv : mpv ≤ MaxProofsVerified) (hbr : branches ≤ PALLAS_SCALAR_CARD)
    (j : ℕ) (hdom : wrapDomainLog2s[j]? = some E.cvk.domainLog2)
    (hgen : gen E.cvk.domainLog2 = E.cvk.omega) :
    ⦃⌜True⌝⦄
    wrapMain (c := Builder Vs (KimchiConstraint Fq)) (FopParams.ofEnv E Linearization.fqTokens)
      gen widths log2s stepKeys pins lagrange h dummy slotWidths adv stmt
    ⦃⇓ hd _ => ⌜∃ (b : ℕ) (hb : b < branches), hd.whichBranch.val Vs = (b : Fq) ∧
      (stmt[29]?.getD (CVar.const 0)).val Vs = 4 * (log2s[b]'(by omega) : Fq)
        + ((List.range mpv).map fun i =>
            ((2 ^ (1 - i) : ℕ) : Fq) * bit (decide (i < widths[b]'(by omega)))).sum ∧
      ∀ i : Fin mpv, hd.slots[i].pins[(⟨b, hb⟩ : Fin branches)] = some j →
        (↑hd.slots[i].unfinalized.shouldFinalize : CVar Fq).val Vs = 1 →
        hd.slots[i].ScalarReads E Vs⌝⦄ := by
  simp only [wrapMain]
  have hh := wrapMainHead_reads E Vs gen widths log2s stepKeys pins dummy slotWidths adv
    (stmt[29]?.getD (CVar.const 0)) hwl hll hw hmpv hbr j hdom hgen
  have ht := fun hd : WrapMainHead branches mpv nc E.σ.k => builder_spec_true (V := Vs)
    (c := KimchiConstraint Fq)
    (wrapMainTail log2s lagrange h dummy slotWidths adv stmt hd)
  mvcgen [hh, ht]

end MainReads

end Pickles
