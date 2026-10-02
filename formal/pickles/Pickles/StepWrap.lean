import Pickles.StepMain
import Pickles.WrapMain
import Pickles.KeyLayout

set_option mvcgen.warning false

/-!
# Every must-verify slot's wrap proof verifies

A step circuit verifies up to `MaxProofsVerified` previous wrap proofs, each across two circuits:
the step circuit checks its group half, and the next wrap circuit's finalize block checks its
scalar half. This module joins the two reads. For any rule, under a valuation satisfying the step
circuit's constraints and one satisfying the wrap circuit's (`wrapMain`), the cells of every slot
the rule marks must-verify hold a wrap proof that `kimchiVerify` accepts.

## Main results

* `stepWrap_kimchiVerify`: the two circuits' runs, each satisfied under its own valuation, with
  the step circuit's output read as the wrap circuit's public input, give each must-verify slot
  whose key cells read as a key its source fits, and whose pin is at that key's wrap domain, a
  wrap proof its cells hold, which `kimchiVerify` accepts at that key.
* `StepStatement.ofWrap_toFields`: the tie's statement, flattened, is the public input
  `wrapPublicInput` commits to.

## Implementation notes

The wrap circuit has one slot per proof the tag verifies, `w`, front-padded: step slot `i` is
wrap slot `i + (w − n)`. A slot's wrap proof carries its source's width of accumulators
(`SlotSource.width`), the wrap circuit is compiled with any challenge-stack height per slot, and
both circuits pad the accumulators to `MaxProofsVerified` alike. The wrap circuit finalizes
every slot with its own tag's constants, which name no key: the curve, the chunk count and the
SRS size fix them (`FopParams.of`). The wrap proofs are at one chunk, the chunk count the wrap
circuit allocates their evaluations at. The step circuit sets `shouldFinalize` on every
must-verify slot, and the tie carries that bit to the finalize block, where it forces the slot
to finalize.

The public-input tie says the step circuit's output reads as `StepStatement.ofWrap`: the statement
the wrap circuit's `Fq` cells hold, each cell taken to the `Fp` scalar its x_hat ladder applies
(the ladder's integer, reduced by the group's order `p`). The ladder bounds every packed cell
below `2^254 < p` (`PackedScalar.Bound`), so no cell wraps and the tie fixes each slot's claims
(`SplitClaimsCast`) and its `shouldFinalize` bit.

The wrap proof is read off the cells of both circuits (`slotProof`): its commitments and opening
from the step circuit's, which the slot check puts on the curve, its evaluations and old
challenges from the next wrap circuit's finalize cells.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-- A bounded cell is the lift of its own public-input entry: reducing into the step field and
lifting back is the identity below `2^254 < p`. -/
private theorem cell_eq_redFq {Vs : Valuation Fq} {k : PackedScalar Fq} (hb : k.Bound Vs) :
    k.cell.val Vs = redFq (PackedScalar.reduced IpaVesta.curve Vs k) := by
  have hN := PackedScalar.val_lt_of_bound hb
  have hp : (2 : ℕ) ^ 254 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  have hr : PackedScalar.reduced IpaVesta.curve Vs k
      = ((ZMod.val (k.cell.val Vs) : ℕ) : Fp) := by
    cases k <;> rfl
  rw [hr, redFq, ZMod.val_natCast_of_lt (hN.trans hp), ZMod.natCast_zmod_val]

/-- An unfinalized entry the wrap circuit's cells hold, as the step circuit's values: each cell
the scalar its x_hat ladder applies (`PackedScalar.reduced`), a bit `true` when it reads `1`. -/
def UnfVal.ofWrap {k : ℕ} (Vs : Valuation Fq)
    (u : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) :
    UnfVal k :=
  let r (x : FVar Fq) : Fp := PackedScalar.reduced IpaVesta.curve Vs (.full x)
  let bb (b : BoolVar Fq) : Bool := decide ((↑b : CVar Fq).val Vs = 1)
  let s (x : Type2 (SplitField (FVar Fq) (BoolVar Fq))) : Type2 (SplitField Fp Bool) :=
    ⟨⟨r x.val.sDiv2, bb x.val.sOdd⟩⟩
  let dv := u.deferredValues
  let pl := dv.plonk
  ⟨s dv.combinedInnerProduct, s dv.b, s pl.zetaToSrsLength, s pl.zetaToDomainSize, s pl.perm,
    r u.spongeDigestBeforeEvaluations, r pl.beta.val, r pl.gamma.val, r pl.alpha.val,
    r pl.zeta.val, r dv.xi.val, dv.bulletproofChallenges.map (r ·.val), bb u.shouldFinalize⟩

/-- The step statement the wrap circuit's cells hold, as the step circuit's values
(`UnfVal.ofWrap` entry by entry). -/
def StepStatement.ofWrap {k w : ℕ} (Vs : Valuation Fq)
    (st : StepStatement (UnfinalizedProof k (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) (FVar Fq) w) :
    StepStatement (UnfVal k) Fp w :=
  ⟨⟨st.proofState.unfinalizedProofs.map (UnfVal.ofWrap Vs),
    PackedScalar.reduced IpaVesta.curve Vs (.full st.proofState.messagesForNextStepProof)⟩,
    st.messagesForNextWrapProof.map fun m => PackedScalar.reduced IpaVesta.curve Vs (.full m)⟩

/-- A boolean bit cell's step bit encodes as the scalar its ladder applies. -/
private theorem bit_ofWrap {Vs : Valuation Fq} {b : BoolVar Fq}
    (hb : (PackedScalar.bit b).Bound Vs) :
    (bit (decide ((↑b : CVar Fq).val Vs = 1)) : Fp)
      = PackedScalar.reduced IpaVesta.curve Vs (.bit b) := by
  obtain ⟨bb, hbb⟩ := hb
  show _ = ((ToNat.toNat ((↑b : CVar Fq).val Vs) : ℕ) : Fp)
  rw [hbb]
  cases bb
  · simp [bit, ToNat.toNat]
  · simp only [bit, ToNat.toNat, decide_true, if_true]
    rw [ZMod.val_one, Nat.cast_one]

/-- An unfinalized entry's values, flattened, are its packed scalars reduced, when its bit cells
read as bits. -/
private theorem UnfVal.ofWrap_toFields {k : ℕ} {Vs : Valuation Fq}
    (u : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (hbnd : ∀ x ∈ u.packed, x.Bound Vs) :
    (CircuitType.valueToFields (F := Fp) (var := UnfVar k) (UnfVal.ofWrap Vs u)).toList
      = u.packed.toList.map (PackedScalar.reduced IpaVesta.curve Vs) := by
  have hbit : ∀ b : BoolVar Fq, PackedScalar.bit b ∈ u.packed →
      (bit (decide ((↑b : CVar Fq).val Vs = 1)) : Fp)
        = PackedScalar.reduced IpaVesta.curve Vs (.bit b) :=
    fun b hm => bit_ofWrap (hbnd _ hm)
  have h1 : ∀ x : Fp, CircuitType.valueToFields (F := Fp) (var := FVar Fp) x = #v[x] :=
    fun _ => rfl
  have h2 : ∀ b : Bool, CircuitType.valueToFields (F := Fp) (var := BoolVar Fp) b = #v[bit b] :=
    fun _ => rfl
  -- the parity bits and the finalize flag
  have e1 := hbit u.deferredValues.combinedInnerProduct.val.sOdd
    (by simp [UnfinalizedProof.packed])
  have e2 := hbit u.deferredValues.b.val.sOdd (by simp [UnfinalizedProof.packed])
  have e3 := hbit u.deferredValues.plonk.zetaToSrsLength.val.sOdd
    (by simp [UnfinalizedProof.packed])
  have e4 := hbit u.deferredValues.plonk.zetaToDomainSize.val.sOdd
    (by simp [UnfinalizedProof.packed])
  have e5 := hbit u.deferredValues.plonk.perm.val.sOdd (by simp [UnfinalizedProof.packed])
  have e6 := hbit u.shouldFinalize (by simp [UnfinalizedProof.packed])
  simp only [CircuitType.toList_valueToFields_ofEquiv, UnfVal.ofWrap, AllocUnfinalized.equivProd,
    Type2.equivVal, SplitField.equivProd, Equiv.coe_fn_mk, CircuitType.valueToFields_prod,
    CircuitType.valueToFields_vector, Vector.toList_append, h1, h2, e1, e2, e3, e4, e5, e6,
    mapVec_eq_map, Vector.map_map, Function.comp_def]
  rw [toList_flatten_singletons]
  simp [UnfinalizedProof.packed, PackedScalar.reduced, PackedScalar.cell]

/-- **The tie's statement is the wire's public input.** Flattened, `StepStatement.ofWrap` is the
public input `wrapPublicInput` commits to, when the ladders bound every packed cell
(`wrapMain_statement`). -/
theorem StepStatement.ofWrap_toFields {ks n nc : ℕ} (σ : SRS IpaVesta.curve.Point)
    (cvk : KimchiVK IpaVesta.curve nc) (Vs : Valuation Fq)
    (st : StepStatement (UnfinalizedProof ks (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) (FVar Fq) n)
    (hbnd : ∀ x ∈ st.packed, x.Bound Vs) :
    (CircuitType.valueToFields (F := Fp) (var := StepStatement (UnfVar ks) (FVar Fp) n)
      (StepStatement.ofWrap Vs st)).toList
      = (wrapPublicInput σ cvk Vs st).toList := by
  rw [wrapPublicInput_toList σ cvk Vs st]
  have h1 : ∀ x : Fp, CircuitType.valueToFields (F := Fp) (var := FVar Fp) x = #v[x] :=
    fun _ => rfl
  rw [StepStatement.toList_valueToFields]
  simp only [StepStatement.ofWrap, CircuitType.valueToFields_prod, CircuitType.valueToFields_vector,
    Vector.toList_append, StepStatement.packed, Vector.toList_mk, List.map_append, h1,
    mapVec_eq_map, Vector.map_map, Function.comp_def]
  rw [toList_flatten_singletons st.messagesForNextWrapProof
    fun x => PackedScalar.reduced IpaVesta.curve Vs (.full x)]
  -- each slot's values, flattened, are its packed scalars reduced
  have hs : (st.proofState.unfinalizedProofs.map fun u => CircuitType.valueToFields (F := Fp)
        (var := UnfVar ks) (UnfVal.ofWrap Vs u)).flatten.toList
      = (st.proofState.unfinalizedProofs.toList.flatMap fun u => u.packed.toList).map
        (PackedScalar.reduced IpaVesta.curve Vs) := by
    simp only [toList_flatten', Vector.toList_map, List.map_map, Function.comp_def, List.flatMap,
      List.map_flatten]
    refine congrArg List.flatten (List.map_congr_left fun u hu =>
      UnfVal.ofWrap_toFields u fun x hx => hbnd x ?_)
    simp only [StepStatement.packed, Vector.mem_mk, List.mem_toArray, List.mem_append,
      List.mem_flatMap]
    exact Or.inl (Or.inl ⟨u, hu, Vector.mem_toList_iff.mpr hx⟩)
  rw [hs]
  simp

open Snarky.Kimchi in
/-- One slot across the tie: its cells, read, are the wrap statement's slot reduced, and the wrap
side's ladders bound that slot; then the wrap circuit's claims hold the step circuit's lifted
(`SplitClaimsCast`) and both read one `shouldFinalize` bit. -/
private theorem slot_cast {k : ℕ} {Vg : Valuation Fp} {Vs : Valuation Fq} (u : UnfVar k)
    (sp : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (a : AllocUnfinalized k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (hu : CircuitType.Reads Vg u (UnfVal.ofWrap Vs sp))
    (hbnd : ∀ x ∈ sp.packed, x.Bound Vs)
    (hsr : SplitClaimsRead Vs a.toUnfinalized sp) :
    SplitClaimsCast Vg u.toUnfinalized Vs a.toUnfinalized ∧
      ∃ bb : Bool, CircuitType.Reads Vg u.toUnfinalized.shouldFinalize bb ∧
        CircuitType.Reads Vs a.toUnfinalized.shouldFinalize bb := by
  -- each wrap entry is the lift of the step cell it is read against
  have hB : ∀ x ∈ sp.packed, x.cell.val Vs = redFq (PackedScalar.reduced IpaVesta.curve Vs x) :=
    fun x hx => cell_eq_redFq (hbnd x hx)
  -- the entry's cells, field by field
  simp only [UnfVal.ofWrap, CircuitType.reads_ofEquiv, AllocUnfinalized.equivProd,
    Type2.equivVal, SplitField.equivProd, Equiv.coe_fn_mk, CircuitType.reads_prod,
    CircuitType.reads_fvar, CircuitType.reads_boolVar] at hu
  obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩, ⟨c5, c6⟩, ⟨c7, c8⟩, ⟨c9, c10⟩, c11, c12, c13, c14, c15, c16, hbpR,
    hsf⟩ := hu
  -- a parity bit's step bit is the scalar its ladder applies
  rw [bit_ofWrap (hbnd _ (by simp [UnfinalizedProof.packed]))] at c2 c4 c6 c8 c10
  have mem : ∀ x, x ∈ sp.packed ↔ x ∈ UnfinalizedProof.packed sp := fun _ => Iff.rfl
  obtain ⟨ha, hbe, hg, hz, hxi, hbps, hsfe, hdig, hscip, hsb, hsperm, hszm, hszn⟩ := hsr
  -- an entry of the slot, read against the step cell `v`, is `v` lifted
  have e : ∀ {x : PackedScalar Fq} {v : Fp}, x ∈ UnfinalizedProof.packed sp →
      v = PackedScalar.reduced IpaVesta.curve Vs x → x.cell.val Vs = redFq v :=
    fun hx hv => (hB _ hx).trans (by rw [hv])
  have mem : ∀ {x : PackedScalar Fq}, x ∈ UnfinalizedProof.packed sp ↔ x ∈ sp.packed :=
    Iff.rfl
  -- the scalar claims and the digest
  have fa : a.alpha.val Vs = redFq (u.alpha.val Vg) := by
    have := e (x := .b128 sp.deferredValues.plonk.alpha.val) (by simp [UnfinalizedProof.packed]) c14
    simpa [PackedScalar.cell, ha, AllocUnfinalized.toUnfinalized] using this
  have fb : a.beta.val Vs = redFq (u.beta.val Vg) := by
    have := e (x := .b128 sp.deferredValues.plonk.beta.val) (by simp [UnfinalizedProof.packed]) c12
    simpa [PackedScalar.cell, hbe, AllocUnfinalized.toUnfinalized] using this
  have fg : a.gamma.val Vs = redFq (u.gamma.val Vg) := by
    have := e (x := .b128 sp.deferredValues.plonk.gamma.val) (by simp [UnfinalizedProof.packed])
      c13
    simpa [PackedScalar.cell, hg, AllocUnfinalized.toUnfinalized] using this
  have fz : a.zeta.val Vs = redFq (u.zeta.val Vg) := by
    have := e (x := .b128 sp.deferredValues.plonk.zeta.val) (by simp [UnfinalizedProof.packed]) c15
    simpa [PackedScalar.cell, hz, AllocUnfinalized.toUnfinalized] using this
  have fxi : a.xi.val Vs = redFq (u.xi.val Vg) := by
    have := e (x := .b128 sp.deferredValues.xi.val) (by simp [UnfinalizedProof.packed]) c16
    simpa [PackedScalar.cell, hxi, AllocUnfinalized.toUnfinalized] using this
  have fd : a.spongeDigest.val Vs = redFq (u.spongeDigest.val Vg) := by
    have := e (x := .full sp.spongeDigestBeforeEvaluations) (by simp [UnfinalizedProof.packed]) c11
    simpa [PackedScalar.cell, hdig, AllocUnfinalized.toUnfinalized] using this
  -- a split claim joins its lifted half and parity
  have join : ∀ (w : Type2 (FVar Fq)) (s : Type2 (SplitField (FVar Fq) (BoolVar Fq)))
      (x : Type2 (SplitField (FVar Fp) (BoolVar Fp))), SplitReads Vs w s →
      (PackedScalar.full s.val.sDiv2).cell.val Vs = redFq (x.val.sDiv2.val Vg) →
      (PackedScalar.bit s.val.sOdd).cell.val Vs = redFq ((↑x.val.sOdd : CVar Fp).val Vg) →
      w.val.val Vs = 2 * redFq (x.val.sDiv2.val Vg) + redFq ((↑x.val.sOdd : CVar Fp).val Vg) := by
    intro w s x ⟨bb, hbb, hw⟩ hh ho
    simp only [PackedScalar.cell] at hh ho
    rw [hw, hh, ← hbb, ho]
  have pm := fun (x : PackedScalar Fq) (h : x ∈ UnfinalizedProof.packed sp) => h
  have fcip := join _ _ u.cip hscip (e (by simp [UnfinalizedProof.packed]) c1)
    (e (by simp [UnfinalizedProof.packed]) c2)
  have fbb := join _ _ u.b hsb (e (by simp [UnfinalizedProof.packed]) c3)
    (e (by simp [UnfinalizedProof.packed]) c4)
  have fzm := join _ _ u.zetaToSrsLength hszm (e (by simp [UnfinalizedProof.packed]) c5)
    (e (by simp [UnfinalizedProof.packed]) c6)
  have fzn := join _ _ u.zetaToDomainSize hszn (e (by simp [UnfinalizedProof.packed]) c7)
    (e (by simp [UnfinalizedProof.packed]) c8)
  have fperm := join _ _ u.perm hsperm (e (by simp [UnfinalizedProof.packed]) c9)
    (e (by simp [UnfinalizedProof.packed]) c10)
  -- the round challenges, entrywise
  have fbp : ∀ i : Fin k, a.bulletproofChallenges[i].val Vs
      = redFq (u.bulletproofChallenges[i].val Vg) := by
    intro i
    have hl := CircuitType.reads_fvar.mp (CircuitType.reads_vector.mp hbpR i i.isLt)
    have hs := hB (.b128 sp.deferredValues.bulletproofChallenges[i].val) (by
      simp only [UnfinalizedProof.packed, Vector.mem_mk, List.mem_toArray, List.mem_append,
        List.mem_cons, List.mem_map, PackedScalar.b128.injEq]
      exact Or.inl (Or.inr ⟨_, by simp, rfl⟩))
    have ha := congrArg (·[i].val.val Vs) hbps
    simp only [AllocUnfinalized.toUnfinalized, Vector.getElem_map, Fin.getElem_fin] at ha hl
    simp only [PackedScalar.cell, Fin.getElem_fin, ha] at hs ⊢
    rw [hs, hl]
    rfl
  -- the finalize flag: a bit on the wrap side, so the same bit on the step side
  have fsf : ∃ bb : Bool, CircuitType.Reads Vg u.shouldFinalize bb ∧
      CircuitType.Reads Vs a.shouldFinalize bb := by
    obtain ⟨bb, hbb⟩ := hbnd (.bit sp.shouldFinalize) (by simp [UnfinalizedProof.packed])
    refine ⟨bb, CircuitType.reads_boolVar.mpr ?_, CircuitType.reads_boolVar.mpr ?_⟩
    · rw [hsf, hbb]
      cases bb <;> simp [bit]
    · rw [← show sp.shouldFinalize = a.shouldFinalize from hsfe]
      exact hbb
  refine ⟨?_, fsf⟩
  simp only [SplitClaimsCast, AllocUnfinalized.toUnfinalized, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at fcip fbb fzm fzn fperm ⊢
  exact ⟨⟨fa, fb, fg, fz, fxi, fd⟩, ⟨fperm, fzm, fzn, fcip, fbb⟩, by
    simpa [Vector.getElem_map] using fbp⟩

/-- A bit that reads as `true` on one side of a tie reads as `true` on the other. -/
private theorem reads_true_of_tie {Vg : Valuation Fp} {Vs : Valuation Fq} {a : BoolVar Fp}
    {a' : BoolVar Fq} (ht : ∃ bb : Bool, CircuitType.Reads Vg a bb ∧ CircuitType.Reads Vs a' bb)
    (hG : CircuitType.Reads Vg a true) : (↑a' : CVar Fq).val Vs = 1 := by
  obtain ⟨bb, hGb, hSb⟩ := ht
  rw [CircuitType.reads_boolVar] at hG hGb hSb
  have : bb = true := by
    cases bb
    · rw [hG] at hGb
      simp [bit] at hGb
    · rfl
  subst this
  simpa [bit] using hSb

/-! ## The wrap proof a slot's cells hold -/

open CompElliptic.CurveForms.ShortWeierstrass in
/-- A checked point's post is Pallas's curve equation. -/
private theorem pallas_onCurve {V : Valuation Fp} {p : AffinePoint (FVar Fp)}
    (h : p.y.val V * p.y.val V = p.x.val V ^ 3 + 0 * p.x.val V + 5) :
    OnCurve IpaPallas.curve.E.A IpaPallas.curve.E.B (p.x.val V, p.y.val V) := by
  simp only [OnCurve, IpaPallas.curve, CompElliptic.Curves.Pasta.Pallas.curve,
    CompElliptic.Curves.Pasta.Pallas.a, CompElliptic.Curves.Pasta.Pallas.b]
  linear_combination h

/-- The wrap proof a slot's cells hold: its commitments and opening from the step circuit's
cells (`IvpProof.read`), its evaluations and old challenges from the next wrap circuit's. -/
private def slotProof {s ks k ncs w : ℕ} (Vg : Valuation Fp) (Vs : Valuation Fq)
    (inp : VerifyOneInput s ks k 1 ncs w) (evals : ChunkedEvals 1 (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) k) MaxProofsVerified) :
    KimchiProof IpaPallas.curve 1 k :=
  inp.proof.read (stepSide Vg) (evals.evals.map fun v => v.map (·.val Vs))
    (.carried (evals.pub.map fun v => v.map (·.val Vs))) (evals.ftEval1.val Vs)
    (inp.sgOld.zipWith (fun P u => ⟨readPt (C := IpaPallas.curve) Vg P, u.map (·.val Vs)⟩)
      prevChallenges).toArray

/-- The accumulator a step circuit and the next wrap circuit emit for the wrap proof they
verify: the step message's commitment at slot `i`, with the wrap message's challenges at `jf`. -/
def StepWrap.emittedAccumulator {n w sa ncw ncs k ks branches mpv ncStep kw ks' : ℕ}
    {ws ss : Fin n → ℕ} {slotWidths : Vector (Fin (MaxProofsVerified + 1)) mpv}
    (Vg : Valuation Fp) (Vs : Valuation Fq) (i : Fin n) (jf : Fin mpv)
    (stepOut : StepMainOut n w ws ss sa ncw ncs k ks)
    (verifyOut : WrapMainVerifyOut mpv ncStep kw ks')
    (finalizeOut : WrapMainFinalizeOut branches mpv ncStep kw slotWidths) :
    Accumulator IpaPallas.curve kw :=
  Accumulator.ofCells Vg Vs stepOut.messagesForNextStepProof.challengePolynomialCommitments[i]
    (verifyOut.messagesForNextWrapProof finalizeOut).oldBulletproofChallenges[jf]

/-- The accumulators a step circuit and the next wrap circuit consume: the step slot's
old-accumulator cells, with the challenges of the wrap message rebuilt for slot `jf`, both padded
(the challenges with `dummy`). -/
def StepWrap.consumedAccumulators {s ks k ncw ncs w branches mpv ncStep kw : ℕ}
    {slotWidths : Vector (Fin (MaxProofsVerified + 1)) mpv}
    (Vg : Valuation Fp) (Vs : Valuation Fq) (inp : VerifyOneInput s ks k ncw ncs w)
    (dummy : Vector Fq kw) (finalizeOut : WrapMainFinalizeOut branches mpv ncStep kw slotWidths)
    (jf : Fin mpv) : List (Accumulator IpaPallas.curve kw) :=
  (Vector.zipWith (Accumulator.ofCells Vg Vs) inp.sgOld
    (padChallenges dummy (finalizeOut.messagesForNextWrapProof jf).oldBulletproofChallenges
      (Nat.lt_succ_iff.mp slotWidths[jf].isLt))).toList

open CompElliptic.CurveForms.ShortWeierstrass in
/-- With its cells on the curve, the step circuit's `sgOld` cells hold `slotProof`'s old
commitments. -/
private theorem slotProof_olds {s ks k ncs w : ℕ} {Vg : Valuation Fp} {Vs : Valuation Fq}
    {inp : VerifyOneInput s ks k 1 ncs w} {evals : ChunkedEvals 1 (FVar Fq)}
    {prevChallenges : Vector (Vector (FVar Fq) k) MaxProofsVerified}
    (hon : ∀ p ∈ inp.sgOld.toList,
      OnCurve IpaPallas.curve.E.A IpaPallas.curve.E.B (p.x.val Vg, p.y.val Vg)) :
    CommReads IpaPallas.curve Vg inp.sgOld.toList
      ((slotProof Vg Vs inp evals prevChallenges).olds.map (·.sg)).toList := by
  have h : ((slotProof Vg Vs inp evals prevChallenges).olds.map (·.sg)).toList
      = inp.sgOld.toList.map (readPt (C := IpaPallas.curve) Vg) := by
    refine List.ext_getElem (by simp [slotProof, IvpProof.read]) fun j h₁ h₂ => ?_
    simp [slotProof, IvpProof.read]
  rw [h]
  exact commReads_readPt hon

open CompElliptic.CurveForms.ShortWeierstrass in
/-- A slot's checked point cells, and the constant padding cells, lie on the curve. -/
private theorem slotInput_onCurve {sp w ncs k ks : ℕ} {V : Valuation Fp}
    (hw : w ≤ MaxProofsVerified) {dummySg : IpaPallas.curve.Point} (hd : dummySg ≠ 0)
    (prev : PrevStatement sp) {s : SlotVar w 1 ncs k ks} (u : UnfVar k) (msg : FVar Fp)
    (hs : SlotWitness.PointsOnCurve V s) :
    let inp := slotInput hw (constPt dummySg) prev s u msg
    (∀ p ∈ inp.proof.points,
      OnCurve IpaPallas.curve.E.A IpaPallas.curve.E.B (p.x.val V, p.y.val V)) ∧
    ∀ p ∈ inp.sgOld.toList,
      OnCurve IpaPallas.curve.E.A IpaPallas.curve.E.B (p.x.val V, p.y.val V) := by
  obtain ⟨⟨hwc, hz, ht, hlr, -, -, hdl, hsg⟩, hprev⟩ := hs
  have hdum : OnCurve IpaPallas.curve.E.A IpaPallas.curve.E.B
      ((constPt dummySg).x.val V, (constPt dummySg).y.val V) := by
    simpa [constPt, CVar.val] using SWPoint.onCurve_of_ne_zero hd
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp [slotInput, IvpProof.points] at hp
    rcases hp with ⟨col, hcol, q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | hp | hp | rfl | rfl
    · exact pallas_onCurve
        (hwc col (Vector.mem_toList_iff.mpr hcol) q (Vector.mem_toList_iff.mpr hq))
    · exact pallas_onCurve (hz q (Vector.mem_toList_iff.mpr hq))
    · obtain ⟨col, hcol, hp⟩ := Vector.mem_flatten.mp hp
      obtain ⟨col, hcol', rfl⟩ := Vector.mem_map.mp hcol
      obtain ⟨q, hq, rfl⟩ := Vector.mem_map.mp hp
      exact pallas_onCurve
        (ht col (Vector.mem_toList_iff.mpr hcol') q (Vector.mem_toList_iff.mpr hq))
    · obtain ⟨a, b, hab, rfl | rfl⟩ := hp
      · exact pallas_onCurve (hlr _ (Vector.mem_toList_iff.mpr hab)).1
      · exact pallas_onCurve (hlr _ (Vector.mem_toList_iff.mpr hab)).2
    · exact pallas_onCurve hdl
    · exact pallas_onCurve hsg
  · simp [slotInput] at hp
    rcases hp with ⟨-, rfl⟩ | ⟨q, hq, rfl⟩
    · exact hdum
    · exact pallas_onCurve (hprev q (Vector.mem_toList_iff.mpr hq))

/-- The next wrap circuit's finalize cells hold `slotProof`'s evaluations and old challenges. -/
private theorem slotProof_fopTies {s ks ncs w : ℕ} {Vg : Valuation Fp} {Vs : Valuation Fq}
    (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve 1)
    {inp : VerifyOneInput s ks σ.k 1 ncs w}
    (claims : UnfinalizedProof σ.k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : ChunkedEvals 1 (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) σ.k) MaxProofsVerified) (pub : Array Fq) :
    FopTies σ cvk (slotProof Vg Vs inp evals prevChallenges) pub
      (ScalarHalf.wrap Vs claims evals prevChallenges) := by
  refine ⟨(ScalarHalf.wrap_olds Vs claims evals prevChallenges _).mpr ?_, rfl, rfl, rfl⟩
  refine List.ext_getElem (by simp [slotProof, IvpProof.read, ScalarHalf.prevVals,
    ScalarHalf.wrap]) fun j h₁ h₂ => ?_
  simp [slotProof, IvpProof.read, ScalarHalf.prevVals, ScalarHalf.wrap]

/-- **Every must-verify slot's wrap proof verifies.** Let `Vg` satisfy the step circuit of any
rule, its slots from any sources, and `Vs` the next wrap circuit, with its branch index reading
as branch `b`. When the step circuit's output reads as the wrap circuit's public input, every
must-verify slot whose key cells read as a key `K` its source fits, and whose wrap slot was
compiled for `K`'s domain, holds a wrap proof in its cells; the next wrap circuit's finalize
cells hold that proof's evaluations and old challenges, and `kimchiVerify` accepts it at `K`
under `SgOk`, with its guards derived from `WrapKeyLayout`. -/
theorem stepWrap_kimchiVerify
    -- the rule's `n` slots; the tag's `w`, the accumulators each of its wrap proofs carries,
    -- a self slot's width and the wrap circuit's slots; the step proofs the wrap proofs
    -- verified at `ncPrevStep`; the wrap circuit's `branches`, the step proof it verifies at
    -- `ncStep` chunks
    {n w ncPrevStep branches ncStep : ℕ}
    [NeZero branches]
    -- the rule's input and output, as values and as cells
    {inVal inVar outVal outVar : Type}
    [CircuitType Fp inVal inVar] [CircuitType Fp outVal outVar]
    -- each slot's previous statement's cell count
    {ss : Fin n → ℕ}
    -- the wrap SRS the slots share
    (S : Srs IpaPallas.curve)
    -- the wrap SRS has the deployed size, `2 ^ WrapIPARounds` points
    (hE : S.σ.k = WrapIPARounds)
    -- the step circuit's finalize constants
    (P : FopParams Fp)
    -- the step domains the step circuit's finalize dispatches over
    (domains : List (KnownDomain Fp))
    -- the rule verifies at most the tag's `w` slots
    (hn : n ≤ w)
    -- the tag verifies at most `MaxProofsVerified`
    (hw : w ≤ MaxProofsVerified)
    -- the `sg` padding the missing accumulators
    (dummySg : IpaPallas.curve.Point)
    -- off the identity, so its constant cells lie on the curve
    (hdummySg : dummySg ≠ 0)
    -- the unfinalized entry padding the step statement to the tag's `w` slots
    (dummyUnf : UnfVal S.σ.k)
    -- each slot's source: a proof of this system, or of another compiled one
    (srcs : Fin n → SlotSource 1 StepIPARounds)
    -- each slot verifies at most `MaxProofsVerified` accumulators
    (hws : ∀ i, SlotSource.widths w srcs i ≤ MaxProofsVerified)
    -- the step circuit's valuation
    (Vg : Valuation Fp)
    [CheckedType Fp (Builder Vg (KimchiConstraint Fp)) inVal inVar]
    -- the application rule: from its input, each slot's statement and the public output
    (rule :
      inVar →
        CircuitM Fp (Builder Vg (KimchiConstraint Fp)) (((i : Fin n) → PrevStatement (ss i)) ×
          outVar))
    -- the step circuit's advice
    (adv : StepMainAdvice n w (SlotSource.widths w srcs) 1 ncPrevStep S.σ.k StepIPARounds inVal)
    -- the next wrap circuit's valuation
    (Vs : Valuation Fq)
    -- the tag's branches' slot counts
    (widths : Vector (Fin (w + 1)) branches)
    -- the step SRS
    (σStep : SRS IpaVesta.curve.Point)
    -- the Lagrange tables the wrap circuit bakes in, per step domain
    (lagrange : ℕ → Vector (Vector IpaVesta.curve.Point ncStep)
      (CircuitType.size Fp (StepStatement (UnfVal S.σ.k) Fp w)))
    -- the tag's step keys, one per branch
    (stepKeys : Vector (KimchiVK IpaVesta.curve ncStep) branches)
    -- each slot's compile-time wrap domain index per branch: the tag's `w` slots, front-padded
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- the padding challenges
    (dummy : Vector Fq S.σ.k)
    -- each wrap slot's challenge-stack height
    (slotWidths : Vector (Fin (MaxProofsVerified + 1)) w)
    -- the wrap circuit's advice
    (advW : WrapMainAdvice w ncStep S.σ.k StepIPARounds (slotWidths.map Fin.val).sum)
    -- fewer branches than the field's characteristic
    (hbr : branches ≤ PALLAS_SCALAR_CARD)
    -- the active branch
    (b : Fin branches) :
    -- the compiled step circuit: its rows, and the cells of the run that emitted them
    let step :=
      compileWith (a := Unit) (b := StepStatement (UnfVal S.σ.k) Fp w)
        (stepMainCircuit (c := Builder Vg (KimchiConstraint Fp)) (outVal := outVal)
          srcs
          hws
          S.σ.h
          P
          domains
          (constPt dummySg)
          dummyUnf
          rule
          adv)
    -- the compiled wrap circuit, over the branches' keys and domains, the Lagrange tables and the
    -- SRS's blinding base
    let wrap :=
      compileWith (a := StatementPacked StepIPARounds (Type1 Fq) Fq) (b := Unit)
        (wrapMainCircuit (c := Builder Vs (KimchiConstraint Fq))
          (FopParams.of IpaPallas.curve 1 S.σ.k Linearization.fqTokens)
          widths
          (stepDomainLog2s stepKeys)
          (stepKeyCells stepKeys)
          pins
          lagrange
          σStep.h
          dummy
          slotWidths
          advW)
    -- `Vg` satisfies every constraint of the compiled step circuit
    (∀ con ∈ step.constraints, ConstraintHolds.Holds Vg con) →
    -- `Vs` satisfies every constraint of the compiled wrap circuit
    (∀ con ∈ wrap.constraints, ConstraintHolds.Holds Vs con) →
    -- the step circuit's run
    let stepOut := step.result.1.2
    -- the wrap circuit's statement
    let wrapStmt := inputVar (F := Fq) (a := StatementPacked StepIPARounds (Type1 Fq) Fq)
    -- the wrap circuit's cells over it
    let wrapFinalizeOut := wrap.result.1.2.1
    let wrapVerifyOut := wrap.result.1.2.2
    -- the wrap circuit's branch index reads as `b`
    wrapFinalizeOut.whichBranch.val Vs = (b : Fq) →
    -- the step proof's public input: the step circuit's statement reads as the one the wrap
    -- circuit's cells hold, each cell the scalar its x_hat ladder applies (`StepStatement.ofWrap`)
    CircuitType.Reads Vg stepOut.out (StepStatement.ofWrap Vs wrapVerifyOut.statement) →
    -- slot `i` must verify
    ∀ i : Fin n,
      CircuitType.Reads Vg (stepOut.prevs i).mustVerify true →
      let inp := slotInput (hws i) (constPt dummySg) (stepOut.prevs i) (stepOut.slots i)
          stepOut.unfs[i] stepOut.msgs[i]
      -- the next wrap circuit's slot for it
      let jf := Fin.cast (Nat.sub_add_cancel hn) (Fin.natAdd (w - n) i)
      let sl := wrapFinalizeOut.slots[jf]
      -- the slot's wrap key `K`, one chunk over the wrap SRS: its source fits `K`, its key
      -- cells read as `K`
      ∀ K : Key IpaPallas.curve 1, 1 = chunkCount S.σ.k K.cvk.domainLog2 →
      WrapKeyLayout K.cvk →
      (srcs i).Fits S.σ K.cvk →
      KeyReads IpaPallas.curve Vg ((srcs i).keyCells stepOut.vk.points) K.cvk →
      -- no relation the slot statements' public-input commitment names commits the SRS to the
      -- identity
      (∀ (inp' : VerifyOneInput (ss i) StepIPARounds S.σ.k 1 ncPrevStep
          (SlotSource.widths w srcs i))
        msg, S.σ.Avoids (stepRelationsAt S.σ K.cvk (inp'.statement msg))) →
      -- the active branch compiled its wrap slot for `K`'s domain
      ∀ j : ℕ, sl.pins[b] = some j → wrapDomainLog2s[j]? = some K.cvk.domainLog2 →
      ∃ (cp : KimchiProof IpaPallas.curve 1 S.σ.k) (ms : Vector Bool (SlotSource.widths w srcs i)),
        -- the slot's public input: its statement, carrying the step-message digest
        let pub := inp.publicInputAt K.cvk Vg ms
        -- its cells hold `cp`, with masks `ms`
        inp.WireReads K.cvk Vg ((srcs i).keyCells stepOut.vk.points) cp ms ∧
        -- the next wrap circuit's finalize cells hold `cp`'s evaluations and old challenges
        FopTies S.σ K.cvk cp pub (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) ∧
        -- the link emits `cp`'s deferred obligation, as its outgoing messages carry it
        StepWrap.emittedAccumulator Vg Vs i jf stepOut wrapVerifyOut wrapFinalizeOut
          = ⟨cp.opening.sg, wireChallenges S.σ K.cvk cp pub⟩ ∧
        -- the link consumes `cp`'s old accumulators, as its incoming messages were rebuilt
        StepWrap.consumedAccumulators Vg Vs inp dummy wrapFinalizeOut jf = cp.olds.toList ∧
        -- the step circuit and the next wrap circuit hash their messages
        stepOut.HashesMessages Vg ∧
        wrapVerifyOut.HashesMessages Vs dummy wrapStmt wrapFinalizeOut ∧
        -- of `cp` itself: only the deferred `sg` equation remains
        (SgOk S.σ K.cvk cp pub →
          kimchiVerify IpaPallas.curve S.σ K.cvk cp pub = true) := by
  intro step wrap hstep hwrap
  rw [show step.result.1.2 = _ from compileWith_stepMainCircuit_cells srcs hws _ _ _ _ _ _ _,
    show wrap.result.1.2 = _ from compileWith_wrapMainCircuit_cells _ _ _ _ _ _ _ _ _ _]
  intro stepOut wrapStmt wrapFinalizeOut wrapVerifyOut hb htie i hmv inp jf sl K hK hlayout hfit
      hkey havoid j hpin hdom
  -- the step side: `shouldFinalize` set, and the group half accepts `cp`
  obtain ⟨hsfG, hslot, -, hpts, ⟨ms, hms⟩, -⟩ := (builder_spec_iff _ _).mp
    (stepMain_reads (outVal := outVal) S.σ P domains
      (by norm_num [MaxProofsVerified, StepIPARounds]) srcs
      (fun _ _ _ => True)
      (fun _ _ _ => builder_spec_imp _ _ _ (builder_spec_true _) fun _ _ _ _ _ => trivial)
      (hn.trans hw) hws (constPt dummySg) dummyUnf rule adv
      (by rw [hE]; decide)) 0
      (fun con hc => hstep con (mem_compileWith_stepMainCircuit srcs hws _ _ _ _ _ _ _ hc)) i hmv
  -- the wrap proof the slot's cells hold
  obtain ⟨hon, holds⟩ := slotInput_onCurve (hws i) hdummySg (stepOut.prevs i) stepOut.unfs[i]
      stepOut.msgs[i] hpts
  let cp := slotProof Vg Vs inp sl.evals sl.prevChallenges
  have hguards : Guards IpaPallas.curve K.cvk cp (inp.publicInputAt K.cvk Vg ms) := by
    constructor
    · rw [hlayout.prevChallenges_eq]
      exact Vector.size_toArray _
    · rw [hlayout.publicCount_eq]
      exact stepPublicInput_size _ _
  have hwire : inp.WireReads K.cvk Vg ((srcs i).keyCells stepOut.vk.points) cp ms :=
    ⟨hms, hkey, IvpProof.read_proofReads _ _ _ _ _ _ hon, slotProof_olds holds⟩
  have hf := slotProof_fopTies (Vg := Vg) (Vs := Vs) S.σ K.cvk (inp := inp) sl.unfinalized
    sl.evals sl.prevChallenges (inp.publicInputAt K.cvk Vg ms)
  obtain ⟨v, hv, hv1⟩ := hslot S rfl K hK hfit havoid cp ms hwire
  -- the wrap side: the body's constraints hold, so its finalize read does
  have hbody : ∀ con ∈ (build (wrapMain (c := Builder Vs (KimchiConstraint Fq))
      (FopParams.of IpaPallas.curve 1 S.σ.k Linearization.fqTokens) widths
      (stepDomainLog2s stepKeys)
          (stepKeyCells stepKeys) pins
          lagrange σStep.h dummy
      slotWidths advW
      (inputVar (F := Fq) (a := StatementPacked StepIPARounds (Type1 Fq) Fq)))
      (bodyStart (F := Fq) (c := Builder Vs (KimchiConstraint Fq))
        (a := StatementPacked StepIPARounds (Type1 Fq) Fq))
      ).constraints, ConstraintHolds.Holds Vs con := fun con hc =>
    hwrap con (mem_compileWith_wrapMainCircuit _ _ _ _ _ _ _ _ _ _ hc)
  -- the finalize reads the slot at `K`
  have hreads := wrapMain_reads S.σ Vs widths (stepDomainLog2s stepKeys)
    (stepKeyCells stepKeys) pins
    lagrange σStep.h dummy
    slotWidths advW
    (inputVar (F := Fq) (a := StatementPacked StepIPARounds (Type1 Fq) Fq)) hw hbr
  obtain ⟨b', hb', hwb, -, -, -, -, hfin⟩ := (builder_spec_iff _ _).mp hreads _ hbody
  -- the tie, slot by slot: the wrap claims hold the step claims lifted (`slot_cast`)
  obtain ⟨hsplitsEq, hsr, hbnd, hslots, hhash⟩ := (builder_spec_iff _ _).mp
    (wrapMain_statement (FopParams.of IpaPallas.curve 1 S.σ.k Linearization.fqTokens) Vs widths
      (stepDomainLog2s stepKeys) (stepKeyCells stepKeys) pins
      lagrange σStep.h dummy
      slotWidths advW
      (inputVar (F := Fq) (a := StatementPacked StepIPARounds (Type1 Fq) Fq))
      (stepKeys[0]'(Nat.pos_of_neZero branches)).nc_pos) _
      hbody
  have hout := (builder_spec_iff _ _).mp
    (stepMain_out (outVal := outVal) srcs hws S.σ.h P domains (constPt dummySg) dummyUnf rule adv) 0
    (fun con hc => hstep con (mem_compileWith_stepMainCircuit srcs hws _ _ _ _ _ _ _ hc))
  -- slot `i` is entry `(w − n) + i` on both sides of the tie
  have hjv : jf.val = w - n + i := rfl
  have hents : CircuitType.Reads Vg stepOut.out.proofState.unfinalizedProofs
      (wrapVerifyOut.statement.proofState.unfinalizedProofs.map (UnfVal.ofWrap Vs)) := by
    simp only [CircuitType.reads_ofEquiv, StepStatement.equivProd, StepProofState.equivProd,
      Equiv.coe_fn_mk, CircuitType.reads_prod] at htie
    exact htie.1.1
  have hblk := CircuitType.reads_vector.mp hents (w - n + i) (by omega)
  have hl : stepOut.out.proofState.unfinalizedProofs[w - n + i]'(by omega) = stepOut.unfs[i] := by
    have h1 : stepOut.out.proofState.unfinalizedProofs = _ := hout.1
    simp [h1]
    rfl
  have hr :
      (wrapVerifyOut.statement.proofState.unfinalizedProofs.map (UnfVal.ofWrap Vs))[w - n + i]'
      (by omega) = UnfVal.ofWrap Vs wrapVerifyOut.splits[jf] := by
    have hs : wrapVerifyOut.statement.proofState.unfinalizedProofs = wrapVerifyOut.splits :=
        hsplitsEq
    simp [hs, hjv]
  rw [hl, hr] at hblk
  have hbj : ∀ x ∈ wrapVerifyOut.splits[jf].packed, x.Bound Vs := fun x hx => hbnd x (by
    simp only [StepStatement.packed, Vector.toList_mk]
    rw [hsplitsEq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨_, Vector.mem_toList_iff.mpr (Vector.getElem_mem _), Vector.mem_toList_iff.mpr hx⟩)))
  obtain ⟨hc, hsf⟩ := slot_cast stepOut.unfs[i] wrapVerifyOut.splits[jf]
      wrapFinalizeOut.proofState.unfinalizedProofs[jf]
    hblk hbj (hsr jf)
  rw [← (hslots jf).1] at hc hsf
  -- the circuit's branch is `b`: both are below the field's characteristic
  have hbb : b' = b.val := CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
    (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) (hwb.symm.trans hb)
  subst hbb
  obtain ⟨hE, hK⟩ := hfin K j hdom _ hpin (reads_true_of_tie hsf hsfG) cp _ Vg inp.unfinalized v
    hv hv1 hc hf
  refine ⟨cp, ms, hwire, hf, ?_, ?_, hout.2.2, hhash, hK hguards⟩
  · have hsgs : stepOut.messagesForNextStepProof.challengePolynomialCommitments
        = Vector.ofFn fun i => (stepOut.slots i).sg.pt := hout.2.1
    simp only [StepWrap.emittedAccumulator, Accumulator.ofCells, Fin.getElem_fin,
      Vector.getElem_map, hsgs, Vector.getElem_ofFn] at hE ⊢
    rw [hE]
    rfl
  · -- the finalize slot's challenges are the rebuilt message's, padded
    simp only [StepWrap.consumedAccumulators]
    rw [← (hslots jf).2]
    rfl

end Pickles
