import Kimchi.Columns
import Pickles.IncrementallyVerify
import Pickles.FinalizeOtherProof
import Pickles.PublicInputCommit
import Pickles.Statement
import Pickles.Encoding

/-!
# `verifyProof` (the step side)

The group-half check of one wrap proof, as the step circuit runs it, transcribed from the OCaml
step verifier (`step_verifier.ml`).

`verifyProof` is the group half with its public input fixed: the wrap statement is packed into
public-input leaves (`WrapStatement.packed`, `packLeaves`), `incrementallyVerifyProof` runs
with the claims of the unfinalized proof (`ξ`, the combined inner product, `b`, the plonk
claims), and its two outputs other than the success bit are asserted against that proof: the
digest equals the claimed `spongeDigestBeforeEvaluations`, and each returned round
prechallenge equals the claimed one — except in the base case, where the claim is compared
with itself.

The two circuits that touch one proof, the group half here and the scalar half
(`finalizeOtherProofStep`) one circuit later over the other field, compose to the wire
verifier in `Pickles.TwoHalves`. The upstream step circuit runs the two halves on two
different proofs in one circuit; that composition is not ported.

## Main definitions

* `WrapStatement.packed`, `packLeaves`: the wrap statement as the public-input leaf list;
* `UnfinalizedProof.packed`, `StepStatement.packed`: one slot, and the step statement, as
  packed scalars;
* `IvpInput.withClaims`, `ivpInputOf`: the group half's input from a proof's claims;
* `verifyProof`: the gadget.

## Main results

* `VerifyReads` / `verifyProof_reads`: on any group side and curve shape, `verifyProof` reads
  as the group half's `IvpReads` at the public input `pubOf (packLeaves statement)`, with the
  claimed digest equal to the wire's digest element and, off the base case, the claimed round
  prechallenges equal to the returned ones pair by pair. The public-input chunks read through
  `xHatKnown_reads_publicCommitment` at the tables' binding (`XhatTable.Bound`), the group half
  through `incrementallyVerifyProof_reads` at `IvpHyps`, and the assertion loop by its
  invariant. `verifyProof_step_reads` is the step side.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open scoped Kimchi

/-! ## Packing the wrap statement -/

section Pack

variable {F : Type} [Field F] [DecidableEq F] {nc k : ℕ}

/-- The branch data as one 10-bit value `4·domainLog2 + m₀ + 2·m₁`, over the mask bits `m₀`,
`m₁`. A missing mask bit reads as `0`. -/
def BranchData.packed (bd : BranchData (FVar F) (BoolVar F)) : FVar F :=
  let bit (i : ℕ) : CVar F := match bd.proofsVerifiedMask.toList[i]? with
    | some b => (↑b : CVar F)
    | none => .const 0
  CVar.add_ (CVar.scale_ 4 bd.domainLog2) (CVar.add_ (bit 0) (CVar.scale_ 2 (bit 1)))

/-- The wrap statement as packed scalars, in packing order: the five shifted scalars
`cip, b, ζ^{2^k}, ζⁿ, perm` (full), `β, γ, α, ζ, ξ` (128), the sponge digest and the two
message digests (full), the round challenges (128), the packed branch data (10). The shifted
scalars are the step proof's `Fp` values in their `Type1` representative, a full field element
each. -/
def WrapStatement.packed (st : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F))) :
    List (PackedScalar F) :=
  let dv := st.proofState.deferredValues
  let pl := dv.plonk
  [.full dv.combinedInnerProduct.val, .full dv.b.val, .full pl.zetaToSrsLength.val,
   .full pl.zetaToDomainSize.val, .full pl.perm.val,
   .b128 pl.beta.val, .b128 pl.gamma.val,
   .b128 pl.alpha.val, .b128 pl.zeta.val, .b128 dv.xi.val,
   .full st.proofState.spongeDigestBeforeEvaluations,
   .full st.proofState.messagesForNextWrapProof, .full st.messagesForNextStepProof]
  ++ dv.bulletproofChallenges.toList.map (fun c => .b128 c.val)
  ++ [.b10 dv.branchData.packed]

/-- A packed wrap statement has no boolean cell: the branch data is one 10-bit scalar. -/
theorem WrapStatement.packed_isScalar
    (st : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F))) :
    ∀ k ∈ st.packed, k.IsScalar := by
  simp only [WrapStatement.packed, PackedScalar.IsScalar, List.cons_append, List.nil_append,
    List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false, forall_eq_or_imp,
    true_and]
  rintro a (⟨c, -, rfl⟩ | rfl) <;> trivial

/-- The public-input leaves of a wrap statement: `packLeavesOf` its packing. -/
def packLeaves (st : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F)))
    (tab : XhatTable F nc) : List (Leaf F nc) :=
  packLeavesOf st.packed tab

/-- One slot of the step statement as packed scalars, in packing order: the five split claims
`cip, b, ζ^{2^k}, ζⁿ, perm` as a full half and a boolean parity, the digest full, `β, γ, α, ζ, ξ`
and the `k` round challenges 128-bit, `shouldFinalize` boolean. -/
def UnfinalizedProof.packed
    (u : UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (SplitField (FVar F) (BoolVar F)))) :
    List (PackedScalar F) :=
  let dv := u.deferredValues
  let pl := dv.plonk
  let split (x : Type2 (SplitField (FVar F) (BoolVar F))) : List (PackedScalar F) :=
    [.full x.val.sDiv2, .bit x.val.sOdd]
  split dv.combinedInnerProduct ++ split dv.b ++ split pl.zetaToSrsLength
    ++ split pl.zetaToDomainSize ++ split pl.perm
    ++ [.full u.spongeDigestBeforeEvaluations,
        .b128 pl.beta.val, .b128 pl.gamma.val, .b128 pl.alpha.val, .b128 pl.zeta.val,
        .b128 dv.xi.val]
    ++ dv.bulletproofChallenges.toList.map (fun c => .b128 c.val)
    ++ [.bit u.shouldFinalize]

/-- The step statement as packed scalars, in packing order: the slots (`UnfinalizedProof.packed`),
then the `messagesForNextStepProof` digest and the slots' `messagesForNextWrapProof` digests,
full. -/
def StepStatement.packed {n : ℕ}
    (st : StepStatement k n (FVar F) (BoolVar F) (Type2 (SplitField (FVar F) (BoolVar F)))) :
    List (PackedScalar F) :=
  st.proofState.unfinalizedProofs.toList.flatMap UnfinalizedProof.packed
    ++ [.full st.proofState.messagesForNextStepProof]
    ++ st.messagesForNextWrapProof.toList.map .full

/-- The group half's input with its claims taken from an unfinalized proof: `xi`,
`combinedInnerProduct`, `b` and the plonk claims of its deferred values; the key, proof and
`sgOld` cells as given. -/
def IvpInput.withClaims {sf : Type} (inp : IvpInput k nc (FVar F) (BoolVar F) sf)
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf) :
    IvpInput k nc (FVar F) (BoolVar F) sf :=
  let dv := u.deferredValues
  { inp with
    plonk := ⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩,
      dv.plonk.perm, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩
    xi := dv.xi
    deferred := ⟨dv.combinedInnerProduct, dv.b⟩ }

end Pack

/-! ## The group half's input, from its records -/

section Records

open Kimchi

/-- A proof at `nc` chunks as the group half reads it, polymorphic in its cells like the
statement records. `IvpInput` holds the commitments as chunk lists; this is their sized form,
the shape a circuit input has. -/
structure IvpProof (k nc : ℕ) (f sf : Type) where
  /-- The 15 witness commitments, `nc` chunks each. -/
  wComm : Vector (Vector (AffinePoint f) nc) wCols
  /-- The permutation accumulator's commitment, `nc` chunks. -/
  zComm : Vector (AffinePoint f) nc
  /-- The `7 · nc` quotient chunks. -/
  tComm : Vector (AffinePoint f) (quotChunks * nc)
  /-- The opening, at `k` rounds. -/
  opening : BulletproofOpening k f sf

/-- A proof is its witness commitments, `zComm`, its quotient chunks and its opening; the
circuit type `instIvpProofCircuitType` is carried along this. -/
def IvpProof.equivProd (k nc : ℕ) (f sf : Type) :
    IvpProof k nc f sf ≃
      Vector (Vector (AffinePoint f) nc) wCols × Vector (AffinePoint f) nc ×
        Vector (AffinePoint f) (quotChunks * nc) × BulletproofOpening k f sf :=
  ⟨fun p => (p.wComm, p.zComm, p.tComm, p.opening), fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance instIvpProofCircuitType {F sv sf : Type} {k nc : ℕ} [CircuitType F sv sf] :
    CircuitType F (IvpProof k nc F sv) (IvpProof k nc (FVar F) sf) :=
  CircuitType.ofEquiv (IvpProof.equivProd k nc F sv) (IvpProof.equivProd k nc (FVar F) sf)

/-- The group half's input from a proof's deferred values (its claims), the old accumulator
points under their keep bits (`sgOld`), a key's commitments and the proof. -/
def ivpInputOf {F sf : Type} {k nc : ℕ} (dv : DeferredValues k (FVar F) sf)
    (sgOld : List (Option (BoolVar F) × AffinePoint (FVar F)))
    (key : VkComms nc (AffinePoint (FVar F))) (pr : IvpProof k nc (FVar F) sf) :
    IvpInput k nc (FVar F) (BoolVar F) sf :=
  { plonk := ⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩, dv.plonk.perm,
      dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩
    xi := dv.xi
    deferred := ⟨dv.combinedInnerProduct, dv.b⟩
    sgOld, key
    wComm := pr.wComm.toList.map (·.toList)
    zComm := pr.zComm.toList
    tComm := pr.tComm.toList
    opening := pr.opening }

/-- The proof's commitment cells, counted: `15 · nc` witness chunks, `nc` accumulator chunks,
`7 · nc` quotient chunks. -/
theorem ivpInputOf_lengths {F sf : Type} {k nc : ℕ} (dv : DeferredValues k (FVar F) sf)
    (sgOld : List (Option (BoolVar F) × AffinePoint (FVar F)))
    (key : VkComms nc (AffinePoint (FVar F))) (pr : IvpProof k nc (FVar F) sf) :
    (ivpInputOf dv sgOld key pr).wComm.flatten.length = wCols * nc ∧
      (ivpInputOf dv sgOld key pr).zComm.length = nc ∧
      (ivpInputOf dv sgOld key pr).tComm.length = quotChunks * nc := by
  simp [ivpInputOf, List.length_flatten, List.map_map, Function.comp_def]
  omega

/-- The circuit's key cells read as the key (`KeyReads`), and the sponge after the index
digest squeezes to the key's digest. -/
structure VkReads {C : KimchiCurve} {nc : ℕ} (cvk : KimchiVK C nc) (V : Valuation C.BaseField)
    (spongeAfterIndex : SpongeVar C.BaseField)
    (keyCells : VkComms nc (AffinePoint (FVar C.BaseField))) : Prop where
  /-- The sponge after the index digest squeezes to the key's digest. -/
  idx : ∃ st : Poseidon.State C.BaseField, SpongeVar.ReadsAt V spongeAfterIndex st ∧
    (Poseidon.squeeze C.sponge.params st).1 = cvk.digest
  /-- The key's commitments. -/
  key : KeyReads C V keyCells cvk

end Records

/-! ## The gadgets -/

section Gadget

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
  {ks k nc : ℕ}

/-- One proof's group-half check: the public-input commitment from the packed statement
(`publicInputCommitKnown`, chunk by chunk, with the constant correction seed and sum), the
group half at the unfinalized proof's claims (`IvpInput.withClaims`), then the two assertions:
the digest equals the claimed `spongeDigestBeforeEvaluations`; each returned round
prechallenge equals the claimed one, the claim compared with itself in the base case. Returns
the success bit. -/
def verifyProof {sf : Type} (ops : IpaScalarOps F c sf) (e : IpaEndo F) (p : Poseidon.Params F)
    (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) {nc : ℕ} (tab : XhatTable F nc)
    (spongeAfterIndex : SpongeVar F) (isBaseCase : BoolVar F)
    (statement : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F)))
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (cells : IvpInput k nc (FVar F) (BoolVar F) sf) : CircuitM F c (BoolVar F) := do
  let leaves := packLeaves statement tab
  let computeXHat : CircuitM F c (List (AffinePoint (FVar F))) :=
    (List.finRange nc).mapM fun ci =>
      publicInputCommitKnown ci blindingH tab.corrHead[ci] tab.corrSum[ci] leaves
  let o ← incrementallyVerifyProof ops e p endo gm sqrtF false blindingH spongeAfterIndex
    computeXHat (cells.withClaims u)
  assertEqual u.spongeDigestBeforeEvaluations o.spongeDigest
  for c12 in u.deferredValues.bulletproofChallenges.toList.zip o.bulletproofChallenges do
    let c2' ← selectField isBaseCase c12.1.val c12.2.val
    assertEqual c12.1.val c2'
  pure o.success

end Gadget

/-! ## The reads -/

section Read

variable {C : KimchiCurve} {V : Valuation C.BaseField} {sf : Type} {ks nc : ℕ}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- The group half's claim cells from a `DeferredValues` record: the plonk claims, `ξ`, and
`cip`, `b`. -/
def DeferredValues.toIvpClaims {F sf : Type} {k : ℕ} (dv : DeferredValues k (FVar F) sf) :
    IvpClaims (FVar F) sf :=
  ⟨⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩,
    dv.plonk.perm, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩,
   dv.xi, ⟨dv.combinedInnerProduct, dv.b⟩⟩

/-- Under any valuation satisfying the emitted constraints, `verifyProof`'s returned bit reads
as a bit (`incrementallyVerifyProof_success_bit`). -/
theorem verifyProof_success_bit {F : Type} [Field F] [DecidableEq F] [ToNat F] {V : Valuation F}
    {sf : Type} (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) {k ks nc : ℕ} (tab : XhatTable F nc)
    (spongeAfterIndex : SpongeVar F) (isBaseCase : BoolVar F)
    (statement : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F)))
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (cells : IvpInput k nc (FVar F) (BoolVar F) sf) :
    ⦃⌜True⌝⦄ verifyProof ops e p endo gm sqrtF blindingH tab spongeAfterIndex isBaseCase
      statement u cells
    ⦃⇓ v _ => ⌜∃ b : Bool, (↑v : CVar F).val V = bit b⌝⦄ := by
  have hivp := fun cx => incrementallyVerifyProof_success_bit (V := V) ops e p endo gm sqrtF
    false blindingH spongeAfterIndex cx (cells.withClaims u)
  have hsel := fun b x y => builder_spec_true
    (selectField (c := Builder V (KimchiConstraint F)) b x y)
  simp only [verifyProof]
  mvcgen [hivp, hsel] invariants
    · ⇓⟨_, _⟩ => ⌜True⌝

/-- `verifyProof`'s read: some group-half output `o` satisfying `IvpReads` at the wire's public
input `pub`, whose success bit is the returned bit, whose digest cell reads as the claimed
`spongeDigestBeforeEvaluations` (so the claim is the wire's digest element), and whose round
prechallenges read as the claimed ones off the base case, pair by pair over the zip, and the
returned bit reads as a bit. The gadget compares the two lists as far as both reach; their
lengths are the statement's and the opening's, not the gadget's. -/
def VerifyReads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (u : UnfinalizedProof σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf) (base : Bool)
    (v : BoolVar C.BaseField) : Prop :=
  ∃ o : IvpOutput C.BaseField,
    IvpReads S σ cvk cp pub u.deferredValues.toIvpClaims o ∧
    o.success = v ∧
    u.spongeDigestBeforeEvaluations.val V = o.spongeDigest.val V ∧
    (base = false → ∀ p ∈ u.deferredValues.bulletproofChallenges.toList.zip o.bulletproofChallenges,
      p.1.val.val V = p.2.val.val V) ∧
    ∃ b : Bool, (↑v : CVar C.BaseField).val V = bit b

/-- **`verifyProof` reads as the group half at the packed statement, on either side.** On the
group side `S` and the curve shape `X`: the wire's public input is
`pubOf (packLeaves statement)`, the statement's scalars reduced to the scalar field; the
public-input commitment tables are bound to the key at those leaves (`XhatTable.Bound`); the
group half's premises hold at the claims-substituted cells (`IvpHyps`). -/
theorem verifyProof_reads
    {nc : ℕ}
    (S : IvpSide C V ops)
    (X : PastaShape C)
    -- the wire objects
    (σ : SRS C.Point)
    (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k)
    -- the circuit's constants
    (endo : FVar C.BaseField)
    (sqrtF : C.BaseField → Option C.BaseField)
    (blindingH : AffinePoint (FVar C.BaseField))
    -- the public-input commitment tables
    (tab : XhatTable C.BaseField nc)
    -- the cells: the sponge after the index digest, the base-case bit, the wrap statement,
    -- the unfinalized proof it is checked against, the group half's commitment cells
    (spongeAfterIndex : SpongeVar C.BaseField)
    (isBaseCase : BoolVar C.BaseField)
    (statement : WrapStatement ks (FVar C.BaseField) (BoolVar C.BaseField)
      (Type1 (FVar C.BaseField)))
    (u : UnfinalizedProof σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (cells : IvpInput σ.k nc (FVar C.BaseField) (BoolVar C.BaseField) sf)
    -- the values the premises speak about: the base-case bit, the old accumulator points under
    -- their bits
    (base : Bool)
    (oldsW : List (C.Point × Bool))
    -- the base-case bit's reading, the tables bound to the key at the packed statement's
    -- leaves, the group half's premises at the claims-substituted cells
    (hbase : CircuitType.Reads V isBaseCase base)
    (htab : tab.Bound X V σ cvk blindingH (packLeaves statement tab))
    (hivp : IvpHyps S σ cvk cp (pubOf C V (packLeaves statement tab)) false
      spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    verifyProof (c := Builder V (KimchiConstraint C.BaseField)) ops S.curve.e C.sponge.params endo
      (.ofSpec C.groupMap)
      sqrtF blindingH tab spongeAfterIndex isBaseCase statement u cells
    ⦃⇓ v _ => ⌜VerifyReads S σ cvk cp (pubOf C V (packLeaves statement tab)) u base v⌝⦄ := by
  obtain ⟨⟨Ts, cps, hxhat⟩, hbases, hcorrs⟩ := htab
  -- the leaves are headed by a scalar leaf: the first packed scalar is `cip`
  have hhead : leafHeadScalar (packLeaves statement tab) := by
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hbases
    obtain ⟨c', cs, hc⟩ := List.exists_cons_of_ne_nil hcorrs
    simp [packLeaves, packLeavesOf, WrapStatement.packed, leafHeadScalar, hb, hc]
  -- the public-input commitment, chunk by chunk, reads as the wire's, crossed to `C.E`
  have hXhat : ⦃⌜True⌝⦄
      (List.finRange nc).mapM (fun ci => publicInputCommitKnown
        (S := Builder V (KimchiConstraint C.BaseField)) ci blindingH tab.corrHead[ci]
        tab.corrSum[ci] (packLeaves statement tab))
      ⦃⇓ pts _ => ⌜CommReads C V pts
        (publicCommitment C σ cvk (pubOf C V (packLeaves statement tab))).toList⌝⦄ := by
    have hvec : (publicCommitment C σ cvk (pubOf C V (packLeaves statement tab))).toList
        = (List.finRange nc).map fun ci =>
            (publicCommitment C σ cvk (pubOf C V (packLeaves statement tab)))[ci] := by
      apply List.ext_getElem <;> simp
    unfold CommReads
    rw [hvec]
    refine builder_spec_imp _ _ _
      (builder_spec_mapM _ (fun r P => OnCurveAt X.d.W V r (SWPoint.equivPoint C.E P)) _
        (fun ci => xHatKnown_reads_publicCommitment X ci σ cvk blindingH tab.corrHead[ci]
          tab.corrSum[ci] _ _ _ (hxhat ci).1 hhead (hxhat ci).2) _)
      fun pts hp => hp.imp fun _ _ h => h
  -- the blinding cell's read is the tables' own: every chunk's binding carries it
  have hh : OnCurveAt C.E.toAffine V blindingH (SWPoint.equivPoint C.E σ.h) :=
    (hxhat ⟨0, hivp.nc_pos⟩).1.blinding
  have hivp := builder_spec_and _ _ _
    (incrementallyVerifyProof_reads S σ cvk cp _ endo sqrtF false blindingH
      spongeAfterIndex _ (cells.withClaims u) oldsW hXhat hh hivp)
    (incrementallyVerifyProof_success_bit ops S.curve.e C.sponge.params endo (.ofSpec C.groupMap)
      sqrtF false blindingH spongeAfterIndex _ (cells.withClaims u))
  have hb := CircuitType.reads_boolVar.mp hbase
  simp only [verifyProof]
  mvcgen [hivp] invariants
    · ⇓⟨xs, _⟩ => ⌜base = false → ∀ p ∈ xs.prefix, p.1.val.val V = p.2.val.val V⌝
  · -- the loop step: the selected cell reads as the returned prechallenge off the base case
    rename_i pref cur suff _ _ _ hinv r _ hsel _ _ heq
    intro hbf p hp
    rw [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hinv hbf p hp
    · rw [heq, hsel base hb, hbf]
      simp
  · -- the loop entry: nothing compared yet
    intro _ p hp
    exact absurd hp List.not_mem_nil
  · -- the exit: the read
    rename_i o _ hivp' _ _ hdig _ _ hall
    exact ⟨o, hivp'.1, rfl, hdig, hall, hivp'.2⟩

end Read

section StepRead

/-- **`verifyProof` reads as the group half on the step side**: `verifyProof_reads` at `stepSide`
and `pastaShapePallas`. -/
theorem verifyProof_step_reads {nc : ℕ} {V : Valuation Fp}
    (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc σ.k)
    (endo : FVar Fp) (sqrtF : Fp → Option Fp) (blindingH : AffinePoint (FVar Fp))
    (tab : XhatTable Fp nc) (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof σ.k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput σ.k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (base : Bool) (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads V isBaseCase base)
    (htab : tab.Bound pastaShapePallas V σ cvk blindingH (packLeaves statement tab))
    (hivp : IvpHyps (stepSide V) σ cvk cp (pubOf IpaPallas.curve V (packLeaves statement tab))
      false spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    verifyProof (c := Builder V (KimchiConstraint Fp)) IpaScalarOps.step IpaEndo.pallas
      IpaPallas.curve.sponge.params endo groupMapParamsPallas sqrtF blindingH tab
      spongeAfterIndex isBaseCase statement u cells
    ⦃⇓ v _ => ⌜VerifyReads (stepSide V) σ cvk cp
      (pubOf IpaPallas.curve V (packLeaves statement tab)) u base v⌝⦄ :=
  verifyProof_reads (stepSide V) pastaShapePallas σ cvk cp endo sqrtF blindingH tab
    spongeAfterIndex
    isBaseCase statement u cells base oldsW hbase htab hivp

end StepRead

/-! The gadget is sealed after its read: a consumer composes `verifyProof_step_reads`, never the
body. -/
attribute [irreducible] verifyProof

end Pickles
