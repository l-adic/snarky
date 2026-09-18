import Pickles.IncrementallyVerify
import Pickles.FinalizeOtherProof
import Pickles.PublicInputCommit
import Pickles.Statement

/-!
# `verify` (the step side)

The port of OCaml `Step_verifier.verify` (`step_verifier.ml:1340–1413`), the `verify` call of
PS `Pickles.Step.VerifyOne.verifyOne`.

`verify` is the group half with its public input fixed: the wrap statement is packed into the
`x_hat` leaves (`Spec.pack`, PS `packStatement`), `incrementally_verify_proof` runs with the
claims of the unfinalized proof (`xi`, `combined_inner_product`, `b`, `plonk`), and its two
outputs other than the success bit are asserted against that proof: the digest equals the
claimed `sponge_digest_before_evaluations`, and each returned round prechallenge equals the
claimed one — except in the base case, where the claim is compared with itself.

The two circuits that touch one proof, the group half here and the scalar half
(`finalize_other_proof`) one circuit later over the other field, compose to the wire
verifier in `Pickles.TwoHalves`; `Step_main.verify_one`, which runs them on two different
proofs in one circuit, is not ported.

## Main definitions

* `WrapStatement.packed`, `packLeaves`: the wrap statement as the `x_hat` leaf list;
* `verifyProof`: `Step_verifier.verify`.

## Main results

* `VerifyReads` / `verifyProof_reads`: on any group side and `x_hat` side, `verify` reads as
  the group half's `IvpReads` at the public input `pubOf (packLeaves statement)`, the wire's
  public input being the packed statement, with the claimed digest equal to the wire's digest
  element and, off the base case, the claimed round prechallenges equal to the returned ones
  pair by pair (hence, through `IvpReads`, the wire's). The `x_hat`
  chunks read through `xHatKnown_reads_publicCommitment` at the tables' binding
  (`XhatTable.Bound`), the group half through `incrementallyVerifyProof_reads` at `IvpHyps`,
  and the assertion loop by its invariant. `verifyProof_step_reads` is the step side.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

/-! ## Packing the wrap statement -/

section Pack

variable {F : Type} [Field F] [DecidableEq F] {nc k : ℕ}

/-- `Branch_data.pack`: `4·domain_log2 + m₀ + 2·m₁`, a 10-bit value (PS `packStatement`). A
missing mask bit reads as `0`. -/
def BranchData.packed (bd : BranchData (FVar F) (BoolVar F)) : FVar F :=
  let bit (i : ℕ) : CVar F := match bd.proofsVerifiedMask.toList[i]? with
    | some b => (↑b : CVar F)
    | none => .const 0
  CVar.add_ (CVar.scale_ 4 bd.domainLog2) (CVar.add_ (bit 0) (CVar.scale_ 2 (bit 1)))

/-- A packed public-input scalar with its ladder width: a full field element, a 128-bit
value, or the 10-bit packed branch data. -/
inductive PackedScalar (F : Type) [Field F] where
  /-- A 255-bit field element. -/
  | full (s : FVar F)
  /-- A 128-bit value. -/
  | b128 (s : FVar F)
  /-- A 10-bit value. -/
  | b10 (s : FVar F)

/-- `Spec.pack (Wrap.Statement.In_circuit.to_data statement)` (PS `packStatement`), in walk
order: the five shifted scalars `cip, b, ζ^{2^k}, ζⁿ, perm` (full), `β, γ` (128), `α, ζ, ξ`
(128), the three digests `sponge_digest, msg_wrap, msg_step` (full), the round challenges
(128), the packed branch data (10). The shifted scalars are the step proof's `Fp` values in
their `Type1` representative, a full field element each. -/
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

/-- The `x_hat` leaves of a wrap statement: leaf `i` is scalar `i` of `WrapStatement.packed`
with Lagrange base `i` and its shift correction from the table (`lagrange_with_correction`). -/
def packLeaves (st : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F)))
    (tab : XhatTable F nc) :
    List (Leaf F nc) :=
  List.zipWith (fun k bc => match k with
    | .full s => Leaf.full s bc.1 bc.2
    | .b128 s => Leaf.b128 s bc.1 bc.2
    | .b10 s => Leaf.b10 s bc.1 bc.2) st.packed (tab.bases.zip tab.corrs)

/-- The group half's input with its claims taken from an unfinalized proof
(`step_verifier.ml:1366–1385`): `xi`, `combined_inner_product`, `b` and the plonk claims
of `unfinalized.deferred_values`; the key, proof and `sg_old` cells as given. -/
def IvpInput.withClaims {sf : Type} (inp : IvpInput k (FVar F) (BoolVar F) sf)
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf) :
    IvpInput k (FVar F) (BoolVar F) sf :=
  let dv := u.deferredValues
  { inp with
    plonk := ⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩,
      dv.plonk.perm, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩
    xi := dv.xi
    deferred := ⟨dv.combinedInnerProduct, dv.b⟩ }

end Pack

/-! ## The gadgets -/

section Gadget

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
  {ks k : ℕ}

/-- `Step_verifier.verify` (`step_verifier.ml:1340`): `x_hat` from the packed statement
(`publicInputCommitKnown`, chunk by chunk, with the constant correction seed and sum), the
group half at the unfinalized proof's claims, then the two assertions: the digest equals the
claimed `sponge_digest_before_evaluations`; each returned round prechallenge equals the
claimed one, the claim compared with itself in the base case. Returns the success bit. -/
def verifyProof {sf : Type} (ops : IpaScalarOps F c sf) (e : IpaEndo F) (p : Poseidon.Params F)
    (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) {nc : ℕ} (tab : XhatTable F nc)
    (spongeAfterIndex : SpongeVar F) (isBaseCase : BoolVar F)
    (statement : WrapStatement ks (FVar F) (BoolVar F) (Type1 (FVar F)))
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (cells : IvpInput k (FVar F) (BoolVar F) sf) : CircuitM F c (BoolVar F) := do
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

variable {C : KimchiCurve} {V : Valuation C.BaseField} {sf : Type} {ks : ℕ}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- `verify`'s read: some group-half output `o` satisfying `IvpReads` at the wire's public
input `pub`, whose success bit is the returned bit, whose digest cell reads as the claimed
`sponge_digest_before_evaluations` (so the claim is the wire's digest element), and whose
round prechallenges read as the claimed ones off the base case, pair by pair over the zip
(the gadget compares the two lists as far as both reach; their lengths are the statement's
and the opening's, not the gadget's), so the claims are the wire's `ipaRunAt` prechallenges. -/
def VerifyReads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (cells : IvpInput σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (u : UnfinalizedProof σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf) (base : Bool)
    (v : BoolVar C.BaseField) : Prop :=
  ∃ o : IvpOutput C.BaseField,
    IvpReads S σ cvk cp pub (cells.withClaims u).toIvpClaims o ∧
    o.success = v ∧
    u.spongeDigestBeforeEvaluations.val V = o.spongeDigest.val V ∧
    (base = false → ∀ p ∈ u.deferredValues.bulletproofChallenges.toList.zip o.bulletproofChallenges,
      p.1.val.val V = p.2.val.val V)

/-- **`verify` reads as the group half at the packed statement, on either side.** On the group
side `S` and the `x_hat` side `X`: the wire's public input is `pubOf (packLeaves statement)`,
the statement's scalars reduced to the scalar field; the `x_hat` tables are bound to the key
at those leaves (`XhatTable.Bound`); the group half's premises hold at the claims-substituted
cells (`IvpHyps`). -/
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
    -- the `x_hat` tables
    (tab : XhatTable C.BaseField nc)
    -- the cells: the sponge after the index digest, the base-case bit, the wrap statement,
    -- the unfinalized proof it is checked against, the group half's commitment cells
    (spongeAfterIndex : SpongeVar C.BaseField)
    (isBaseCase : BoolVar C.BaseField)
    (statement : WrapStatement ks (FVar C.BaseField) (BoolVar C.BaseField)
      (Type1 (FVar C.BaseField)))
    (u : UnfinalizedProof σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (cells : IvpInput σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
    -- the values the premises speak about: the base-case bit, the `sg_old` points under their
    -- bits
    (base : Bool)
    (oldsW : List (C.Point × Bool))
    -- the base-case bit's reading, the tables bound to the key at the packed statement's
    -- leaves, the group half's premises at the claims-substituted cells
    (hbase : CircuitType.Reads V isBaseCase base)
    (htab : tab.Bound X V σ cvk blindingH (packLeaves statement tab))
    (hivp : IvpHyps S σ cvk cp (pubOf C V (packLeaves statement tab)) false blindingH
      spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    verifyProof (c := Builder V (KimchiConstraint C.BaseField)) ops S.curve.e C.sponge.params endo
      (.ofSpec C.groupMap)
      sqrtF blindingH tab spongeAfterIndex isBaseCase statement u cells
    ⦃⇓ v _ => ⌜VerifyReads S σ cvk cp (pubOf C V (packLeaves statement tab)) cells u base v⌝⦄ := by
  obtain ⟨⟨Ts, cps, hxhat⟩, hbases, hcorrs⟩ := htab
  -- the leaves are headed by a scalar leaf: the first packed scalar is `cip`
  have hhead : leafHeadScalar (packLeaves statement tab) := by
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hbases
    obtain ⟨c', cs, hc⟩ := List.exists_cons_of_ne_nil hcorrs
    simp [packLeaves, WrapStatement.packed, leafHeadScalar, hb, hc]
  -- `x_hat`, chunk by chunk, reads as the wire's public commitment, crossed to `C.E`
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
  have hivp := incrementallyVerifyProof_reads S σ cvk cp _ endo sqrtF false blindingH
    spongeAfterIndex _ (cells.withClaims u) oldsW hXhat hivp
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
    exact ⟨o, hivp', rfl, hdig, hall⟩

end Read

section StepRead

/-- **`verify` reads as the group half on the step side**: `verifyProof_reads` at `stepSide`
and `pastaShapePallas`. -/
theorem verifyProof_step_reads {nc : ℕ} {V : Valuation Fp}
    (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc σ.k)
    (endo : FVar Fp) (sqrtF : Fp → Option Fp) (blindingH : AffinePoint (FVar Fp))
    (tab : XhatTable Fp nc) (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof σ.k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput σ.k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (base : Bool) (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads V isBaseCase base)
    (htab : tab.Bound pastaShapePallas V σ cvk blindingH (packLeaves statement tab))
    (hivp : IvpHyps (stepSide V) σ cvk cp (pubOf IpaPallas.curve V (packLeaves statement tab))
      false blindingH spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    verifyProof (c := Builder V (KimchiConstraint Fp)) IpaScalarOps.step IpaEndo.pallas
      IpaPallas.curve.sponge.params endo groupMapParamsPallas sqrtF blindingH tab
      spongeAfterIndex isBaseCase statement u cells
    ⦃⇓ v _ => ⌜VerifyReads (stepSide V) σ cvk cp
      (pubOf IpaPallas.curve V (packLeaves statement tab)) cells u base v⌝⦄ :=
  verifyProof_reads (stepSide V) pastaShapePallas σ cvk cp endo sqrtF blindingH tab
    spongeAfterIndex
    isBaseCase statement u cells base oldsW hbase htab hivp

end StepRead

/-! The gadget is sealed after its read: a consumer composes `verifyProof_step_reads`, never the
body. -/
attribute [irreducible] verifyProof

end Pickles
