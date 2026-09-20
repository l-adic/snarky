import Pickles.StepScalarHalf
import Pickles.WrapVerify
import Snarky.Compile

/-!
# A step proof is verified by its two circuits

The top-level statement for a step proof (Vesta commitments): a valuation satisfying the wrap
circuit's verify block, a valuation satisfying the next step circuit's scalar half with its
`finalized` bit set, the readings of their inputs as the wire's proof, and the ties between
them, make the deployed verifier accept.

`kimchiVerify` accepts exactly when its guards hold, the opening's Schnorr equation holds at
the run's own scalars, and `sg` is the challenge polynomial's commitment
(`kimchiVerify_reflects`, `verifyWith`). The group circuit proves the equation at the claimed
scalars; the scalar circuit proves the claimed scalars are the run's; the ties say the two
circuits speak of one set of claims. The guards are the environment's, and the `sg` equation
is the one check no circuit performs — pickles defers it to the next proof's accumulator
(`SgOk`, `sgOk_iff_accOk`).

The two halves run in different circuits over different fields, so neither is a triple's
program here: each is compiled (`Snarky.compile`) over its input and appears as its
constraint system, satisfied by its own valuation — what a triple unfolds to
(`builder_spec_iff`). An input's check is among the compiled rows, so the mask's booleanity
is a consequence of satisfaction, as it is in `Step.Main`, which checks the branch data where
it allocates it.

## The hypotheses

* `InputReads`: the input cells that hold the wire's objects read as them — the step
  statement as the public input, the proof cells as the proof, the accumulator cells as the
  old accumulators, the evaluation cells as the evaluations, the branch's domain as the key's;
* `VkReads`: the circuit's key cells read as the key;
* `HalvesTies`: the two circuits hold one set of deferred claims;
* what no circuit enforces, each its own hypothesis: the shifted claims avoid the ladder's
  band (`hclaimOk`) and the statement's scalars the `x_hat` band (`hoff`), the `ζ` powers are
  the run's (`hzetaM`, `hzetaN`). The permutation scalar is no hypothesis: the scalar circuit
  compares it at the transcript's challenges, which the group read gives before it opens
  (`IvpReads`), and `HalvesTies.perm` carries it across the field crossing;
* `Guards` and `SgOk`, of the proof itself.

The layered hypotheses the halves' reads consume (`IvpHyps`, `IvpTies`, `FopTies`) are built
from these in the proof; the shape guards among them (`mask`, `canon`, `nc_pos`, `t_ne`,
`lr_ne`, `char`) are proved — `lr_ne` from the environment's `rounds_pos`.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

namespace StepProof

/-- The group circuit's input cells: fixed by the input type. -/
abbrev groupInput (k kw n : ℕ) : GroupVar k kw n := inputVar (F := Fq) (a := GroupIn k kw n)

/-- The scalar circuit's input cells: fixed by the input type. -/
abbrev scalarInput (k : ℕ) : ScalarVar k := inputVar (F := Fp) (a := ScalarIn k)

section Hyp

variable {kw n : ℕ}

/-- The input cells that hold the wire's objects read as them: the step statement as the
public input, the proof cells as the proof's commitments and opening, the `sg` cells under
their keep bits as the old accumulators' commitments; the branch's domain as the key's, the
evaluation cells as the proof's evaluations, the kept previous challenges as the old
accumulators'. -/
structure InputReads (E : Env IpaVesta.curve) (cp : KimchiProof IpaVesta.curve 1 E.σ.k)
    (pub : Array Fp) (domains : KnownDomains E) (Vg : Valuation Fq) (Vs : Valuation Fp)
    (g : GroupVar E.σ.k kw n) (s : ScalarVar E.σ.k) : Prop where
  /-- The step statement's cells are the public input. -/
  statement : wrapPublicInput E Vg g.stepStatement = pub
  /-- The witness commitments. -/
  w : ColumnsRead IpaVesta.curve Vg g.wComm cp.wComm.toList
  /-- The permutation accumulator's commitment. -/
  z : CommReads IpaVesta.curve Vg g.zComm cp.zComm.toList
  /-- The quotient chunks. -/
  t : CommReads IpaVesta.curve Vg g.tComm cp.tComm.toList
  /-- The opening's `(L, R)` pairs. -/
  lr : List.Forall₂ (PairReads IpaVesta.curve.E.toAffine Vg) g.opening.lr.toList
    (cp.opening.lr.toList.map fun q =>
      (SWPoint.equivPoint IpaVesta.curve.E q.1, SWPoint.equivPoint IpaVesta.curve.E q.2))
  /-- The opening's `δ`. -/
  delta : OnCurveAt IpaVesta.curve.E.toAffine Vg g.opening.delta
    (SWPoint.equivPoint IpaVesta.curve.E cp.opening.delta)
  /-- The opening's `sg`. -/
  sg : OnCurveAt IpaVesta.curve.E.toAffine Vg g.opening.sg
    (SWPoint.equivPoint IpaVesta.curve.E cp.opening.sg)
  /-- The opening's `z₁`. -/
  z1 : (wrapSide Vg).decode g.opening.z1 = cp.opening.z1
  /-- The opening's `z₂`. -/
  z2 : (wrapSide Vg).decode g.opening.z2 = cp.opening.z2
  /-- The `sg` cells under their keep bits; the kept ones are the old accumulators'. -/
  olds : ∃ oldsW : List (IpaVesta.curve.Point × Bool),
    List.Forall₂ (MaskedBaseReads IpaVesta.curve.E.toAffine Vg) (g.sgOld.map fun m => (m.2, m.1))
      (oldsW.map fun b => (SWPoint.equivPoint IpaVesta.curve.E b.1, b.2)) ∧
    (oldsW.filter (·.2)).map (·.1) = (cp.olds.map (·.sg)).toList
  /-- The branch's domain is the key's. -/
  domain : s.branch.domainLog2.val Vs = (domains.keyLog2 : Fp)
  /-- `ft(ζω)`. -/
  ftEval1 : s.evals.ftEval1.val Vs = cp.ftEval1
  /-- The proof's evaluations, as its one-chunk vectors. -/
  evals : s.evals.evals.map (fun x => #v[x.val Vs]) = cp.evals
  /-- The public evaluations are the run's (`runPubEvals`). -/
  pubEvals : s.evals.pub.map (fun x => #v[x.val Vs])
    = runPubEvals IpaVesta.curve E.σ E.cvk cp pub
  /-- The kept previous challenges are the old accumulators', in order. -/
  prevChallenges : (List.zipWith (fun m cv => if m then [cv] else []) (s.half Vs).maskVals
      (s.half Vs).prevVals).flatten = (cp.olds.map (·.u.toList)).toList

variable {E : Env IpaVesta.curve} {cp : KimchiProof IpaVesta.curve 1 E.σ.k} {pub : Array Fp}
  {domains : KnownDomains E} {Vg : Valuation Fq} {Vs : Valuation Fp}
  {g : GroupVar E.σ.k kw n} {s : ScalarVar E.σ.k}
  {keyCells : List (List (AffinePoint (FVar Fq)))} {spongeAfterIndex : SpongeVar Fq}

/-- The scalar half's proof ties are the input's readings. -/
private theorem InputReads.fopTies (hin : InputReads E cp pub domains Vg Vs g s) :
    FopTies E cp pub (s.half Vs) :=
  ⟨hin.prevChallenges, hin.ftEval1, hin.evals, hin.pubEvals⟩

/-- The base field's characteristic exceeds the group half's absorb count. -/
private theorem char_guard (m : ℕ) (hm : m ≤ 53) (h0 : (m : Fq) = 0) : m = 0 := by
  have hd : PALLAS_SCALAR_CARD ∣ m := (ZMod.natCast_eq_zero_iff m PALLAS_SCALAR_CARD).mp h0
  exact Nat.eq_zero_of_dvd_of_lt hd (lt_of_le_of_lt hm (by norm_num [PALLAS_SCALAR_CARD]))

private theorem length_flatten_singletons {α : Type} (l : List α) :
    (l.map ([·])).flatten.length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simpa using ih

private theorem sgOld_length_le (g : GroupVar E.σ.k kw n) : g.sgOld.length ≤ 2 := by
  simp only [GroupVar.sgOld, List.length_map, List.length_zip, List.length_drop,
    Vector.length_toList, MaxProofsVerified]
  omega

/-- The group half's hypotheses: the readings from `InputReads` and `VkReads`, the claims no
circuit enforces from their own hypotheses, the shape guards proved — every `sg` cell carries
a keep bit, the claim is canonical on the wrap side, one chunk, seven quotient chunks, a round,
and at most `53` absorbed cells. -/
private theorem InputReads.ivpHyps (hin : InputReads E cp pub domains Vg Vs g s)
    (hvk : VkReads E.cvk Vg spongeAfterIndex keyCells)
    (hclaimOk : ∀ x ∈ g.shifted, (wrapSide Vg).ClaimOk x) :
    ∃ oldsW, IvpHyps (wrapSide Vg) E.σ E.cvk cp pub true spongeAfterIndex
      ((g.cells keyCells).withClaims g.claims) oldsW := by
  have hc : (g.cells keyCells).withClaims g.claims = g.cells keyCells := rfl
  rw [hc]
  obtain ⟨oldsW, holds, hkept⟩ := hin.olds
  refine ⟨oldsW,
    { idx := hvk.idx, mask := ?mask
      ties :=
        { olds := holds, olds_kept := hkept, w := hin.w, z := hin.z, t := hin.t
          index := hvk.index, coefficients := hvk.coefficients, sigma := hvk.sigma
          sigmaLast := hvk.sigmaLast, z1 := hin.z1, z2 := hin.z2, claimOk := hclaimOk
          lr := hin.lr, delta := hin.delta, sg := hin.sg }
      canon := trivial, nc_pos := Nat.one_pos, t_ne := ?tne, lr_ne := ?lrne, char := ?char }⟩
  case mask =>
    intro m hm
    have hm' : m ∈ g.sgOld := hm
    simp only [GroupVar.sgOld, List.mem_map] at hm'
    obtain ⟨q, -, rfl⟩ := hm'
    rfl
  case tne =>
    intro he
    have he' : g.tComm = [] := he
    simpa [GroupVar.tComm] using congrArg List.length he'
  case lrne =>
    intro he
    have he' : g.opening.lr.toList = [] := he
    have hlen := congrArg List.length he'
    rw [Vector.length_toList, List.length_nil] at hlen
    exact absurd hlen (Nat.pos_iff_ne_zero.mp E.rounds_pos)
  case char =>
    intro m hm h0
    refine char_guard m (le_trans hm ?_) h0
    have h1 : (g.cells keyCells).sgOld.length ≤ 2 := sgOld_length_le g
    have h2 : (g.cells keyCells).wComm.flatten.length = 15 := by
      show g.wComm.flatten.length = 15
      rw [GroupVar.wComm, length_flatten_singletons, Vector.length_toList]
    have h3 : (g.cells keyCells).zComm.length = 1 := rfl
    have h4 : (g.cells keyCells).tComm.length = 7 := by
      show g.tComm.length = 7
      simp [GroupVar.tComm]
    omega

end Hyp

end StepProof

open StepProof in
/-- **A step proof's two circuits, satisfied, make `kimchiVerify` accept.** The wrap circuit's
verify block and the step circuit's scalar half, each compiled over its input and satisfied,
with the inputs reading as the wire's proof (`InputReads`), the key cells as the key
(`VkReads`) and the two circuits holding one set of deferred claims (`HalvesTies`): under the
proof's `Guards` and `SgOk`, and what no circuit enforces, `kimchiVerify` accepts. -/
theorem stepProof_kimchiVerify_vesta {kw n : ℕ}
    (E : Env IpaVesta.curve)
    (cp : KimchiProof IpaVesta.curve 1 E.σ.k)
    (pub : Array Fp)
    (domains : KnownDomains E)
    -- the group circuit's constants
    (keyCells : List (List (AffinePoint (FVar Fq))))
    (spongeAfterIndex : SpongeVar Fq)
    (msgSponge : SpongeVar Fq)
    -- the group circuit: the wrap verify block, compiled over its input, satisfied
    (Vg : Valuation Fq)
    (hsatG : ∀ con ∈ (compile (a := GroupIn E.σ.k kw n) (b := Unit)
        (groupCircuit (c := Builder Vg (KimchiConstraint Fq)) E keyCells spongeAfterIndex
          msgSponge)).constraints, ConstraintHolds.Holds Vg con)
    -- the scalar circuit: the step finalize, compiled over its input, satisfied
    (Vs : Valuation Fp)
    (hsatS : ∀ con ∈ (compile (a := ScalarIn E.σ.k) (b := Unit)
        (scalarCircuit (c := Builder Vs (KimchiConstraint Fp)) E domains)).constraints,
        ConstraintHolds.Holds Vs con)
    -- the input cells read as the wire's
    (hin : InputReads E cp pub domains Vg Vs (groupInput E.σ.k kw n) (scalarInput E.σ.k))
    -- the key cells read as the key
    (hvk : VkReads E.cvk Vg spongeAfterIndex keyCells)
    -- the two circuits hold one set of deferred claims
    (ht : HalvesTies ((groupInput E.σ.k kw n).half Vg) ((scalarInput E.σ.k).half Vs))
    -- what no circuit enforces
    (hclaimOk : ∀ x ∈ (groupInput E.σ.k kw n).shifted, (wrapSide Vg).ClaimOk x)
    (hoff : ∀ leaf ∈ wrapLeavesAt E (groupInput E.σ.k kw n).stepStatement,
      Leaf.offBand IpaVesta.curve.scalar Vg leaf)
    (hzetaM : (wrapSide Vg).decode
        (groupInput E.σ.k kw n).claims.deferredValues.plonk.zetaToSrsLength
      = runZetaM IpaVesta.curve E.σ E.cvk cp pub)
    (hzetaN : (wrapSide Vg).decode
        (groupInput E.σ.k kw n).claims.deferredValues.plonk.zetaToDomainSize
      = runZetaN IpaVesta.curve E.σ E.cvk cp pub)
    -- of the proof itself
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    (hsg : SgOk E cp pub) :
    kimchiVerify IpaVesta.curve E.σ E.cvk cp pub = true := by
  have hpub := hin.statement
  have hivp := hin.ivpHyps (keyCells := keyCells) (spongeAfterIndex := spongeAfterIndex) hvk
    hclaimOk
  have hf := hin.fopTies
  have hdom := hin.domain
  subst hpub
  obtain ⟨v, hv, hv1⟩ := (builder_spec_iff _ _).mp
    (wrapVerifyAt_reads (V := Vg) E cp (groupInput E.σ.k kw n).stepStatement
      spongeAfterIndex msgSponge (groupInput E.σ.k kw n).newBp (groupInput E.σ.k kw n).msgDigest
      (groupInput E.σ.k kw n).claims ((groupInput E.σ.k kw n).cells keyCells) hoff hivp) _
    fun con hc => hsatG con (mem_compile_of_mem_body hc)
  have hmask := BranchData.mask_boolean (V := Vs) (scalarInput E.σ.k).branch
    (CheckedType.check_sound Vs (scalarInput E.σ.k) _
      fun con hc => hsatS con (mem_compile_of_mem_check hc)).1
  exact (builder_spec_iff _ _).mp
    (scalarCircuit_reads E cp _ hguard Vs domains (scalarInput E.σ.k) hmask hdom Vg _ v hv hv1
      ht hf hzetaM hzetaN hsg) _
    fun con hc => hsatS con (mem_compile_of_mem_body hc)

end Pickles
