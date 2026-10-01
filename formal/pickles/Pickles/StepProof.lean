import Kimchi.Columns
import Pickles.StepScalarHalf
import Pickles.WrapVerify
import Snarky.Compile
import Pickles.ListLemmas

/-!
# A step proof is verified by its two circuits

The top-level statement for a step proof (Vesta commitments): a valuation satisfying the wrap
circuit's verify block, a valuation satisfying the next step circuit's scalar half with its
`finalized` bit set, the readings of their inputs as the wire's proof, and the ties between
them, make the deployed verifier accept.

The statement is about a slot that must verify: the scalar half asserts `finalized`. A base-case
slot has no proof to verify, and the deployed circuits accept it without one; their read over
every slot is `wrapStep_kimchiVerify`.

`kimchiVerify` accepts exactly when its guards hold, the opening's Schnorr equation holds at
the run's own scalars, and `sg` is the challenge polynomial's commitment
(`kimchiVerify_reflects`, `verifyWith`). The group circuit proves the equation at the claimed
scalars; the scalar circuit proves the claimed scalars are the run's; the ties say the two
circuits speak of one set of claims. The guards are the key's, and the `sg` equation
is the one check no circuit performs: it is deferred to the next proof's accumulator (`SgOk`).

The two halves run in different circuits over different fields, so each is compiled
(`Snarky.compile`) over its input and appears as its constraint system, satisfied by its own
valuation (`builder_spec_iff`). The input's check is among the compiled rows, so the mask's
booleanity follows from satisfaction (`BranchData.mask_boolean`).

## The hypotheses

* `StepProof.InputReads`: the input cells read as the wire's objects — the step statement as
  the public input, the proof cells as the proof, the `sg` cells as the old accumulators, the
  evaluation cells as the evaluations, the branch's domain as the key's;
* `VkReads`: the circuit's key cells read as the key;
* `ClaimsCast`: the wrap circuit's claim cells hold the step circuit's, reduced into the wrap
  field — what the statement carries between them; that the two circuits then hold one set of
  deferred claims (`HalvesTies`) is derived;
* no hypothesis where a circuit enforces it: the three scalars `ftComm` scales by, which the
  scalar circuit checks and the cast carries over. No scalar a ladder reads is excluded:
  every ladder top is below `4·order − 4` (`wrapSide_claimOk`);
* `havoid`: the SRS avoids the key's Lagrange relations (`SRS.Avoids`,
  `KimchiVK.lagrangeRelations`). The key's Lagrange points are commitments against the SRS, finite
  exactly when the SRS has no relation at their coefficient vectors, which no invariant gives;
* `Guards` and `SgOk`, of the proof itself.

The layered hypotheses the halves' reads consume (`IvpHyps`, `IvpTies`, `FopTies`) are built
from these in the proof; the shape guards among them (`mask`, `nc_pos`, `k_pos`,
`char`) are proved.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open scoped Kimchi

namespace StepProof

/-- The group circuit's input cells. -/
abbrev groupInput (k kw pad nc : ℕ) : GroupVar k kw pad nc :=
  inputVar (F := Fq) (a := GroupIn k kw pad nc)

/-- The scalar circuit's input cells. -/
abbrev scalarInput (k nc : ℕ) : ScalarVar k nc := inputVar (F := Fp) (a := ScalarIn k nc)

section Hyp

variable {kw pad nc : ℕ}

/-- The input cells that hold the wire's objects read as them: the step statement as the
public input, the proof cells as the proof's commitments and opening, the `sg` cells under
their keep bits as the old accumulators' commitments; the branch's domain as the key's, the
evaluation cells as the proof's evaluations, the kept previous challenges as the old
accumulators'. -/
structure InputReads (σ : SRS IpaVesta.curve.Point) (cvk : KimchiVK IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc σ.k)
    (pub : Array Fp) (domains : KnownDomains nc) (Vg : Valuation Fq) (Vs : Valuation Fp)
    (g : GroupVar σ.k kw pad nc) (s : ScalarVar σ.k nc) : Prop where
  /-- The step statement's cells are the public input. -/
  statement : wrapPublicInput σ cvk Vg g.stepStatement = pub
  /-- The proof's cells read as the proof's. -/
  proof : ProofReads (wrapSide Vg) g.wComm g.zComm g.tComm g.opening cp
  /-- The `sg` cells under their keep bits; the kept ones are the old accumulators'. -/
  olds : ∃ oldsW, OldsRead Vg g.sgOld cp oldsW
  /-- The branch's domain is the key's. -/
  domain : s.branch.domainLog2.val Vs = (cvk.domainLog2 : Fp)
  /-- `ft(ζω)`. -/
  ftEval1 : s.evals.ftEval1.val Vs = cp.ftEval1
  /-- The proof's evaluations, chunk by chunk. -/
  evals : s.evals.evals.map (fun v => v.map (·.val Vs)) = cp.evals
  /-- The public evaluations are the run's (`runPubEvals`), chunk by chunk. -/
  pubEvals : s.evals.pub.map (fun v => v.map (·.val Vs))
    = runPubEvals IpaVesta.curve σ cvk cp pub
  /-- The kept previous challenges are the old accumulators', in order. -/
  prevChallenges : (Vector.zipWith (fun m cv => if m then [cv] else []) (s.half Vs).maskVals
      (s.half Vs).prevVals).toList.flatten = (cp.olds.map (·.u)).toList

/-- The scalar half's proof ties are the input's readings. -/
private theorem InputReads.fopTies {σ : SRS IpaVesta.curve.Point}
    {cvk : KimchiVK IpaVesta.curve nc} {cp : KimchiProof IpaVesta.curve nc σ.k} {pub : Array Fp}
    {domains : KnownDomains nc} {Vg : Valuation Fq} {Vs : Valuation Fp}
    {g : GroupVar σ.k kw pad nc} {s : ScalarVar σ.k nc}
    (hin : InputReads σ cvk cp pub domains Vg Vs g s) : FopTies σ cvk cp pub (s.half Vs) :=
  ⟨hin.prevChallenges, hin.ftEval1, hin.evals, hin.pubEvals⟩

/-- The group half's hypotheses, from the readings (`InputReads`, `VkReads`), with the shifted
claims' `IvpSide.ClaimOk` and the shape guards proved (`ivpHyps_of_reads_wrap`). -/
private theorem InputReads.ivpHyps {S : Srs IpaVesta.curve} {K : Key IpaVesta.curve nc}
    {cp : KimchiProof IpaVesta.curve nc S.σ.k} {pub : Array Fp} {domains : KnownDomains nc}
    {Vg : Valuation Fq} {Vs : Valuation Fp} {g : GroupVar S.σ.k kw pad nc} {s : ScalarVar S.σ.k nc}
    {keyCells : VkComms nc (AffinePoint (FVar Fq))} {spongeAfterIndex : SpongeVar Fq}
    (hin : InputReads S.σ K.cvk cp pub domains Vg Vs g s)
    (hnc : nc = chunkCount S.σ.k K.cvk.domainLog2)
    (hvk : VkReads K.cvk Vg spongeAfterIndex keyCells) :
    ∃ oldsW, IvpHyps (wrapSide Vg) S.σ K.cvk cp pub true spongeAfterIndex
      ((g.cells keyCells).withClaims g.claims) oldsW := by
  obtain ⟨oldsW, holds⟩ := hin.olds
  refine ⟨oldsW, ivpHyps_of_reads_wrap hnc _ g.sgOld g.val.group.proof g.claims oldsW ?_
    (Nat.sub_le _ _) hin.proof holds hvk⟩
  intro m hm
  simp only [GroupVar.sgOld] at hm
  obtain ⟨q, -, rfl⟩ := Vector.mem_map.mp hm
  rfl

end Hyp

end StepProof

open StepProof in
/-- **A step proof's two circuits, satisfied, make `kimchiVerify` accept.** The wrap circuit's
verify block and the step circuit's scalar half, each compiled over its input and satisfied,
with the inputs reading as the wire's proof (`InputReads`), the key cells as the key
(`VkReads`) and the wrap circuit's claim cells holding the step circuit's (`ClaimsCast`): under the
proof's `Guards` and `SgOk`, and what no circuit enforces, `kimchiVerify` accepts. The slot must
verify; the base case is `wrapStep_kimchiVerify`'s. -/
theorem stepProof_kimchiVerify_vesta {kw pad nc : ℕ}
    (S : Srs IpaVesta.curve) (K : Key IpaVesta.curve nc)
    (hnc : nc = chunkCount S.σ.k K.cvk.domainLog2)
    (cp : KimchiProof IpaVesta.curve nc S.σ.k)
    (pub : Array Fp)
    (domains : KnownDomains nc)
    -- the group circuit's constants
    (keyCells : VkComms nc (AffinePoint (FVar Fq)))
    (spongeAfterIndex : SpongeVar Fq)
    (msgSponge : SpongeVar Fq)
    -- the group circuit: the wrap verify block, compiled over its input, satisfied
    (Vg : Valuation Fq)
    (hsatG : ∀ con ∈ (compile (a := GroupIn S.σ.k kw pad nc) (b := Unit)
        (groupCircuit (c := Builder Vg (KimchiConstraint Fq)) S.σ K.cvk keyCells spongeAfterIndex
          msgSponge)).constraints, ConstraintHolds.Holds Vg con)
    -- the scalar circuit: the step finalize, compiled over its input, satisfied
    (Vs : Valuation Fp)
    (hsatS : ∀ con ∈ (compile (a := ScalarIn S.σ.k nc) (b := Unit)
        (scalarCircuit (c := Builder Vs (KimchiConstraint Fp)) domains)).constraints,
        ConstraintHolds.Holds Vs con)
    -- the input cells read as the wire's
    (hin : InputReads S.σ K.cvk cp pub domains Vg Vs (groupInput S.σ.k kw pad nc)
      (scalarInput S.σ.k nc))
    -- the key cells read as the key
    (hvk : VkReads K.cvk Vg spongeAfterIndex keyCells)
    -- the wrap circuit's claim cells hold the step circuit's, reduced into the wrap field
    (hc : ClaimsCast Vg (groupInput S.σ.k kw pad nc).claims Vs (scalarInput S.σ.k nc).claims)
    -- the SRS avoids the key's Lagrange relations, one per packed scalar
    (havoid : S.σ.Avoids
      (K.cvk.lagrangeRelations S.σ.k (CircuitType.size Fp (StepStatement (UnfVal kw) Fp
        (MaxProofsVerified - pad)))))
    -- of the proof itself
    (hguard : Guards IpaVesta.curve K.cvk cp pub)
    (hsg : SgOk S.σ K.cvk cp pub) :
    kimchiVerify IpaVesta.curve S.σ K.cvk cp pub = true := by
  have hpub := hin.statement
  have hivp := hin.ivpHyps (keyCells := keyCells) (spongeAfterIndex := spongeAfterIndex) hnc hvk
  have hf := hin.fopTies
  have hdom := hin.domain
  subst hpub
  obtain ⟨v, hv, hv1⟩ := (builder_spec_iff _ _).mp
    (groupCircuit_reads (V := Vg) S K hnc cp keyCells spongeAfterIndex msgSponge
      (groupInput S.σ.k kw pad nc) havoid fun _ => hivp) _
    fun con hc => hsatG con (mem_compile_of_mem_body hc)
  have hmask := BranchData.mask_boolean (V := Vs) (scalarInput S.σ.k nc).branch
    (CheckedType.check_sound Vs (scalarInput S.σ.k nc) _
      fun con hc => hsatS con (mem_compile_of_mem_check hc)).1
  exact (builder_spec_iff _ _).mp
    (scalarCircuit_reads S K cp _ hguard Vs domains (scalarInput S.σ.k nc) hmask hdom Vg _ v hv hv1
      hc hf hsg) _
    fun con hc => hsatS con (mem_compile_of_mem_body hc)

end Pickles
