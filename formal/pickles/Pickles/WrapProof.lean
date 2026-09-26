import Kimchi.Columns
import Pickles.StepGroupHalf
import Pickles.WrapScalarHalf
import Pickles.Encoding
import Snarky.Compile
import Pickles.ListLemmas

/-!
# A wrap proof is verified by its two circuits

The top-level statement for a wrap proof (Pallas commitments), the twin of
`stepProof_kimchiVerify_vesta`: a valuation satisfying the step circuit's `verify`, a valuation
satisfying the next wrap circuit's scalar half with its `finalized` bit set, the readings of
their inputs as the wire's proof, and the ties between them, make the deployed verifier accept.

The two halves run in different circuits over different fields, so each is compiled
(`Snarky.compile`) over its input and appears as its constraint system, satisfied by its own
valuation (`builder_spec_iff`).

## The hypotheses

* `WrapProof.InputReads`: the input cells read as the wire's objects — the wrap statement as
  the public input, the slot as one that must verify, the proof cells as the proof, the `sg`
  cells as the old accumulators, the evaluation cells as the evaluations;
* `VkReads`: the circuit's key cells read as the key;
* `SplitClaimsCast`: the wrap circuit's claim cells hold the step circuit's, lifted into the
  wrap field — what the statement carries between them; that the two circuits then hold one
  set of deferred claims (`HalvesTies`) is derived;
* no hypothesis where a circuit enforces it: the three scalars `ftComm` scales by, which the
  scalar circuit checks and the cast carries over; the claimed `cip` absorbing as its
  canonical representative, which its own ladder (`scaleByCip`) pins; and the parity cells
  of the split shifted claims, which the group circuit asserts boolean
  (`assertClaimBitsStep`);
* `havoid`: the SRS avoids the public-input relations (`SRS.Avoids`, `stepRelationsAt`). The
  Lagrange points and each chunk of the correction sum the fold adds are commitments against
  the SRS, finite exactly when the SRS has no relation at their coefficient vectors, which no
  invariant gives;
* `hsmall`: the wrap statement packs no more leaves than the SRS has points, so each chunk of
  the correction sum has nonzero coefficients;
* `Guards` and `SgOk`, of the proof itself.

Unlike the step proof's statement, there is no domain cell (the wrap circuit's domain is a
constant) and every `sg` slot is kept. The layered hypotheses the halves' reads consume
(`IvpHyps`, `IvpTies`, `FopTies`) are built from these in the proof; the shape guards among
them (`mask`, `nc_pos`, `t_ne`, `lr_ne`, `char`) are proved.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open scoped Kimchi

namespace WrapProof

variable {ks nc : ℕ}

/-- The group circuit's input cells. -/
abbrev groupInput (ks k nc : ℕ) : GroupVar ks k nc := inputVar (F := Fp) (a := GroupIn ks k nc)
/-- The scalar circuit's input cells. -/
abbrev scalarInput (k nc : ℕ) : ScalarVar k nc := inputVar (F := Fq) (a := ScalarIn k nc)

/-! ## The hypotheses, and the statement -/

/-- The input cells that hold the wire's objects read as them: the wrap statement as the
public input, the slot as one that must verify, the proof cells as the proof's commitments and
opening, the `sg` cells as the old accumulators' commitments; the evaluation cells as the
proof's evaluations, the previous challenges as the old accumulators'. -/
structure InputReads (E : Env IpaPallas.curve nc) (cp : KimchiProof IpaPallas.curve nc E.σ.k)
    (pub : Array Fq) (Vg : Valuation Fp) (Vs : Valuation Fq)
    (g : GroupVar ks E.σ.k nc) (s : ScalarVar E.σ.k nc) : Prop where
  /-- The wrap statement's cells are the public input. -/
  statement : stepPublicInput E Vg g.statement = pub
  /-- The slot must verify: its base-case bit reads `false`. -/
  mustVerify : CircuitType.Reads Vg g.isBaseCase false
  /-- The proof's cells read as the proof's. -/
  proof : ProofReads (stepSide Vg) g.wComm g.zComm g.tComm g.opening cp
  /-- The `sg` cells are the old accumulators', every slot kept. -/
  olds : CommReads IpaPallas.curve Vg g.sgOld (cp.olds.map (·.sg)).toList
  /-- `ft(ζω)`. -/
  ftEval1 : s.evals.ftEval1.val Vs = cp.ftEval1
  /-- The proof's evaluations, chunk by chunk. -/
  evals : s.evals.evals.map (fun v => v.map (·.val Vs)) = cp.evals
  /-- The public evaluations are the run's (`runPubEvals`), chunk by chunk. -/
  pubEvals : s.evals.pub.map (fun v => v.map (·.val Vs))
    = runPubEvals IpaPallas.curve E.σ E.cvk cp pub
  /-- The previous challenges are the old accumulators', in order. -/
  prevChallenges : (List.zipWith (fun m cv => if m then [cv] else []) (s.half Vs).maskVals
      (s.half Vs).prevVals).flatten = (cp.olds.map (·.u.toList)).toList

variable {E : Env IpaPallas.curve nc} {cp : KimchiProof IpaPallas.curve nc E.σ.k}
  {pub : Array Fq} {Vg : Valuation Fp} {Vs : Valuation Fq}
  {g : GroupVar ks E.σ.k nc} {s : ScalarVar E.σ.k nc}
  {keyCells : VkComms nc (AffinePoint (FVar Fp))} {spongeAfterIndex : SpongeVar Fp}

/-- The scalar half's proof ties are the input's readings. -/
private theorem InputReads.fopTies (hin : InputReads E cp pub Vg Vs g s) :
    FopTies E cp pub (s.half Vs) :=
  ⟨hin.prevChallenges, hin.ftEval1, hin.evals, hin.pubEvals⟩

/-- The group half's hypotheses, from the readings (`InputReads`, `VkReads`) and the shifted
claims' `IvpSide.ClaimOk`, with the shape guards proved. -/
private theorem InputReads.ivpHyps (hin : InputReads E cp pub Vg Vs g s)
    (hvk : VkReads E.cvk Vg spongeAfterIndex keyCells)
    (hclaimOk : ∀ x ∈ g.shifted, (stepSide Vg).ClaimOk x) :
    ∃ oldsW, IvpHyps (stepSide Vg) E.σ E.cvk cp pub false spongeAfterIndex
      ((g.cells keyCells).withClaims g.claims) oldsW :=
  ivpHyps_of_reads g.claims g.sgOld g.val.proof (by simp [GroupVar.sgOld, MaxProofsVerified])
    hin.proof hin.olds hvk hclaimOk

end WrapProof

open WrapProof in
/-- **A wrap proof's two circuits, satisfied, make `kimchiVerify` accept.** The step circuit's
`verify` and the wrap circuit's scalar half, each compiled over its input and satisfied, with
the inputs reading as the wire's proof (`InputReads`), the key cells as the key (`VkReads`)
and the wrap circuit's claim cells holding the step circuit's (`SplitClaimsCast`): under the
proof's `Guards` and `SgOk`, and what no circuit enforces, `kimchiVerify` accepts. -/
theorem wrapProof_kimchiVerify_pallas {ks nc : ℕ}
    (E : Env IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc E.σ.k)
    (pub : Array Fq)
    -- the group circuit's constants
    (keyCells : VkComms nc (AffinePoint (FVar Fp)))
    (spongeAfterIndex : SpongeVar Fp)
    -- the group circuit: the step circuit's verify, compiled over its input, satisfied
    (Vg : Valuation Fp)
    (hsatG : ∀ con ∈ (compile (a := GroupIn ks E.σ.k nc) (b := Unit)
        (groupCircuit (c := Builder Vg (KimchiConstraint Fp)) E keyCells
          spongeAfterIndex)).constraints, ConstraintHolds.Holds Vg con)
    -- the scalar circuit: the wrap finalize, compiled over its input, satisfied
    (Vs : Valuation Fq)
    (hsatS : ∀ con ∈ (compile (a := ScalarIn E.σ.k nc) (b := Unit)
        (scalarCircuit (c := Builder Vs (KimchiConstraint Fq)) E)).constraints,
        ConstraintHolds.Holds Vs con)
    -- the input cells read as the wire's
    (hin : InputReads E cp pub Vg Vs (groupInput ks E.σ.k nc) (scalarInput E.σ.k nc))
    -- the key cells read as the key
    (hvk : VkReads E.cvk Vg spongeAfterIndex keyCells)
    -- the wrap circuit's claim cells hold the step circuit's, lifted into the wrap field
    (hc : SplitClaimsCast Vg (groupInput ks E.σ.k nc).claims Vs (scalarInput E.σ.k nc).claims)
    -- the statement packs no more leaves than the SRS has points, and the SRS avoids the
    -- public-input relations
    (hsmall : (groupInput ks E.σ.k nc).statement.packed.length ≤ 2 ^ E.σ.k)
    (havoid : E.σ.Avoids (stepRelationsAt E (groupInput ks E.σ.k nc).statement))
    -- of the proof itself
    (hguard : Guards IpaPallas.curve E.cvk cp pub)
    (hsg : SgOk E.σ E.cvk cp pub) :
    kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true := by
  have hpub := hin.statement
  have hivp := hin.ivpHyps (keyCells := keyCells) (spongeAfterIndex := spongeAfterIndex) hvk
  have hf := hin.fopTies
  have hbase := hin.mustVerify
  subst hpub
  obtain ⟨v, hv, hv1⟩ := (builder_spec_iff _ _).mp
    (groupCircuit_reads (V := Vg) E cp keyCells spongeAfterIndex (groupInput ks E.σ.k nc) hbase
      hsmall havoid hivp) _
    fun con hc => hsatG con (mem_compile_of_mem_body hc)
  exact (builder_spec_iff _ _).mp
    (scalarCircuit_reads E cp _ hguard Vs (scalarInput E.σ.k nc) Vg _ v hv hv1 hc hf hsg) _
    fun con hc => hsatS con (mem_compile_of_mem_body hc)

end Pickles
