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

* `WrapProof.InputReads`: the input cells that hold the wire's objects read as them — the wrap
  statement as the public input, the slot as one that must verify, the proof cells as the
  proof, the `sg` cells as the old accumulators, the evaluation cells as the evaluations;
* `VkReads`: the circuit's key cells read as the key;
* `HalvesTies`: the two circuits hold one set of deferred claims;
* what is no hypothesis, because a circuit enforces it: the three scalars `ft_comm` scales by
  (the scalar circuit compares each, `HalvesTies` carries them over); the claimed `cip`
  absorbing as its canonical representative (its own ladder, `scaleByCip`, pins the half one
  bit narrower); and the ladder's band, which the group circuit asserts on the cells it
  scales — the shifted claims and the `x_hat` full leaves (`Pickles.LadderBand`), an assertion
  of this harness rather than of the shared gadget;
* `havoid`: the SRS avoids the `x_hat` relations (`SRS.Avoids`, `stepRelationsAt`). The table
  is computed from the key (`xhatTableAt`), and its points are commitments against the SRS;
  that the Lagrange points and the constant correction sum the fold adds are finite points
  is that the SRS has no relation at their coefficient vectors, which no invariant gives;
* `Guards` and `SgOk`, of the proof itself.

Against the step proof's statement: no domain cell (the wrap circuit's domain is a constant)
and every `sg` slot kept. The layered hypotheses the halves' reads consume (`IvpHyps`,
`IvpTies`, `FopTies`) are built from these in the proof; the shape guards among them (`mask`,
`nc_pos`, `t_ne`, `lr_ne`, `char`) are proved.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

namespace WrapProof

variable {ks : ℕ}

/-- The group circuit's input cells. -/
abbrev groupInput (ks k : ℕ) : GroupVar ks k := inputVar (F := Fp) (a := GroupIn ks k)
/-- The scalar circuit's input cells. -/
abbrev scalarInput (k : ℕ) : ScalarVar k := inputVar (F := Fq) (a := ScalarIn k)

/-! ## The hypotheses, and the statement -/

/-- The input cells that hold the wire's objects read as them: the wrap statement as the
public input, the slot as one that must verify, the proof cells as the proof's commitments and
opening, the `sg` cells as the old accumulators' commitments; the evaluation cells as the
proof's evaluations, the previous challenges as the old accumulators'. -/
structure InputReads (E : Env IpaPallas.curve 1) (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
    (pub : Array Fq) (Vg : Valuation Fp) (Vs : Valuation Fq)
    (g : GroupVar ks E.σ.k) (s : ScalarVar E.σ.k) : Prop where
  /-- The wrap statement's cells are the public input. -/
  statement : stepPublicInput E Vg g.statement = pub
  /-- The slot must verify: `is_base_case` reads `false`. -/
  mustVerify : CircuitType.Reads Vg g.isBaseCase false
  /-- The witness commitments. -/
  w : ColumnsRead IpaPallas.curve Vg g.wComm cp.wComm.toList
  /-- The permutation accumulator's commitment. -/
  z : CommReads IpaPallas.curve Vg g.zComm cp.zComm.toList
  /-- The quotient chunks. -/
  t : CommReads IpaPallas.curve Vg g.tComm cp.tComm.toList
  /-- The opening's `(L, R)` pairs. -/
  lr : List.Forall₂ (PairReads IpaPallas.curve.E.toAffine Vg) g.opening.lr.toList
    (cp.opening.lr.toList.map fun q =>
      (SWPoint.equivPoint IpaPallas.curve.E q.1, SWPoint.equivPoint IpaPallas.curve.E q.2))
  /-- The opening's `δ`. -/
  delta : OnCurveAt IpaPallas.curve.E.toAffine Vg g.opening.delta
    (SWPoint.equivPoint IpaPallas.curve.E cp.opening.delta)
  /-- The opening's `sg`. -/
  sg : OnCurveAt IpaPallas.curve.E.toAffine Vg g.opening.sg
    (SWPoint.equivPoint IpaPallas.curve.E cp.opening.sg)
  /-- The opening's `z₁`. -/
  z1 : (stepSide Vg).decode g.opening.z1 = cp.opening.z1
  /-- The opening's `z₂`. -/
  z2 : (stepSide Vg).decode g.opening.z2 = cp.opening.z2
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

variable {E : Env IpaPallas.curve 1} {cp : KimchiProof IpaPallas.curve 1 E.σ.k} {pub : Array Fq}
  {Vg : Valuation Fp} {Vs : Valuation Fq}
  {g : GroupVar ks E.σ.k} {s : ScalarVar E.σ.k}
  {keyCells : VkComms 1 (AffinePoint (FVar Fp))} {spongeAfterIndex : SpongeVar Fp}

/-- The scalar half's proof ties are the input's readings. -/
private theorem InputReads.fopTies (hin : InputReads E cp pub Vg Vs g s) :
    FopTies E cp pub (s.half Vs) :=
  ⟨hin.prevChallenges, hin.ftEval1, hin.evals, hin.pubEvals⟩

/-- The base field's characteristic exceeds the group half's absorb count. -/
private theorem char_guard (m : ℕ) (hm : m ≤ 53) (h0 : (m : Fp) = 0) : m = 0 := by
  have hd : PALLAS_BASE_CARD ∣ m := (ZMod.natCast_eq_zero_iff m PALLAS_BASE_CARD).mp h0
  exact Nat.eq_zero_of_dvd_of_lt hd (lt_of_le_of_lt hm (by norm_num [PALLAS_BASE_CARD]))

/-- The group half's hypotheses: the readings from `InputReads` and `VkReads`, what no circuit
enforces from its own hypotheses, the shape guards proved. -/
private theorem InputReads.ivpHyps (hin : InputReads E cp pub Vg Vs g s)
    (hvk : VkReads E.cvk Vg spongeAfterIndex keyCells)
    (hclaimOk : ∀ x ∈ g.shifted, (stepSide Vg).ClaimOk x) :
    ∃ oldsW, IvpHyps (stepSide Vg) E.σ E.cvk cp pub false spongeAfterIndex
      ((g.cells keyCells).withClaims g.claims) oldsW := by
  have hc : (g.cells keyCells).withClaims g.claims = g.cells keyCells := rfl
  rw [hc]
  refine ⟨(cp.olds.map (·.sg)).toList.map (·, true),
    { idx := hvk.idx, mask := ?mask
      ties :=
        { olds := ⟨?olds, ?kept⟩, w := hin.w, z := hin.z, t := hin.t
          key := hvk.key
          z1 := hin.z1, z2 := hin.z2, claimOk := hclaimOk
          lr := hin.lr, delta := hin.delta, sg := hin.sg }
      nc_pos := Nat.one_pos, t_ne := ?tne, lr_ne := ?lrne, char := ?char }⟩
  case mask =>
    intro m hm
    have hm' : m ∈ g.sgOld.map (none, ·) := hm
    simp only [List.mem_map] at hm'
    obtain ⟨q, -, rfl⟩ := hm'
    rfl
  case olds =>
    show List.Forall₂ (MaskedBaseReads IpaPallas.curve.E.toAffine Vg)
      ((g.sgOld.map (none, ·)).map fun m => (m.2, m.1)) _
    simp only [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hin.olds.imp fun _ _ h => ⟨h, rfl⟩
  case kept => simp [List.filter_map, Function.comp_def]
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
    have h1 : (g.cells keyCells).sgOld.length = 2 := by
      show (g.sgOld.map (none, ·)).length = 2
      simp [GroupVar.sgOld, MaxProofsVerified]
    have hl := ivpInputOf_lengths g.claims.deferredValues (g.sgOld.map (none, ·)) keyCells
      g.val.proof
    have h2 : (g.cells keyCells).wComm.flatten.length = 15 := hl.1
    have h3 : (g.cells keyCells).zComm.length = 1 := hl.2.1
    have h4 : (g.cells keyCells).tComm.length = 7 := hl.2.2
    omega

end WrapProof

open WrapProof in
/-- **A wrap proof's two circuits, satisfied, make `kimchiVerify` accept.** The step circuit's
`verify` and the wrap circuit's scalar half, each compiled over its input and satisfied, with
the inputs reading as the wire's proof (`InputReads`), the key cells as the key (`VkReads`)
and the two circuits holding one set of deferred claims (`HalvesTies`): under the proof's
`Guards` and `SgOk`, and what no circuit enforces, `kimchiVerify` accepts. -/
theorem wrapProof_kimchiVerify_pallas {ks : ℕ}
    (E : Env IpaPallas.curve 1)
    (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
    (pub : Array Fq)
    -- the group circuit's constants
    (keyCells : VkComms 1 (AffinePoint (FVar Fp)))
    (spongeAfterIndex : SpongeVar Fp)
    -- the group circuit: the step circuit's verify, compiled over its input, satisfied
    (Vg : Valuation Fp)
    (hsatG : ∀ con ∈ (compile (a := GroupIn ks E.σ.k) (b := Unit)
        (groupCircuit (c := Builder Vg (KimchiConstraint Fp)) E keyCells
          spongeAfterIndex)).constraints, ConstraintHolds.Holds Vg con)
    -- the scalar circuit: the wrap finalize, compiled over its input, satisfied
    (Vs : Valuation Fq)
    (hsatS : ∀ con ∈ (compile (a := ScalarIn E.σ.k) (b := Unit)
        (scalarCircuit (c := Builder Vs (KimchiConstraint Fq)) E)).constraints,
        ConstraintHolds.Holds Vs con)
    -- the input cells read as the wire's
    (hin : InputReads E cp pub Vg Vs (groupInput ks E.σ.k) (scalarInput E.σ.k))
    -- the key cells read as the key
    (hvk : VkReads E.cvk Vg spongeAfterIndex keyCells)
    -- the two circuits hold one set of deferred claims
    (ht : HalvesTies ((groupInput ks E.σ.k).half Vg) ((scalarInput E.σ.k).half Vs))
    -- the SRS has no relation at the `x_hat` table's coefficient vectors
    (havoid : E.σ.Avoids (stepRelationsAt E (groupInput ks E.σ.k).statement))
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
    (groupCircuit_reads (V := Vg) E cp keyCells spongeAfterIndex (groupInput ks E.σ.k) hbase
      havoid hivp) _
    fun con hc => hsatG con (mem_compile_of_mem_body hc)
  exact (builder_spec_iff _ _).mp
    (scalarCircuit_reads E cp _ hguard Vs (scalarInput E.σ.k) Vg _ v hv hv1 ht hf hsg) _
    fun con hc => hsatS con (mem_compile_of_mem_body hc)

end Pickles
