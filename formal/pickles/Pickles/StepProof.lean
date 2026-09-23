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

`kimchiVerify` accepts exactly when its guards hold, the opening's Schnorr equation holds at
the run's own scalars, and `sg` is the challenge polynomial's commitment
(`kimchiVerify_reflects`, `verifyWith`). The group circuit proves the equation at the claimed
scalars; the scalar circuit proves the claimed scalars are the run's; the ties say the two
circuits speak of one set of claims. The guards are the environment's, and the `sg` equation
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
* `HalvesTies`: the two circuits hold one set of deferred claims;
* no hypothesis where a circuit enforces it: the three scalars `ftComm` scales by, which the
  scalar circuit checks and `HalvesTies` carries over. No scalar a ladder reads is excluded:
  every ladder top is below `4·order − 4` (`wrapSide_claimOk`);
* `havoid`: the SRS avoids the key's Lagrange relations (`SRS.Avoids`,
  `Env.lagrangeRelations`). The key's Lagrange points are commitments against the SRS, finite
  exactly when the SRS has no relation at their coefficient vectors, which no invariant gives;
* `Guards` and `SgOk`, of the proof itself.

The layered hypotheses the halves' reads consume (`IvpHyps`, `IvpTies`, `FopTies`) are built
from these in the proof; the shape guards among them (`mask`, `nc_pos`, `t_ne`, `lr_ne`,
`char`) are proved.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open scoped Kimchi

namespace StepProof

/-- The group circuit's input cells. -/
abbrev groupInput (k kw n nc : ℕ) : GroupVar k kw n nc :=
  inputVar (F := Fq) (a := GroupIn k kw n nc)

/-- The scalar circuit's input cells. -/
abbrev scalarInput (k nc : ℕ) : ScalarVar k nc := inputVar (F := Fp) (a := ScalarIn k nc)

section Hyp

variable {kw n nc : ℕ}

/-- The input cells that hold the wire's objects read as them: the step statement as the
public input, the proof cells as the proof's commitments and opening, the `sg` cells under
their keep bits as the old accumulators' commitments; the branch's domain as the key's, the
evaluation cells as the proof's evaluations, the kept previous challenges as the old
accumulators'. -/
structure InputReads (E : Env IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc E.σ.k)
    (pub : Array Fp) (domains : KnownDomains E) (Vg : Valuation Fq) (Vs : Valuation Fp)
    (g : GroupVar E.σ.k kw n nc) (s : ScalarVar E.σ.k nc) : Prop where
  /-- The step statement's cells are the public input. -/
  statement : wrapPublicInput E Vg g.stepStatement = pub
  /-- The proof's cells read as the proof's. -/
  proof : ProofReads (wrapSide Vg) g.wComm g.zComm g.tComm g.opening cp
  /-- The `sg` cells under their keep bits; the kept ones are the old accumulators'. -/
  olds : ∃ oldsW, OldsRead Vg g.sgOld cp oldsW
  /-- The branch's domain is the key's. -/
  domain : s.branch.domainLog2.val Vs = (domains.keyLog2 : Fp)
  /-- `ft(ζω)`. -/
  ftEval1 : s.evals.ftEval1.val Vs = cp.ftEval1
  /-- The proof's evaluations, chunk by chunk. -/
  evals : s.evals.evals.map (fun v => v.map (·.val Vs)) = cp.evals
  /-- The public evaluations are the run's (`runPubEvals`), chunk by chunk. -/
  pubEvals : s.evals.pub.map (fun v => v.map (·.val Vs))
    = runPubEvals IpaVesta.curve E.σ E.cvk cp pub
  /-- The kept previous challenges are the old accumulators', in order. -/
  prevChallenges : (List.zipWith (fun m cv => if m then [cv] else []) (s.half Vs).maskVals
      (s.half Vs).prevVals).flatten = (cp.olds.map (·.u.toList)).toList

variable {E : Env IpaVesta.curve nc} {cp : KimchiProof IpaVesta.curve nc E.σ.k}
  {pub : Array Fp} {domains : KnownDomains E} {Vg : Valuation Fq} {Vs : Valuation Fp}
  {g : GroupVar E.σ.k kw n nc} {s : ScalarVar E.σ.k nc}
  {keyCells : VkComms nc (AffinePoint (FVar Fq))} {spongeAfterIndex : SpongeVar Fq}

/-- The scalar half's proof ties are the input's readings. -/
private theorem InputReads.fopTies (hin : InputReads E cp pub domains Vg Vs g s) :
    FopTies E cp pub (s.half Vs) :=
  ⟨hin.prevChallenges, hin.ftEval1, hin.evals, hin.pubEvals⟩

/-- A step key has at most `2^32` chunks: its domain size divides `|Fp| − 1`, whose two-adic
part is `2^32`, and the chunk count is at most the domain size. -/
private theorem nc_le (E : Env IpaVesta.curve nc) : nc ≤ 2 ^ 32 := by
  have hω0 : E.cvk.omega ≠ 0 := E.omega_prim.ne_zero (by rw [KimchiVK.n]; positivity)
  have hn : E.cvk.n ∣ PALLAS_BASE_CARD - 1 :=
    E.omega_prim.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one hω0)
  have hd : E.cvk.domainLog2 ≤ 32 := by
    by_contra h
    have h33 : 2 ^ 33 ∣ PALLAS_BASE_CARD - 1 :=
      (Nat.pow_dvd_pow 2 (show 33 ≤ E.cvk.domainLog2 by omega)).trans hn
    exact absurd h33 (by norm_num [PALLAS_BASE_CARD])
  calc nc ≤ E.cvk.n := E.nc_le_n
    _ = 2 ^ E.cvk.domainLog2 := rfl
    _ ≤ 2 ^ 32 := Nat.pow_le_pow_right two_pos hd

/-- The base field's characteristic exceeds the group half's absorb count. -/
private theorem char_guard (m : ℕ) (hm : m ≤ 5 + 48 * 2 ^ 32) (h0 : (m : Fq) = 0) : m = 0 := by
  have hd : PALLAS_SCALAR_CARD ∣ m := (ZMod.natCast_eq_zero_iff m PALLAS_SCALAR_CARD).mp h0
  exact Nat.eq_zero_of_dvd_of_lt hd (lt_of_le_of_lt hm (by norm_num [PALLAS_SCALAR_CARD]))

private theorem sgOld_length_le (g : GroupVar E.σ.k kw n nc) : g.sgOld.length ≤ 2 := by
  simp only [GroupVar.sgOld, List.length_map, List.length_zip, List.length_drop,
    Vector.length_toList, MaxProofsVerified]
  omega

/-- The group half's hypotheses, from the readings (`InputReads`, `VkReads`) and the shifted
claims' `IvpSide.ClaimOk`, with the shape guards proved. -/
private theorem InputReads.ivpHyps (hin : InputReads E cp pub domains Vg Vs g s)
    (hvk : VkReads E.cvk Vg spongeAfterIndex keyCells)
    (hclaimOk : ∀ x ∈ g.shifted, (wrapSide Vg).ClaimOk x) :
    ∃ oldsW, IvpHyps (wrapSide Vg) E.σ E.cvk cp pub true spongeAfterIndex
      ((g.cells keyCells).withClaims g.claims) oldsW := by
  have hc : (g.cells keyCells).withClaims g.claims = g.cells keyCells := rfl
  rw [hc]
  obtain ⟨oldsW, holds⟩ := hin.olds
  refine ⟨oldsW,
    { idx := hvk.idx, mask := ?mask
      ties :=
        { olds := holds, proof := hin.proof
          key := hvk.key
          claimOk := hclaimOk }
      nc_pos := E.nc_pos, t_ne := ?tne, lr_ne := ?lrne, char := ?char }⟩
  case mask =>
    intro m hm
    have hm' : m ∈ g.sgOld := hm
    simp only [GroupVar.sgOld, List.mem_map] at hm'
    obtain ⟨q, -, rfl⟩ := hm'
    rfl
  case tne =>
    intro he
    have he' : g.tComm = [] := he
    have hl := congrArg List.length he'
    simp [GroupVar.tComm] at hl
    exact E.nc_pos.ne' hl
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
    have hl := ivpInputOf_lengths g.val.group.statement.proofState.deferredValues.toDeferredValues
      g.sgOld keyCells g.val.group.proof
    have h2 : (g.cells keyCells).wComm.flatten.length = 15 * nc := hl.1
    have h3 : (g.cells keyCells).zComm.length = nc := hl.2.1
    have h4 : (g.cells keyCells).tComm.length = quotChunks * nc := hl.2.2
    have h5 := nc_le E
    omega

end Hyp

end StepProof

open StepProof in
/-- **A step proof's two circuits, satisfied, make `kimchiVerify` accept.** The wrap circuit's
verify block and the step circuit's scalar half, each compiled over its input and satisfied,
with the inputs reading as the wire's proof (`InputReads`), the key cells as the key
(`VkReads`) and the two circuits holding one set of deferred claims (`HalvesTies`): under the
proof's `Guards` and `SgOk`, and what no circuit enforces, `kimchiVerify` accepts. -/
theorem stepProof_kimchiVerify_vesta {kw n nc : ℕ}
    (E : Env IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc E.σ.k)
    (pub : Array Fp)
    (domains : KnownDomains E)
    -- the group circuit's constants
    (keyCells : VkComms nc (AffinePoint (FVar Fq)))
    (spongeAfterIndex : SpongeVar Fq)
    (msgSponge : SpongeVar Fq)
    -- the group circuit: the wrap verify block, compiled over its input, satisfied
    (Vg : Valuation Fq)
    (hsatG : ∀ con ∈ (compile (a := GroupIn E.σ.k kw n nc) (b := Unit)
        (groupCircuit (c := Builder Vg (KimchiConstraint Fq)) E keyCells spongeAfterIndex
          msgSponge)).constraints, ConstraintHolds.Holds Vg con)
    -- the scalar circuit: the step finalize, compiled over its input, satisfied
    (Vs : Valuation Fp)
    (hsatS : ∀ con ∈ (compile (a := ScalarIn E.σ.k nc) (b := Unit)
        (scalarCircuit (c := Builder Vs (KimchiConstraint Fp)) E domains)).constraints,
        ConstraintHolds.Holds Vs con)
    -- the input cells read as the wire's
    (hin : InputReads E cp pub domains Vg Vs (groupInput E.σ.k kw n nc) (scalarInput E.σ.k nc))
    -- the key cells read as the key
    (hvk : VkReads E.cvk Vg spongeAfterIndex keyCells)
    -- the two circuits hold one set of deferred claims
    (ht : HalvesTies ((groupInput E.σ.k kw n nc).half Vg) ((scalarInput E.σ.k nc).half Vs))
    -- the SRS avoids the key's Lagrange relations
    (havoid : E.σ.Avoids E.lagrangeRelations)
    -- of the proof itself
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    (hsg : SgOk E.σ E.cvk cp pub) :
    kimchiVerify IpaVesta.curve E.σ E.cvk cp pub = true := by
  have hpub := hin.statement
  have hivp := hin.ivpHyps (keyCells := keyCells) (spongeAfterIndex := spongeAfterIndex) hvk
  have hf := hin.fopTies
  have hdom := hin.domain
  subst hpub
  obtain ⟨v, hv, hv1⟩ := (builder_spec_iff _ _).mp
    (groupCircuit_reads (V := Vg) E cp keyCells spongeAfterIndex msgSponge
      (groupInput E.σ.k kw n nc) havoid hivp) _
    fun con hc => hsatG con (mem_compile_of_mem_body hc)
  have hmask := BranchData.mask_boolean (V := Vs) (scalarInput E.σ.k nc).branch
    (CheckedType.check_sound Vs (scalarInput E.σ.k nc) _
      fun con hc => hsatS con (mem_compile_of_mem_check hc)).1
  exact (builder_spec_iff _ _).mp
    (scalarCircuit_reads E cp _ hguard Vs domains (scalarInput E.σ.k nc) hmask hdom Vg _ v hv hv1
      ht hf hsg) _
    fun con hc => hsatS con (mem_compile_of_mem_body hc)

end Pickles
