import Pickles.IncrementallyVerify
import Pickles.FinalizeOtherProof
import Pickles.Verify
import Kimchi.Columns

/-!
# The two halves of one proof read as `kimchiVerify`

One kimchi proof `cp` of key `cvk` at public input `pub` is verified by two circuits over
the two fields of the cycle, in this order:

1. the **group half**, `incrementally_verify_proof`, over the base field, in the circuit that
   receives the proof (for a step proof: the wrap circuit). It scales by the claimed `cip`,
   `b`, `ξ` and returns whether the opening's Schnorr equation holds at them;
2. the **scalar half**, `finalize_other_proof`, over the scalar field, one circuit later (for
   a step proof: the next step circuit, over the deferred values the wrap statement carried).
   It recomputes `cip`, `b`, `ξ` and the permutation scalar from the evaluations and returns
   whether the claims are honest.

This module states the composition, with no circuit and no `mvcgen`: from the two reads
(`IvpReads`, `FopReadsWire`) and the ties between the two circuits' cells (`HalvesTies`),
the two bits reading `1` together with the deferred `sg`-correctness equation forces the
acceptance of `kimchiVerify` (`twoHalves_kimchiVerify`), and the two bits alone force the
wire's Schnorr equation at honest claims (`twoHalves_schnorr`); where the scalar half's `ξ`
comparison is exact (`ScalarHalf.XiExact`) both are equivalences (`twoHalves_kimchiVerify_iff`,
`twoHalves_iff_schnorr`).

## The arguments

Three kinds, kept apart:

* the **environment** `Env`: the SRS and the verifier key, shared by everything;
* the **proof**: `cp` and its public input `pub`, the wire objects `kimchiVerify` judges;
* the two **circuit halves**, `GroupHalf` then `ScalarHalf`: each a valuation, the side (the
  curve-dependent constants: decodes, tokens, group facts), the cells the circuit is given
  (its claims; on the scalar side also the evaluations, the mask and the previous
  challenges) and its output. The circuits are given cells, not the proof; the wire
  recomputes what the cells claim (`ClaimsHonest`), and the theorem is that the cells are
  forced to it. Everything else the scalar half is parameterized by is derived
  (`FopParams.ofKey`, the key's domain, the proof's recursion digest, the values from the
  cells through the side's decode).

## The direction

The circuit reads pin every 128-bit prechallenge to the wire's (`Low128.exact`) and the `U`
base to the wire's `uBase`, so the bits reading `1` force `kimchiVerify`'s acceptance. The
converse — the wire accepting at honest claims makes the bits read `1` — needs the `ξ`
comparison to be exact: `xiCorrect` compares the claim against the low half of a split of
the fr-sponge's squeeze, and only where the circuit range-checks that low half is the split
canonical. The step circuit does (`xiConstrainLowBits`), so at a step proof the statement
is an equivalence (`twoHalves_kimchiVerify_vesta`); the wrap circuit does not
(`squeezeScalar`), so at a wrap proof the converse is stated separately under
`ScalarHalf.XiExact` as a hypothesis (`twoHalves_kimchiVerify_pallas_converse`).

## What this is not

The chain: `sgOk` is a hypothesis here (pickles defers it to the next proof's batch
opening — `Carry` names the handover and `sgOk_iff_accOk` transports the equation), the
message digests are two entries of `pub` like any other, and the packing of statements across
the cycle is `verify`'s. This is the per-proof checkpoint, at one chunk.

## Main definitions

* `Env`, `GroupHalf`, `ScalarHalf`: the three kinds of argument;
* `FopSide`, `FopParams.ofEnv`: the scalar half's side and its parameters from the
  environment;
* `GroupHalf.Reads`, `ScalarHalf.Reads`: the circuit reads (`IvpReads`, `FopReadsWire`) at a
  half's own cells; `ScalarHalf.XiExact`: the `ξ` comparison exact at a half's cells, which
  the read gives where the side constrains the low half (`ScalarHalf.xiExact_of_constrained`);
* `HalvesTies`: the claim cells of the two halves read the same claims across the field
  crossing, the digest crosses as `castDigest`, the evaluations and old accumulators are the
  proof's.

## Main results

* `twoHalves_schnorr`: the two bits read `1` make the claims honest and the wire's Schnorr
  equation hold; `twoHalves_kimchiVerify`: with the deferred `sg` equation, they make
  `kimchiVerify` accept at honest claims; `twoHalves_iff_schnorr`, `twoHalves_kimchiVerify_iff`:
  the same as equivalences under `ScalarHalf.XiExact`; at a step proof (Vesta commitments:
  the wrap circuit's group half, then the step circuit's scalar half) the equivalence
  `twoHalves_kimchiVerify_vesta`, with the claim tie unfolded (`vesta_claim_tie`); at a wrap
  proof (Pallas commitments: the step circuit's group half, then the wrap circuit's scalar
  half) `twoHalves_kimchiVerify_pallas`, and its converse under the exact-`ξ` hypothesis
  `twoHalves_kimchiVerify_pallas_converse`.

## Implementation notes

The proof identifies the scalar half's inputs with the run's through the ties (`rows_eq`:
the row list `finalize_other_proof` combines is the run's segment stream), and never
unfolds a sponge run: `runOracles`, `transcriptFrom` are projected by `simp` to the raw
`fqRun`/`ipaRunAt` fields, since a definitional unfolding of those recurses into the
permutation.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open Kimchi.Protocol.Linearization Poseidon.FqSponge
open scoped Kimchi

/-! ## The environment -/

/-- The verification environment: the SRS and the verifier key of the proof under
verification, at one chunk. Shared by the wire verifier and both circuit halves. -/
structure Env (C : KimchiCurve) where
  /-- The SRS (`σ.h` the blinding base, `σ.k` the round count). -/
  σ : SRS C.Point
  /-- The verifier key, one chunk. -/
  cvk : KimchiVK C 1

/-! ## The group half -/

/-- Pointwise ties along a zip give the mapped lists, at equal lengths: what a circuit that
compares two cell lists entry by entry establishes about them as lists. -/
private theorem map_eq_map_of_zip {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ p ∈ l₁.zip l₂, f p.1 = g p.2) → l₁.map f = l₂.map g
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => absurd hlen (by simp)
  | _ :: _, [], hlen, _ => absurd hlen (by simp)
  | a :: as, b :: bs, hlen, h => by
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨h (a, b) (by simp), map_eq_map_of_zip (by simpa using hlen) fun p hp => h p ?_⟩
      rw [List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hp

/-- The group half of a proof's verification, as one circuit runs it (for a step proof, the
wrap circuit): its valuation, its side (the ladder reading, the claim decode, the group facts),
the claim cells of its statement — the deferred values it scales by, the round challenges and
the fq digest its `incrementally_verify_proof` output is asserted equal to (`verify`) — and
the one bit it exports, the success bit. The `IvpOutput` itself is internal: existential in
`GroupHalf.Reads`, pinned to the claims by those assertions. -/
structure GroupHalf (C : KimchiCurve) (sf : Type) (k : ℕ) where
  /-- The circuit's valuation (over the base field). -/
  V : Valuation C.BaseField
  /-- The shifted-scalar operations of the side. -/
  ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf
  /-- The side. -/
  side : IvpSide C V ops
  /-- The statement's claim cells: the deferred values, the round challenges, the digest. -/
  claims : UnfinalizedProof k (FVar C.BaseField) (BoolVar C.BaseField) sf
  /-- The success bit: the opening's Schnorr equation at the claims. -/
  success : BoolVar C.BaseField

/-! ## The scalar half -/

/-- The scalar half's side: how a shifted claim cell reads (`FopShiftOps.Reading.read`), how
that reading unshifts, and the side's linearization token stream. The two functions are the
gadget's own (`stepShiftOps.reading`, `wrapShiftOps.reading`), kept apart because
`FopVerifyReads` takes them apart. -/
structure FopSide (C : KimchiCurve) (V : Valuation C.ScalarField) (sf : Type) where
  /-- The value a shifted claim cell reads as, still shifted. -/
  read : sf → C.ScalarField
  /-- The decode of a reading: the shift the side's claims carry. -/
  unshiftV : C.ScalarField → C.ScalarField
  /-- The linearization token stream of the side. -/
  toks : Array Linearization.PolishToken
  /-- Whether the side range-checks the low half of the `ξ` split (`xiConstrainLowBits`):
  the step circuit does, the wrap circuit does not. -/
  xiConstrainLowBits : Bool

/-- The scalar a shifted claim cell reads as: its value, unshifted. -/
def FopSide.decode {C : KimchiCurve} {V : Valuation C.ScalarField} {sf : Type}
    (S : FopSide C V sf) (x : sf) : C.ScalarField := S.unshiftV (S.read x)

/-- The two functions `FopVerifyReads` takes apart, put back together: what the gadget's read
states of a shifted claim is the half's decode of it. -/
theorem FopSide.unshiftV_read {C : KimchiCurve} {V : Valuation C.ScalarField} {sf : Type}
    (S : FopSide C V sf) (x : sf) : S.unshiftV (S.read x) = S.decode x := rfl

/-- The scalar half of a proof's verification, as the next circuit runs it (for a step proof,
the following step circuit): its valuation, its side, the deferred claim cells with the fq
digest, the evaluation cells, the predecessor mask and previous-challenge cells, and its
output — the four checks, their conjunction and the expanded challenges. -/
structure ScalarHalf (C : KimchiCurve) (sf : Type) (k : ℕ) where
  /-- The circuit's valuation (over the scalar field). -/
  V : Valuation C.ScalarField
  /-- The side. -/
  side : FopSide C V sf
  /-- The deferred claim cells and the fq digest cell. -/
  claims : UnfinalizedProof k (FVar C.ScalarField) (BoolVar C.ScalarField) sf
  /-- The evaluation cells: `ft(ζω)`, the public pair, the proof's evaluations. -/
  evals : AllEvals (FVar C.ScalarField)
  /-- The predecessor mask (`proofs_verified_mask`), one bit per slot: `true` for a real
  predecessor, `false` for a dummy pad slot. The step circuit varies it; the wrap circuit
  absorbs every slot, so its half fixes it all-true (`ScalarHalf.wrap`). -/
  mask : Vector Bool MaxProofsVerified
  /-- The previous challenges (`prev_challenges`), per slot the `k` expanded round challenges
  of that predecessor's opening (`k` the proof's own round count, its old accumulators'), as
  values of the circuit's cells. -/
  prevChallenges : Vector (Vector C.ScalarField k) MaxProofsVerified
  /-- The output. -/
  out : FopOutput C.ScalarField

/-- `finalize_other_proof`'s parameters from the environment: the fr-sponge, the eigenvalue,
the MDS matrix, the key's endo coefficient, coset shifts and `zk_rows`, the SRS's round
count, and the side's tokens. -/
def FopParams.ofEnv {C : KimchiCurve} (E : Env C) (toks : Array Linearization.PolishToken) :
    FopParams C.ScalarField :=
  { sponge := C.frSponge.params
    endoLam := C.lam
    endo := E.cvk.endo
    mds := mdsOfParams C.frSponge.params
    toks := toks
    shifts := fun i => E.cvk.shifts[i]
    srsLengthLog2 := E.σ.k
    zkRows := E.cvk.zkRows }

/-! ## The two halves' reads at their own cells -/

section AtCells

variable {C : KimchiCurve} {sf sf' : Type}

/-- The group half's read (`verify`'s): some `incrementally_verify_proof` output satisfying
`IvpReads` at the half's side and claim cells, whose success bit is the exported one and whose
digest and round prechallenges the statement's claims equal — `verify`'s two assertions. -/
def GroupHalf.Reads (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (G : GroupHalf C sf E.σ.k) : Prop :=
  VerifyReads G.side E.σ E.cvk cp pub G.claims false G.success

/-- The scalar half's read: `finalize_other_proof`'s own (`FopVerifyReads`, what both deployed
specs conclude), at the half's cells and the environment's parameters — `FopParams.ofEnv`, the
key's domain, the proof's recursion digest. A delegation, as `GroupHalf.Reads` is to
`VerifyReads`: the half restates nothing the gadget already says. Where the circuit's own
domain and digest differ from the key's and the proof's, that is a tie for the consumer to
supply, not something this definition may absorb. -/
def ScalarHalf.Reads (E : Env C) (cp : KimchiProof C 1 E.σ.k) (Sc : ScalarHalf C sf' E.σ.k) :
    Prop :=
  FopVerifyReads (p := C.scalar) (FopParams.ofEnv E Sc.side.toks) Sc.side.xiConstrainLowBits
    E.cvk.n E.cvk.omega (recDigest C (cp.olds.map (·.u))) Sc.mask.toList
    (Sc.prevChallenges.toList.map Vector.toList) Sc.claims Sc.evals C.lam
    Sc.side.read Sc.side.unshiftV Sc.V Sc.out

/-- The `ξ` comparison is exact at the half: a `ξ` claim reading as the wire's fr-sponge `ξ`
prechallenge — at the half's own digest, `ft(ζω)` and evaluation cells, the proof's recursion
digest — makes `xiCorrect` read `1`. The read gives this where the side range-checks the low
half of the `ξ` split (`xiExact_of_constrained`). Where it does not, the prover may witness
a low half at or above `2¹²⁸` whose split still lies below the modulus; the recomputed `ξ'`
then differs from the claim and `xiCorrect` reads `0`, so the exactness is a hypothesis. -/
def ScalarHalf.XiExact (E : Env C) (cp : KimchiProof C 1 E.σ.k) (Sc : ScalarHalf C sf' E.σ.k) :
    Prop :=
  let pre := frPrechallenges C.frSponge.params
    (frTranscript (Sc.claims.spongeDigestBeforeEvaluations.val Sc.V)
      (recDigest C (cp.olds.map (·.u))) (Sc.evals.ftEval1.val Sc.V)
      (Sc.evals.pub.map fun x => #v[x.val Sc.V]) (Sc.evals.evals.map fun x => #v[x.val Sc.V]))
  ∀ ξ₀ : Prechallenge, Reads128 Sc.V Sc.claims.deferredValues.xi ξ₀ → ξ₀.val = pre.1 →
    (↑Sc.out.xiCorrect : CVar C.ScalarField).val Sc.V = 1

end AtCells

/-! ## The ties between the two halves -/

section Ties

variable {C : KimchiCurve} {sf sf' : Type}

/-- What the two halves share, and what the scalar half's cells are on the wire. Two kinds:

* the claim ties (`alpha` … `digest`): the group half's statement cells and the scalar
  half's deferred cells carry one value across the field crossing — the shifted claims as
  `sf` cells decoded by the group side and `sf'` cells decoded by the scalar side, the
  128-bit prechallenges and round prechallenges as `SizedF 128` cells reading one
  prechallenge on both sides, the fq digest as the cast (`castDigest`, zero when the base
  element does not fit the scalar field: a completeness gap, not a soundness one). The
  protocol enforces these by the `x_hat` commitment binding the wrap statement into the
  proof; no circuit computes them, so they are hypotheses here;
* the proof ties (`olds` … `pubEvals`): the scalar half's evaluation, mask and
  previous-challenge cells are the proof's — prover-supplied cells against the wire objects
  the verifier judges. -/
structure HalvesTies (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (G : GroupHalf C sf E.σ.k) (Sc : ScalarHalf C sf' E.σ.k) : Prop where
  /-- `α`: the two cells read one prechallenge. -/
  alpha : ∃ a₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.plonk.alpha a₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.plonk.alpha a₀
  /-- `ζ`, likewise. -/
  zeta : ∃ z₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.plonk.zeta z₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.plonk.zeta z₀
  /-- `β`, likewise. -/
  beta : ∃ b₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.plonk.beta b₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.plonk.beta b₀
  /-- `γ`, likewise. -/
  gamma : ∃ g₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.plonk.gamma g₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.plonk.gamma g₀
  /-- `ξ`, likewise. -/
  xi : ∃ ξ₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.xi ξ₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.xi ξ₀
  /-- The `cip` claim decodes to the same scalar on both sides. -/
  cip : Sc.side.decode Sc.claims.deferredValues.combinedInnerProduct
    = G.side.decode G.claims.deferredValues.combinedInnerProduct
  /-- The `b` claim, likewise. -/
  b : Sc.side.decode Sc.claims.deferredValues.b = G.side.decode G.claims.deferredValues.b
  /-- The permutation-scalar claim, likewise. -/
  perm : Sc.side.decode Sc.claims.deferredValues.plonk.perm
    = G.side.decode G.claims.deferredValues.plonk.perm
  /-- The round challenges: the two cell lists read one prechallenge list. -/
  chals : ∃ ms : List Prechallenge,
    List.Forall₂ (Reads128 G.V) G.claims.deferredValues.bulletproofChallenges.toList ms ∧
    List.Forall₂ (Reads128 Sc.V) Sc.claims.deferredValues.bulletproofChallenges.toList ms
  /-- The fq digest: the scalar half's cell is the cast of the group half's. -/
  digest : Sc.claims.spongeDigestBeforeEvaluations.val Sc.V
    = castDigest C (G.claims.spongeDigestBeforeEvaluations.val G.V)
  /-- The kept previous challenges are the old accumulators' challenges, in order. -/
  olds : (List.zipWith (fun m cv => if m then [cv] else []) Sc.mask.toList
      (Sc.prevChallenges.toList.map Vector.toList)).flatten
    = (cp.olds.map (·.u.toList)).toList
  /-- `ft(ζω)` is the proof's. -/
  ftEval1 : Sc.evals.ftEval1.val Sc.V = cp.ftEval1
  /-- The evaluation cells are the proof's evaluations, as its one-chunk vectors. -/
  evals : Sc.evals.evals.map (fun x => #v[x.val Sc.V]) = cp.evals
  /-- The public evaluation cells are the run's (`runPubEvals`), as its one-chunk vectors. -/
  pubEvals : Sc.evals.pub.map (fun x => #v[x.val Sc.V]) = runPubEvals C E.σ E.cvk cp pub

/-- Where the side constrains the low half of the `ξ` split, the read makes the `ξ` comparison
exact: the `α`, `ζ` cells read as prechallenges (the ties' shared readings), and the read's
converse clause is `XiExact` at the claim the `ξ` cell reads. -/
theorem ScalarHalf.xiExact_of_constrained (E : Env C) (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField) {G : GroupHalf C sf E.σ.k}
    {Sc : ScalarHalf C sf' E.σ.k} (hflag : Sc.side.xiConstrainLowBits = true)
    (hs : Sc.Reads E cp) (ht : HalvesTies E cp pub G Sc) : Sc.XiExact E cp := by
  have hinjS := castInj128_of_lt _ hscalar
  obtain ⟨a₀, -, hαSa⟩ := ht.alpha
  obtain ⟨z₀, -, hζSz⟩ := ht.zeta
  simp only [ScalarHalf.Reads, FopVerifyReads] at hs
  obtain ⟨a₀', z₀', hαS, hζS, hs⟩ := hs
  obtain rfl := Reads128.unique hinjS hαSa hαS
  obtain rfl := Reads128.unique hinjS hζSz hζS
  simp only [FopReadsWire, FopParams.ofEnv] at hs
  obtain ⟨ξ₀', -, -, hξS, -, -, -, hex, -, -⟩ := hs
  intro ξ₀ hξ hpre
  obtain rfl := Reads128.unique hinjS hξ hξS
  exact hex hflag hpre

/-- The claims are the wire's own values: `cip` is `cipOf` the run's input, `b` is
`combinedB` at the run's round challenges, the permutation scalar is `runPScalar`, and the
`ξ` cell reads as the run's fr-sponge `ξ` prechallenge. What the scalar half's `finalized`
bit asserts, in wire terms. -/
def ClaimsHonest (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (cipV bV permV : C.ScalarField) (V : Valuation C.ScalarField)
    (xi : SizedF 128 (FVar C.ScalarField)) : Prop :=
  let run := runInput C E.σ E.cvk cp pub
  let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
  cipV = cipOf run ∧
  bV = combinedB (fun i => tr.2.1[i]) run.evalscale run.pointFn ∧
  permV = runPScalar C E.σ E.cvk cp pub ∧
  ∃ m : Prechallenge, Reads128 V xi m ∧
    m.val = (frPrechallenges C.frSponge.params (frTranscript (runOracles C E.σ E.cvk cp pub).digest
      (recDigest C (cp.olds.map (·.u))) cp.ftEval1 (runPubEvals C E.σ E.cvk cp pub) cp.evals)).1

/-- The claims of a scalar half, as `ClaimsHonest` reads them: the three shifted claims
through the side's decode, the `ξ` cell at the half's valuation. -/
def ScalarHalf.ClaimsHonest (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (Sc : ScalarHalf C sf' E.σ.k) : Prop :=
  let dv := Sc.claims.deferredValues
  Pickles.ClaimsHonest E cp pub (Sc.side.decode dv.combinedInnerProduct) (Sc.side.decode dv.b)
    (Sc.side.decode dv.plonk.perm) Sc.V dv.xi

/-- The deferred `sg`-correctness equation of the proof's opening at the wire's round
challenges (`verifyWith`'s second conjunct): what pickles checks one proof later. -/
def SgOk (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField) : Prop :=
  let run := runInput C E.σ E.cvk cp pub
  let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
  run.proof.sg = msm C E.σ.g (bPolyCoefficients fun i => tr.2.1[i])

/-- The decidable mirror of `SgOk`. This is the check the terminator runs out of circuit,
so it is the form in which the deferred obligation meets a wire proof. -/
def sgOk (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField) : Bool :=
  let run := runInput C E.σ E.cvk cp pub
  let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
  decide (run.proof.sg = msm C E.σ.g (bPolyCoefficients fun i => tr.2.1[i]))

/-- `sgOk` reflects `SgOk`. -/
theorem sgOk_iff (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField) :
    sgOk E cp pub = true ↔ SgOk E cp pub := by
  simp [sgOk, SgOk]

/-! ## The deferred obligation, carried

Pickles never checks `SgOk` on the proof itself. The proof's `(sg, round challenges)` becomes
an old accumulator of the next proof on the same curve, whose batch opens it; the circuit in
between, on the other curve, computes the challenges and passes them through its statement.
`Carry` names that handover, and `sgOk_iff_accOk` says the deferred equation is then an
equation on the next proof's input alone. -/

/-- The accumulator equation on an old accumulator alone: its commitment is the challenge
polynomial of its round challenges over the SRS — `SgOk` with the proof's opening and
transcript replaced by what the next proof carries. -/
def AccOk (σ : SRS C.Point) (a : Accumulator C σ.k) : Prop :=
  a.sg = msm C σ.g (bPolyCoefficients fun i => a.u[i])

/-- The decidable mirror of `AccOk`. -/
def accOk (σ : SRS C.Point) (a : Accumulator C σ.k) : Bool :=
  decide (a.sg = msm C σ.g (bPolyCoefficients fun i => a.u[i]))

/-- `accOk` reflects `AccOk`. -/
theorem accOk_iff (σ : SRS C.Point) (a : Accumulator C σ.k) : accOk σ a = true ↔ AccOk σ a := by
  simp [accOk, AccOk]

/-- `cp'` carries `cp`'s deferred obligation as its old accumulator `i`: the accumulator's
commitment is `cp`'s opening's `sg`, its challenges the wire's round challenges of `cp` — the
vector `SgOk` commits. Pickles forces this through the message digests of the statements
between the two proofs; here it is the named hypothesis. -/
def Carry (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (cp' : KimchiProof C 1 E.σ.k) (i : Fin cp'.olds.size) : Prop :=
  let run := runInput C E.σ E.cvk cp pub
  let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
  cp'.olds[i].sg = run.proof.sg ∧ cp'.olds[i].u = tr.2.1

/-- The decidable mirror of `Carry`. -/
def carry (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (cp' : KimchiProof C 1 E.σ.k) (i : Fin cp'.olds.size) : Bool :=
  let run := runInput C E.σ E.cvk cp pub
  let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
  decide (cp'.olds[i].sg = run.proof.sg ∧ cp'.olds[i].u = tr.2.1)

/-- `carry` reflects `Carry`. -/
theorem carry_iff (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (cp' : KimchiProof C 1 E.σ.k) (i : Fin cp'.olds.size) :
    carry E cp pub cp' i = true ↔ Carry E cp pub cp' i := by
  simp [carry, Carry]

/-- **The deferred obligation transports.** Under `Carry`, `cp`'s `SgOk` is the accumulator
equation of what `cp'` carries: checkable on `cp'`'s input, without `cp`. -/
theorem sgOk_iff_accOk (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (cp' : KimchiProof C 1 E.σ.k) (i : Fin cp'.olds.size) (h : Carry E cp pub cp' i) :
    SgOk E cp pub ↔ AccOk E.σ cp'.olds[i] := by
  obtain ⟨hsg, hu⟩ := h
  simp only [SgOk, AccOk, hsg, hu]

/-! ### Reading the wire's batch through the scalar half's rows -/

/-- A zip mapped through its second component is the second list mapped. -/
private theorem zip_map_snd {α β γ : Type} (g : β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      (l₁.zip l₂).map (fun x => g x.2) = l₂.map g := fun l₁ l₂ h => by
  rw [show (fun x : α × β => g x.2) = g ∘ Prod.snd from rfl, ← List.map_map,
    List.map_snd_zip h.ge]

/-- The head of a one-entry vector's list. -/
private theorem vec1_headD {α : Type} (v : Vector α 1) (d : α) : v.toList.headD d = v[0] := by
  obtain ⟨⟨l⟩, h⟩ := v
  simp at h
  match l, h with
  | [a], _ => rfl

/-- The chunk combination of one chunk is the chunk. -/
private theorem combineAt_one {F : Type} [Field F] (xM : F) (v : Vector F 1) :
    combineAt xM v.toArray = v[0] := by
  obtain ⟨⟨l⟩, h⟩ := v
  simp at h
  match l, h with
  | [a], _ => simp [combineAt]

/-- The challenge polynomial over a vector's list is the one over the vector. -/
private theorem bPoly_toList {F : Type} [Field F] {k : ℕ} (u : Vector F k) (x : F) :
    bPoly (fun i : Fin u.toList.length => u.toList.get i) x = bPoly u.get x := by
  unfold bPoly
  refine Fintype.prod_equiv (finCongr Vector.length_toList) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast, List.get_eq_getElem, Vector.getElem_toList,
    Vector.length_toList]
  rfl

/-- The one-chunk proof's combined evaluations are the linearization view of its chunks. -/
private theorem linEvals_one {C : KimchiCurve} {k : ℕ} (cp : KimchiProof C 1 k)
    (zM zOM : C.ScalarField) :
    cp.linEvals zM zOM = linEvals (cp.evals.map (·.toList.headD 0)) := by
  ext <;> simp only [KimchiProof.linEvals, linEvals, ProofEvaluations.map, PointEvaluations.map,
    combineAt_one, Fin.getElem_fin, Vector.getElem_map, vec1_headD]

/-- The combined inner product over a row list is the one over a vector with the same rows. -/
private theorem cip_congr {F : Type} [Field F] (ξ r : F) {m : ℕ} (rows : List (PointEvaluations F))
    (v : Vector (Vector F evalPts) m) (h : rows.map PointEvaluations.toVector = v.toList) :
    Bulletproof.combinedInnerProduct ξ r
        (fun (i : Fin rows.length) (j : Fin evalPts) => ((rows.get i).toVector)[j])
      = Bulletproof.combinedInnerProduct ξ r (fun (i : Fin m) (j : Fin evalPts) => (v[i])[j]) := by
  have hlen : rows.length = m := by
    have := congrArg List.length h
    simpa using this
  unfold Bulletproof.combinedInnerProduct
  refine Fintype.sum_equiv (finCongr hlen) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hi : PointEvaluations.toVector (rows.get i) = v[Fin.cast hlen i] := by
    have := List.getElem_of_eq h (i := i.val) (by simp)
    simpa [List.getElem_map, Vector.getElem_toList] using this
  rw [hi]

/-- Flattening a list of singletons is mapping. -/
private theorem flatten_singletons {α β : Type} (f : α → β) :
    ∀ l : List α, (l.map fun x => [f x]).flatten = l.map f := fun l => by
  induction l <;> simp_all

/-- One row's segments at one chunk, as a list: its single triple. -/
private theorem zipSeg_toList_one {C : KimchiCurve} (comm : Vector C.Point 1)
    (ev : PointEvaluations (Vector C.ScalarField 1)) :
    (zipSeg C comm ev).toList = [(comm[0], ev.zeta[0], ev.zetaOmega[0])] := by
  simp [zipSeg, Vector.toList_ofFn, List.ofFn_succ]

/-- The tail rows as a list: the four regions' lists (the vector append is typed at the
literal `tailRowCount`, which `Vector.toList_append` does not see through). -/
private theorem tailRows_toList {C : KimchiCurve} {k : ℕ} (cvk : KimchiVK C 1)
    (cp : KimchiProof C 1 k) :
    (tailRowsOf C cvk cp).toList
      = (litRowsOf C cvk cp).toList
        ++ ((cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)).toList
        ++ ((cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)).toList
        ++ (((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
              (fun x => zipSeg C x.1 x.2)).toList := by
  unfold tailRowsOf
  erw [Vector.toList_append, Vector.toList_append, Vector.toList_append]

/-- **The scalar half's rows are the run's stream.** At one chunk, the row list
`finalize_other_proof` combines — the kept challenge-polynomial rows, the public row, the
`ft` row, the 43 evaluation rows — projected to `(ζ, ζω)` pairs, is the run's segment stream
so projected: the old accumulators' rows, the public chunk, the `ft` segment, the tail rows. -/
private theorem rows_eq (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (ms : List Bool) (cvs : List (List C.ScalarField))
    (holds : (List.zipWith (fun m cv => if m then [cv] else []) ms cvs).flatten
      = (cp.olds.map (·.u.toList)).toList) :
    let pe := runPubEvals C E.σ E.cvk cp pub
    let o := runOracles C E.σ E.cvk cp pub
    let e := cp.evals.map (·.toList.headD 0)
    (sgRows ms (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) o.zeta)
        (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (o.zeta * E.cvk.omega))
      ++ ⟨pe.zeta[0], pe.zetaOmega[0]⟩
        :: ⟨ftEval0 E.cvk.n E.cvk.zkRows E.cvk.omega (fun i => E.cvk.shifts[i]) E.cvk.endo
              (mdsOfParams C.frSponge.params) o.alpha o.beta o.gamma o.zeta pe.zeta[0] (linEvals e),
            cp.ftEval1⟩
        :: evalRows e).map PointEvaluations.toVector
    = ((runStreamP C E.σ E.cvk cp pub pe).map
        (fun r => (#v[r.2.1, r.2.2] : Vector C.ScalarField evalPts))).toList := by
  intro pe o e
  rw [sgRows_kept, holds]
  simp only [o, e, runStreamP, runZetaOmega, runFtEval0P, runLinEvals, combineAt_one, linEvals_one,
    Vector.toList_map, Vector.toList_append, Vector.toList_ofFn,
    Snarky.toList_flatten, List.map_append, List.map_cons, List.map_map,
    List.ofFn_succ, List.ofFn_zero, evalRows, ProofEvaluations.map, PointEvaluations.map,
    PointEvaluations.toVector, tailRows_toList, litRowsOf, Function.comp_def, zipSeg_toList_one,
    Vector.toList_zip, Array.toList_map, Vector.toList_mk, List.nil_append, List.cons_append,
    List.flatten_cons, List.flatten_append, vec1_headD, bPoly_toList, flatten_singletons]
  have hz := zip_map_snd (α := Vector C.Point 1)
    (fun ev : PointEvaluations (Vector C.ScalarField 1) =>
      (#v[ev.zeta[0], ev.zetaOmega[0]] : Vector C.ScalarField evalPts))
  rw [hz cp.wComm.toList cp.evals.w.toList (by simp),
    hz E.cvk.coefficientsComm.toList cp.evals.coefficients.toList (by simp)]
  erw [hz _ cp.evals.s.toList]
  · rfl
  · simp

/-! ### Reading the cells through the ties -/

/-- `combinedB` over a vector's list is `combinedB` over the vector. -/
private theorem combinedB_toList {F : Type} [Field F] {k m : ℕ} (v : Vector F k) (r : F)
    (x : Fin m → F) :
    combinedB (fun i : Fin v.toList.length => v.toList.get i) r x
      = combinedB (fun i => v[i]) r x := by
  unfold combinedB
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bPoly_toList]
  rfl

/-- The run's evaluation points, as `finalize_other_proof` lists them. -/
private theorem pointFn_eq (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField) :
    (runInput C E.σ E.cvk cp pub).pointFn
      = ![(runOracles C E.σ E.cvk cp pub).zeta,
          (runOracles C E.σ E.cvk cp pub).zeta * E.cvk.omega] := by
  funext j
  fin_cases j <;> rfl

/-- Both directions of the Schnorr composition at once, the converse under `XiExact`: one
proof, projected by `twoHalves_schnorr` and `twoHalves_iff_schnorr`. -/
private theorem twoHalves_schnorr_core
    (E : Env C)
    (hbase : 2 ^ 128 < C.base)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C 1 E.σ.k)
    (pub : Array C.ScalarField)
    -- the group half
    (G : GroupHalf C sf E.σ.k)
    (hg : G.Reads E cp pub)
    -- the scalar half
    (Sc : ScalarHalf C sf' E.σ.k)
    (hs : Sc.Reads E cp)
    -- across the two
    (ht : HalvesTies E cp pub G Sc) :
    let run := runInput C E.σ E.cvk cp pub
    let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
    (((↑G.success : CVar C.BaseField).val G.V = 1
        ∧ (↑Sc.out.finalized : CVar C.ScalarField).val Sc.V = 1)
      → Sc.ClaimsHonest E cp pub ∧
        schnorrAt C E.σ tr.1 tr.2.1 tr.2.2 (cipOf run)
          (combinedB (fun i => tr.2.1[i]) run.evalscale run.pointFn)
          (combineCommitments C run.polyscale run.commitments.toArray) run.proof) ∧
    (Sc.XiExact E cp →
      Sc.ClaimsHonest E cp pub ∧
        schnorrAt C E.σ tr.1 tr.2.1 tr.2.2 (cipOf run)
          (combinedB (fun i => tr.2.1[i]) run.evalscale run.pointFn)
          (combineCommitments C run.polyscale run.commitments.toArray) run.proof
      → (↑G.success : CVar C.BaseField).val G.V = 1
        ∧ (↑Sc.out.finalized : CVar C.ScalarField).val Sc.V = 1) := by
  intro run tr
  have hinjG := castInj128_of_lt _ hbase
  have hinjS := castInj128_of_lt _ hscalar
  -- the shared prechallenges
  obtain ⟨a₀, hαGa, hαSa⟩ := ht.alpha
  obtain ⟨z₀, hζGz, hζSz⟩ := ht.zeta
  obtain ⟨b₀, hβGb, hβSb⟩ := ht.beta
  obtain ⟨g₀, hγGg, hγSg⟩ := ht.gamma
  obtain ⟨ξ₀, hξGx, hξSx⟩ := ht.xi
  -- the group half's read: `α`, `ζ` are the wire's through the shared readings
  obtain ⟨o, hx, hsucc, hdig, hbpc⟩ := hg
  simp only [IvpReads, DeferredValues.toIvpClaims] at hx
  obtain ⟨hdE, hβG, hγG, hαG', hζG', hξG⟩ := hx
  have hαG := (hαG' a₀ hαGa) ▸ hαGa
  have hζG := (hζG' z₀ hζGz) ▸ hζGz
  obtain ⟨U, ns, c₀, chals, rfl, hns, rfl, rfl, hchals, hiff⟩ := hξG ξ₀ hξGx
  have hch : chals = (ipaRunAt C (fqRun C E.cvk cp (publicCommitment C E.σ E.cvk pub)).warm
      (G.side.decode G.claims.deferredValues.combinedInnerProduct) cp.opening).2.1.map
        fun m => endoExpand C.lam m.val :=
    Vector.toList_inj.mp (by rw [hchals, Vector.toList_map])
  subst hch
  rw [hsucc] at hiff
  -- the scalar half's read, at the shared `α`, `ζ`
  simp only [ScalarHalf.Reads, FopVerifyReads] at hs
  obtain ⟨a₀', z₀', hαS, hζS, hs⟩ := hs
  obtain rfl := Reads128.unique hinjS hαSa hαS
  obtain rfl := Reads128.unique hinjS hζSz hζS
  simp only [FopReadsWire, FopChecks, FopParams.ofEnv, FopSide.unshiftV_read] at hs
  obtain ⟨ξ₀', r', ĉ, hξS, hr', -, hxiF, -, hĉ, hcipC, hbC, hpermC, hfin, -⟩ := hs
  obtain rfl : ξ₀ = ξ₀' := Reads128.unique hinjS hξSx hξS
  -- the scalar half's inputs are the run's
  have hζ : endoExpand C.lam z₀.val = (runOracles C E.σ E.cvk cp pub).zeta := by
    simp only [runOracles, fqOracles, FqRun.expand]
    rw [Reads128.unique hinjG hζGz hζG]
  have hα : endoExpand C.lam a₀.val = (runOracles C E.σ E.cvk cp pub).alpha := by
    simp only [runOracles, fqOracles, FqRun.expand]
    rw [Reads128.unique hinjG hαGa hαG]
  have hβ : Sc.claims.deferredValues.plonk.beta.val.val Sc.V
      = (runOracles C E.σ E.cvk cp pub).beta := by
    simp only [runOracles, fqOracles, FqRun.expand]
    unfold Reads128 at hβSb
    rw [Reads128.unique hinjG hβGb hβG] at hβSb
    exact hβSb
  have hγ : Sc.claims.deferredValues.plonk.gamma.val.val Sc.V
      = (runOracles C E.σ E.cvk cp pub).gamma := by
    simp only [runOracles, fqOracles, FqRun.expand]
    unfold Reads128 at hγSg
    rw [Reads128.unique hinjG hγGg hγG] at hγSg
    exact hγSg
  have hd : Sc.claims.spongeDigestBeforeEvaluations.val Sc.V
      = (runOracles C E.σ E.cvk cp pub).digest := by
    rw [ht.digest, hdig, ← hdE]; rfl
  -- the evaluation values are the proof's heads: the functor law, `headD 0 ∘ #v[·]` being `id`
  have hev : Sc.evals.evals.map (·.val Sc.V) = cp.evals.map (·.toList.headD 0) := by
    rw [← ht.evals]
    show ProofEvaluations.map _ _
      = (·.toList.headD 0) <$> (fun x => #v[x.val Sc.V]) <$> Sc.evals.evals
    rw [← LawfulFunctor.comp_map]
    rfl
  have hpz : Sc.evals.pub.zeta.val Sc.V = (runPubEvals C E.σ E.cvk cp pub).zeta[0] := by
    rw [← ht.pubEvals]; rfl
  have hpzo : Sc.evals.pub.zetaOmega.val Sc.V = (runPubEvals C E.σ E.cvk cp pub).zetaOmega[0] := by
    rw [← ht.pubEvals]; rfl
  rw [hd, ht.ftEval1, ht.pubEvals, ht.evals] at hr' hxiF
  have hr : endoExpand C.lam r'.val = run.evalscale := by
    show _ = (frOracles C cp _ _).r
    rw [frOracles_eq_frPrechallenges, hr']
  have hxiF' : (↑Sc.out.xiCorrect : CVar C.ScalarField).val Sc.V = 1
      → ∃ m : Prechallenge, Reads128 Sc.V Sc.claims.deferredValues.xi m ∧
        m.val = (frPrechallenges C.frSponge.params
            (frTranscript (runOracles C E.σ E.cvk cp pub).digest
            (recDigest C (cp.olds.map (·.u))) cp.ftEval1 (runPubEvals C E.σ E.cvk cp pub)
            cp.evals)).1 :=
    fun h => ⟨ξ₀, hξS, hxiF h⟩
  have hξrun : (∃ m : Prechallenge, Reads128 Sc.V Sc.claims.deferredValues.xi m ∧
        m.val = (frPrechallenges C.frSponge.params
            (frTranscript (runOracles C E.σ E.cvk cp pub).digest
            (recDigest C (cp.olds.map (·.u))) cp.ftEval1 (runPubEvals C E.σ E.cvk cp pub)
            cp.evals)).1) →
      endoExpand C.lam ξ₀.val = run.polyscale := by
    rintro ⟨m, hm, hmv⟩
    rw [Reads128.unique hinjS hξS hm, hmv]
    show _ = (frOracles C cp _ _).xi
    rw [frOracles_eq_frPrechallenges]
  -- the round challenges: the cell lists' readings are equations of lists
  obtain ⟨ms, hmsG, hmsS⟩ := ht.chals
  -- `verify` compares the claimed challenges with the returned ones entry by entry off the
  -- base case; both lists have the SRS's round count, so the ties give the lists
  have hbpc' : G.claims.deferredValues.bulletproofChallenges.toList.map (·.val.val G.V)
      = o.bulletproofChallenges.map (·.val.val G.V) :=
    map_eq_map_of_zip (by simp [hns.length_eq]) (hbpc rfl)
  rw [forall₂_reads128_iff] at hmsG hmsS hns hĉ
  have hĉeq : ĉ = (ipaRunAt C (fqRun C E.cvk cp (publicCommitment C E.σ E.cvk pub)).warm
      (G.side.decode G.claims.deferredValues.combinedInnerProduct) cp.opening).2.1.toList :=
    (List.map_injective_iff.mpr hinjS.prechallenge_injective (hĉ.symm.trans hmsS)).trans
      (List.map_injective_iff.mpr hinjG.prechallenge_injective (hmsG.symm.trans (hbpc'.trans hns)))
  -- the four checks, in wire terms
  rw [hζ, hα, hβ, hγ, hev, hpz, hpzo, ht.ftEval1] at hcipC
  rw [hζ] at hbC
  rw [hζ, hα, hβ, hγ, hev] at hpermC
  have hcipIff : endoExpand C.lam ξ₀.val = run.polyscale →
      ((↑Sc.out.cipCorrect : CVar C.ScalarField).val Sc.V = 1
        ↔ Sc.side.decode Sc.claims.deferredValues.combinedInnerProduct = cipOf run) := by
    intro hξv
    simp only [hcipC, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [hξv, hr, cip_congr _ _ _ _ (rows_eq E cp pub _ _ ht.olds)]
    exact Iff.rfl
  have hbIff : (↑Sc.out.bCorrect : CVar C.ScalarField).val Sc.V = 1
      ↔ Sc.side.decode Sc.claims.deferredValues.b
        = combinedB (fun i =>
            ((ipaRunAt C (fqRun C E.cvk cp (publicCommitment C E.σ E.cvk pub)).warm
              (G.side.decode G.claims.deferredValues.combinedInnerProduct) cp.opening).2.1.map
                (fun m => endoExpand C.lam m.val))[i]) run.evalscale run.pointFn := by
    simp only [hbC, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [hr, hĉeq, ← Vector.toList_map, combinedB_toList, pointFn_eq]
  have hpermIff : (↑Sc.out.plonkOk : CVar C.ScalarField).val Sc.V = 1
      ↔ Sc.side.decode Sc.claims.deferredValues.plonk.perm = runPScalar C E.σ E.cvk cp pub := by
    simp only [hpermC, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    unfold runPScalar runLinEvals
    rw [linEvals_one]
  -- assemble, the wire's transcript projected (no unfolding of the sponge runs)
  have hproof : (runInput C E.σ E.cvk cp pub).proof = cp.opening := rfl
  have hwarm : (runOracles C E.σ E.cvk cp pub).warm
      = (fqRun C E.cvk cp (publicCommitment C E.σ E.cvk pub)).warm := by
    simp only [runOracles, fqOracles, FqRun.expand]
  rw [hproof] at hiff
  simp only [ScalarHalf.ClaimsHonest, ClaimsHonest, run, tr, transcriptFrom, hwarm, hproof]
  rw [hfin]
  simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
  rw [hbIff, hpermIff]
  constructor
  · rintro ⟨hsG, hxiC, hb, hcip, hperm⟩
    have hxiV := hxiF' hxiC
    have hξv := hξrun hxiV
    have hcip' := (hcipIff hξv).1 hcip
    have hcipG : G.side.decode G.claims.deferredValues.combinedInnerProduct = cipOf run :=
      ht.cip.symm.trans hcip'
    rw [hcipG] at hiff hb
    rw [hξv, ← ht.b, hb] at hiff
    exact ⟨⟨hcip', hb, hperm, hxiV⟩, hiff.1 hsG⟩
  · -- the converse: the exact `ξ` comparison turns the honest claim into the bit
    rintro hxi ⟨⟨hcip, hb, hperm, hxiV⟩, hschnorr⟩
    simp only [ScalarHalf.XiExact] at hxi
    rw [hd, ht.ftEval1, ht.pubEvals, ht.evals] at hxi
    obtain ⟨m, hm, hmv⟩ := hxiV
    have hxiC := hxi m hm hmv
    have hξv := hξrun ⟨m, hm, hmv⟩
    have hcipG : G.side.decode G.claims.deferredValues.combinedInnerProduct = cipOf run :=
      ht.cip.symm.trans hcip
    rw [hcipG] at hiff ⊢
    rw [hξv, ← ht.b, hb] at hiff
    exact ⟨hiff.2 hschnorr, hxiC, hb, (hcipIff hξv).2 hcip, hperm⟩

/-- **The two bits make the claims honest and the wire's Schnorr equation hold.** Without
`SgOk`: the two bits reading `1` make the claims the wire's own values and the opening's
Schnorr equation hold at the wire's transcript — `verifyWith`'s first conjunct. -/
theorem twoHalves_schnorr
    (E : Env C)
    (hbase : 2 ^ 128 < C.base)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C 1 E.σ.k)
    (pub : Array C.ScalarField)
    -- the group half
    (G : GroupHalf C sf E.σ.k)
    (hg : G.Reads E cp pub)
    -- the scalar half
    (Sc : ScalarHalf C sf' E.σ.k)
    (hs : Sc.Reads E cp)
    -- across the two
    (ht : HalvesTies E cp pub G Sc) :
    let run := runInput C E.σ E.cvk cp pub
    let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
    ((↑G.success : CVar C.BaseField).val G.V = 1
        ∧ (↑Sc.out.finalized : CVar C.ScalarField).val Sc.V = 1)
      → Sc.ClaimsHonest E cp pub ∧
        schnorrAt C E.σ tr.1 tr.2.1 tr.2.2 (cipOf run)
          (combinedB (fun i => tr.2.1[i]) run.evalscale run.pointFn)
          (combineCommitments C run.polyscale run.commitments.toArray) run.proof :=
  (twoHalves_schnorr_core E hbase hscalar cp pub G hg Sc hs ht).1

/-- **The two bits are the honest claims with the wire's Schnorr equation**, where the scalar
half's `ξ` comparison is exact: `twoHalves_schnorr` and its converse. -/
theorem twoHalves_iff_schnorr
    (E : Env C)
    (hbase : 2 ^ 128 < C.base)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C 1 E.σ.k)
    (pub : Array C.ScalarField)
    -- the group half
    (G : GroupHalf C sf E.σ.k)
    (hg : G.Reads E cp pub)
    -- the scalar half
    (Sc : ScalarHalf C sf' E.σ.k)
    (hs : Sc.Reads E cp)
    (hxi : Sc.XiExact E cp)
    -- across the two
    (ht : HalvesTies E cp pub G Sc) :
    let run := runInput C E.σ E.cvk cp pub
    let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
    ((↑G.success : CVar C.BaseField).val G.V = 1
        ∧ (↑Sc.out.finalized : CVar C.ScalarField).val Sc.V = 1)
      ↔ Sc.ClaimsHonest E cp pub ∧
        schnorrAt C E.σ tr.1 tr.2.1 tr.2.2 (cipOf run)
          (combinedB (fun i => tr.2.1[i]) run.evalscale run.pointFn)
          (combineCommitments C run.polyscale run.commitments.toArray) run.proof :=
  ⟨(twoHalves_schnorr_core E hbase hscalar cp pub G hg Sc hs ht).1,
    (twoHalves_schnorr_core E hbase hscalar cp pub G hg Sc hs ht).2 hxi⟩

/-- **The two halves' bits and the deferred `sg` equation make `kimchiVerify` accept.** In the
environment `E`, for the proof `(cp, pub)`: with the group half and the scalar half reading at
their cells, tied, and the guards, the success bit and the `finalized` bit reading `1` with
`SgOk` make `kimchiVerify` accept and the claims the wire's own values. (`kimchiVerify`
recomputes the claims and never sees the cells, so the honest-claims conjunct is what
`finalized` adds.) -/
theorem twoHalves_kimchiVerify
    (E : Env C)
    (hbase : 2 ^ 128 < C.base)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C 1 E.σ.k)
    (pub : Array C.ScalarField)
    (hguard : Guards C E.cvk cp pub)
    -- the group half
    (G : GroupHalf C sf E.σ.k)
    (hg : G.Reads E cp pub)
    -- the scalar half
    (Sc : ScalarHalf C sf' E.σ.k)
    (hs : Sc.Reads E cp)
    -- across the two
    (ht : HalvesTies E cp pub G Sc) :
    ((↑G.success : CVar C.BaseField).val G.V = 1
        ∧ (↑Sc.out.finalized : CVar C.ScalarField).val Sc.V = 1)
        ∧ SgOk E cp pub
      → kimchiVerify C E.σ E.cvk cp pub = true ∧ Sc.ClaimsHonest E cp pub := by
  have h := twoHalves_schnorr E hbase hscalar cp pub G hg Sc hs ht
  -- the body reflection: under the guards, the warm-sponge IPA finish on the run's input
  simp only [transcriptFrom] at h
  rw [kimchiVerify_reflects, and_iff_right hguard]
  simp only [SgOk, verifyFrom, transcriptFrom, verifyWith_eq]
  rintro ⟨hbits, hsg⟩
  obtain ⟨hc, hsch⟩ := h hbits
  exact ⟨⟨hsch, hsg⟩, hc⟩

/-- **The two halves accept exactly when the wire verifier does at honest claims, given the
deferred `sg` equation**, where the scalar half's `ξ` comparison is exact:
`twoHalves_kimchiVerify` and its converse. -/
theorem twoHalves_kimchiVerify_iff
    (E : Env C)
    (hbase : 2 ^ 128 < C.base)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C 1 E.σ.k)
    (pub : Array C.ScalarField)
    (hguard : Guards C E.cvk cp pub)
    -- the group half
    (G : GroupHalf C sf E.σ.k)
    (hg : G.Reads E cp pub)
    -- the scalar half
    (Sc : ScalarHalf C sf' E.σ.k)
    (hs : Sc.Reads E cp)
    (hxi : Sc.XiExact E cp)
    -- across the two
    (ht : HalvesTies E cp pub G Sc) :
    ((↑G.success : CVar C.BaseField).val G.V = 1
        ∧ (↑Sc.out.finalized : CVar C.ScalarField).val Sc.V = 1)
        ∧ SgOk E cp pub
      ↔ kimchiVerify C E.σ E.cvk cp pub = true ∧ Sc.ClaimsHonest E cp pub := by
  have h := twoHalves_iff_schnorr E hbase hscalar cp pub G hg Sc hs hxi ht
  -- the body reflection: under the guards, the warm-sponge IPA finish on the run's input
  simp only [transcriptFrom] at h
  rw [h, kimchiVerify_reflects, and_iff_right hguard]
  simp only [SgOk, verifyFrom, transcriptFrom, verifyWith_eq]
  exact ⟨fun ⟨⟨hc, hs⟩, hsg⟩ => ⟨⟨hs, hsg⟩, hc⟩, fun ⟨⟨hs, hsg⟩, hc⟩ => ⟨⟨hc, hs⟩, hsg⟩⟩

end Ties

/-! ## At a step proof: Vesta commitments

A step proof's commitments are Vesta points (`Fq` coordinates) with `Fp` scalars. Its group
half runs first, in the wrap circuit (over `Fq`, `wrapSide`, the claims as `Type1 (FVar Fq)`);
its scalar half one circuit later, in the next step circuit (over `Fp`, `fopStep`, the claims
as `Type1 (FVar Fp)`, carried through the wrap statement). The sides fix everything but the
cells; what is left to see is the claim tie, which unfolds to *one integer carried in two
fields* (`vesta_claim_tie`): the `Fp` cell's value is the `Fq` cell's value as an integer.
There is no canonicity condition (`wrapSide.Canon` is trivial). -/

section StepProof

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The step circuit's scalar side: `Type1` claims decoded as the step reading unshifts them
(`stepShiftOps.reading`, `Type1.fromShifted 255`), the `Fp` linearization tokens. -/
def fopStep (V : Valuation Fp) : FopSide IpaVesta.curve V (Type1 (FVar Fp)) where
  read := (stepShiftOps.reading (V := V) (by decide)).read
  unshiftV := (stepShiftOps.reading (V := V) (by decide)).unshiftV
  toks := Linearization.fpTokens
  xiConstrainLowBits := true

/-- The wrap circuit's group half of a step proof: `wrapSide` at the circuit's valuation. -/
def GroupHalf.wrap {k : ℕ} (V : Valuation Fq)
    (claims : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (success : BoolVar Fq) : GroupHalf IpaVesta.curve (Type1 (FVar Fq)) k :=
  ⟨V, IpaScalarOps.wrap, wrapSide V, claims, success⟩

/-- The step circuit's scalar half of a step proof: `fopStep` at the circuit's valuation, at
the round count `k` of the finalized proof's SRS (`StepIPARounds` when deployed). -/
def ScalarHalf.step {k : ℕ} (V : Valuation Fp)
    (claims : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : AllEvals (FVar Fp)) (mask : Vector Bool MaxProofsVerified)
    (prevChallenges : Vector (Vector Fp k) MaxProofsVerified) (out : FopOutput Fp) :
    ScalarHalf IpaVesta.curve (Type1 (FVar Fp)) k :=
  ⟨V, fopStep V, claims, evals, mask, prevChallenges, out⟩

/-- At a step proof the claim tie is the `Fp` cell's value equal to the `Fq` cell's value as
an integer: both sides unshift at `255` bits, and the unshift is injective. -/
theorem vesta_claim_tie {Vg : Valuation Fq} {Vs : Valuation Fp}
    (x : Type1 (FVar Fp))
    (y : Type1 (FVar Fq)) :
    (fopStep Vs).decode x = (wrapSide Vg).decode y ↔ x.val.val Vs = ((y.val.val Vg).val : Fp) := by
  simp only [FopSide.decode, fopStep, stepShiftOps.reading, wrapSide, wrapDecode,
    Type1.fromShifted, Pasta.Shifted.unshiftType1]
  constructor
  · intro h
    have h2 : (2 : Fp) ≠ 0 := by decide
    exact mul_left_cancel₀ h2 (add_right_cancel (add_right_cancel h))
  · intro h
    rw [h]

/-- **A step proof's two halves accept exactly when `kimchiVerify` does at honest claims.** The
wrap circuit's group half, then the step circuit's scalar half, tied, with the guards; the
step circuit range-checks the low half of its `ξ` split, so the `ξ` comparison is exact and
the statement an equivalence. -/
theorem twoHalves_kimchiVerify_vesta
    (E : Env IpaVesta.curve)
    (cp : KimchiProof IpaVesta.curve 1 E.σ.k)
    (pub : Array Fp)
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    -- the wrap circuit: its valuation, its statement's claims, its success bit, its read
    (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (successG : BoolVar Fq)
    (hg : (GroupHalf.wrap Vg claimsG successG).Reads E cp pub)
    -- the next step circuit: its valuation, its cells, its output, its read
    (Vs : Valuation Fp)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : AllEvals (FVar Fp))
    (mask : Vector Bool MaxProofsVerified)
    (prevChallenges : Vector (Vector Fp E.σ.k) MaxProofsVerified)
    (outS : FopOutput Fp)
    (hs : (ScalarHalf.step Vs claimsS evals mask prevChallenges outS).Reads E cp)
    -- across the two
    (ht : HalvesTies E cp pub (GroupHalf.wrap Vg claimsG successG)
      (ScalarHalf.step Vs claimsS evals mask prevChallenges outS)) :
    ((↑successG : CVar Fq).val Vg = 1 ∧ (↑outS.finalized : CVar Fp).val Vs = 1)
        ∧ SgOk E cp pub
      ↔ kimchiVerify IpaVesta.curve E.σ E.cvk cp pub = true ∧
        (ScalarHalf.step Vs claimsS evals mask prevChallenges outS).ClaimsHonest E cp pub :=
  twoHalves_kimchiVerify_iff E (by norm_num [PALLAS_SCALAR_CARD]) (by norm_num [PALLAS_BASE_CARD])
    cp pub hguard _ hg _ hs
    (ScalarHalf.xiExact_of_constrained E (by norm_num [PALLAS_BASE_CARD]) cp pub rfl hs ht) ht

end StepProof

/-! ## At a wrap proof: Pallas commitments

A wrap proof's commitments are Pallas points (`Fp` coordinates) with `Fq` scalars. Its group
half runs first, in the step circuit (over `Fp`, `stepSide`, the claims as split `Type2` cells);
its scalar half one circuit later, in the next wrap circuit (over `Fq`, `fopWrap`, the claims
as `Type2 (FVar Fq)`, carried through the step statement). -/

section WrapProof

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The wrap circuit's scalar side: `Type2` claims decoded as the wrap reading unshifts them
(`wrapShiftOps.reading`, `Type2.fromShifted 255`), the `Fq` linearization tokens. -/
def fopWrap (V : Valuation Fq) : FopSide IpaPallas.curve V (Type2 (FVar Fq)) where
  read := (wrapShiftOps.reading (V := V)).read
  unshiftV := (wrapShiftOps.reading (V := V)).unshiftV
  toks := Linearization.fqTokens
  xiConstrainLowBits := false

/-- The step circuit's group half of a wrap proof: `stepSide` at the circuit's valuation. -/
def GroupHalf.step {k : ℕ} (V : Valuation Fp)
    (claims : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (success : BoolVar Fp) :
    GroupHalf IpaPallas.curve (Type2 (SplitField (FVar Fp) (BoolVar Fp))) k :=
  ⟨V, IpaScalarOps.step, stepSide V, claims, success⟩

/-- The wrap circuit's scalar half of a wrap proof: `fopWrap` at the circuit's valuation, at the
round count `k` of the finalized proof's SRS (`WrapIPARounds` when deployed), every slot
present: the wrap circuit has no mask (`finalizeOtherProofWrap` absorbs every slot), so the
half's is all-true. -/
def ScalarHalf.wrap {k : ℕ} (V : Valuation Fq)
    (claims : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : AllEvals (FVar Fq)) (prevChallenges : Vector (Vector Fq k) MaxProofsVerified)
    (out : FopOutput Fq) : ScalarHalf IpaPallas.curve (Type2 (FVar Fq)) k :=
  ⟨V, fopWrap V, claims, evals, Vector.replicate MaxProofsVerified true, prevChallenges, out⟩

/-- At the wrap half the `olds` tie keeps every slot: the previous-challenge cells are the old
accumulators' challenges, in order. -/
theorem ScalarHalf.wrap_olds {k : ℕ} (V : Valuation Fq)
    (claims : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : AllEvals (FVar Fq))
    (prevChallenges : Vector (Vector Fq k) MaxProofsVerified) (out : FopOutput Fq)
    (olds : List (List Fq)) :
    ((List.zipWith (fun m cv => if m then [cv] else [])
        (ScalarHalf.wrap V claims evals prevChallenges out).mask.toList
        ((ScalarHalf.wrap V claims evals prevChallenges out).prevChallenges.toList.map
          Vector.toList)).flatten = olds)
      ↔ prevChallenges.toList.map Vector.toList = olds := by
  have hkeep : ∀ (n : ℕ) (l : List (List Fq)), l.length = n →
      (List.zipWith (fun m cv => if m then [cv] else []) (List.replicate n true) l).flatten
        = l := by
    intro n l hn
    subst hn
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.flatten_cons,
        if_pos rfl, List.singleton_append, ih]
  simp only [ScalarHalf.wrap, Vector.toList_replicate]
  rw [hkeep _ _ (by simp)]

/-- **A wrap proof's two halves accepting makes `kimchiVerify` accept.** The step circuit's
group half, then the wrap circuit's scalar half, tied, with the guards. -/
theorem twoHalves_kimchiVerify_pallas
    (E : Env IpaPallas.curve)
    (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
    (pub : Array Fq)
    (hguard : Guards IpaPallas.curve E.cvk cp pub)
    -- the step circuit: its valuation, its statement's claims, its success bit, its read
    (Vg : Valuation Fp)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (successG : BoolVar Fp)
    (hg : (GroupHalf.step Vg claimsG successG).Reads E cp pub)
    -- the next wrap circuit: its valuation, its cells, its output, its read
    (Vs : Valuation Fq)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : AllEvals (FVar Fq))
    (prevChallenges : Vector (Vector Fq E.σ.k) MaxProofsVerified)
    (outS : FopOutput Fq)
    (hs : (ScalarHalf.wrap Vs claimsS evals prevChallenges outS).Reads E cp)
    -- across the two
    (ht : HalvesTies E cp pub (GroupHalf.step Vg claimsG successG)
      (ScalarHalf.wrap Vs claimsS evals prevChallenges outS)) :
    ((↑successG : CVar Fp).val Vg = 1 ∧ (↑outS.finalized : CVar Fq).val Vs = 1)
        ∧ SgOk E cp pub
      → kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true ∧
        (ScalarHalf.wrap Vs claimsS evals prevChallenges outS).ClaimsHonest E cp pub :=
  twoHalves_kimchiVerify E (by norm_num [PALLAS_BASE_CARD]) (by norm_num [PALLAS_SCALAR_CARD])
    cp pub hguard _ hg _ hs ht

/-- **`kimchiVerify` accepting at honest claims makes a wrap proof's two halves accept, where
the wrap circuit's `ξ` comparison is exact.** The converse of `twoHalves_kimchiVerify_pallas`,
and weaker than an equivalence by its last hypothesis: the wrap circuit's `squeezeScalar`
leaves the low half of its `ξ` split unchecked, so a prover may witness a low half at or above
`2¹²⁸` whose split still lies below the modulus, and `xiCorrect` then reads `0` at a claim
equal to the wire's `ξ`. `ScalarHalf.XiExact` rules that witness out. -/
theorem twoHalves_kimchiVerify_pallas_converse
    (E : Env IpaPallas.curve)
    (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
    (pub : Array Fq)
    (hguard : Guards IpaPallas.curve E.cvk cp pub)
    -- the step circuit: its valuation, its statement's claims, its success bit, its read
    (Vg : Valuation Fp)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (successG : BoolVar Fp)
    (hg : (GroupHalf.step Vg claimsG successG).Reads E cp pub)
    -- the next wrap circuit: its valuation, its cells, its output, its read
    (Vs : Valuation Fq)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : AllEvals (FVar Fq))
    (prevChallenges : Vector (Vector Fq E.σ.k) MaxProofsVerified)
    (outS : FopOutput Fq)
    (hs : (ScalarHalf.wrap Vs claimsS evals prevChallenges outS).Reads E cp)
    -- across the two
    (ht : HalvesTies E cp pub (GroupHalf.step Vg claimsG successG)
      (ScalarHalf.wrap Vs claimsS evals prevChallenges outS))
    -- the exact `ξ` comparison, which the wrap circuit does not enforce
    (hxi : (ScalarHalf.wrap Vs claimsS evals prevChallenges outS).XiExact E cp) :
    kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true ∧
        (ScalarHalf.wrap Vs claimsS evals prevChallenges outS).ClaimsHonest E cp pub
      → ((↑successG : CVar Fp).val Vg = 1 ∧ (↑outS.finalized : CVar Fq).val Vs = 1)
        ∧ SgOk E cp pub :=
  (twoHalves_kimchiVerify_iff E (by norm_num [PALLAS_BASE_CARD])
    (by norm_num [PALLAS_SCALAR_CARD]) cp pub hguard _ hg _ hs hxi ht).2

end WrapProof

end Pickles
