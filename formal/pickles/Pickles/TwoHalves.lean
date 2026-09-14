import Pickles.IncrementallyVerify
import Pickles.FinalizeOtherProof
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
the two bits reading `1` together with the deferred `sg`-correctness equation is the
acceptance of `kimchiVerify` (`twoHalves_kimchiVerify`), and the two bits alone are the
wire's Schnorr equation at honest claims (`twoHalves_iff_schnorr`).

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

## The slack this closes by hypothesis

The reads carry two slacks the circuits leave open: the `lowest_128_bits` alias on every
128-bit prechallenge (`PrechallengeAlias`, #344) and the sign of the map-to-curve's `U`.
A prover choosing a non-canonical alias runs a different Fiat–Shamir instance, so the
composition cannot equal `kimchiVerify` without closing them. `IvpReadsExact` and
`FopReadsExact` are the reads with the alias replaced by equality and the sign fixed; each
implies its slack form, and each becomes the read itself once the fork pins canonicity in
circuit.

## What this is not

The chain: `sgOk` is a hypothesis here (pickles defers it to the next proof's batch
opening), the message digests are two entries of `pub` like any other, and the packing
of statements across the cycle is `verify`'s. This is the per-proof checkpoint, at one chunk.

## Main definitions

* `Env`, `GroupHalf`, `ScalarHalf`: the three kinds of argument;
* `FopSide`, `FopParams.ofEnv`: the scalar half's side and its parameters from the
  environment;
* `IvpReadsExact`, `FopReadsExact`: the two reads with their slacks closed;
  `GroupHalf.Reads`, `ScalarHalf.Reads`: the reads at a half's own cells;
* `HalvesTies`: the claim cells of the two halves read the same claims across the field
  crossing, the digest crosses as `castDigest`, the evaluations and old accumulators are the
  proof's.

## Main results

* `twoHalves_iff_schnorr`: the two bits read `1` iff the claims are honest and the wire's
  Schnorr equation holds; `twoHalves_kimchiVerify`: with the deferred `sg` equation, iff
  `kimchiVerify` accepts at honest claims; at a step proof (Vesta commitments: the wrap
  circuit's group half, then the step circuit's scalar half) `twoHalves_kimchiVerify_vesta`,
  with the claim tie unfolded (`vesta_claim_tie`).

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
structure Env (C : CommitmentCurve) where
  /-- The SRS (`σ.h` the blinding base, `σ.k` the round count). -/
  σ : SRS C.Point
  /-- The verifier key, one chunk. -/
  cvk : KimchiVK C 1

/-! ## The group half -/

/-- The group half of a proof's verification, as one circuit runs it (for a step proof, the
wrap circuit): its valuation, its side (the ladder reading, the claim decode, the group facts),
the claim cells of its statement — the deferred values it scales by, the round challenges and
the fq digest its `incrementally_verify_proof` output is asserted equal to (`verify`) — and
the one bit it exports, the success bit. The `IvpOutput` itself is internal: existential in
`GroupHalf.Reads`, pinned to the claims by those assertions. -/
structure GroupHalf (C : CommitmentCurve) (sf : Type) where
  /-- The circuit's valuation (over the base field). -/
  V : Valuation C.BaseField
  /-- The shifted-scalar operations of the side. -/
  ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf
  /-- The side. -/
  side : IvpSide C V ops
  /-- The statement's claim cells: the deferred values, the round challenges, the digest. -/
  claims : UnfinalizedProof C.BaseField sf
  /-- The success bit: the opening's Schnorr equation at the claims. -/
  success : BoolVar C.BaseField

/-- The group half's claim cells from a `DeferredValues` record: the plonk claims, `ξ`, and
`cip`, `b`. -/
def DeferredValues.toIvpClaims {F sf : Type} (dv : DeferredValues F sf) :
    IvpClaims F sf :=
  ⟨⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩,
    dv.plonk.perm, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩,
   dv.xi, ⟨dv.combinedInnerProduct, dv.b⟩⟩

/-! ## The scalar half -/

/-- The scalar half's side: how a shifted claim cell reads as a scalar (the unshifted value
at the valuation), and the side's linearization token stream. -/
structure FopSide (C : CommitmentCurve) (V : Valuation C.ScalarField) (sf : Type) where
  /-- The scalar a shifted claim cell reads as: its value, unshifted. -/
  decode : sf → C.ScalarField
  /-- The linearization token stream of the side. -/
  toks : Array Linearization.PolishToken

/-- The scalar half of a proof's verification, as the next circuit runs it (for a step proof,
the following step circuit): its valuation, its side, the deferred claim cells with the fq
digest, the evaluation cells, the predecessor mask and previous-challenge cells, and its
output — the four checks, their conjunction and the expanded challenges. -/
structure ScalarHalf (C : CommitmentCurve) (sf : Type) (k : ℕ) where
  /-- The circuit's valuation (over the scalar field). -/
  V : Valuation C.ScalarField
  /-- The side. -/
  side : FopSide C V sf
  /-- The deferred claim cells and the fq digest cell. -/
  claims : UnfinalizedProof C.ScalarField sf
  /-- The evaluation cells: `ft(ζω)`, the public pair, the proof's evaluations. -/
  evals : AllEvals C.ScalarField
  /-- The predecessor mask (`proofs_verified_mask`), one bit per slot: `true` for a real
  predecessor, `false` for a dummy pad slot. -/
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
def FopParams.ofEnv {C : CommitmentCurve} (E : Env C) (toks : Array Linearization.PolishToken) :
    FopParams C.ScalarField :=
  { sponge := C.frParams
    endoLam := C.sponge.lam
    endo := E.cvk.endo
    mds := mdsOfParams C.frParams
    toks := toks
    shifts := fun i => E.cvk.shifts[i]
    srsLengthLog2 := E.σ.k
    zkRows := E.cvk.zkRows }

/-! ## The reads with their slacks closed -/

section Exact

variable {C : CommitmentCurve} {V : Valuation C.BaseField} {sf : Type}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- `IvpReads` with its slacks closed: the four plonk cells read the wire's fq
prechallenges exactly, the map-to-curve is the wire's `toGroup` (no sign), the returned
round prechallenges are the wire's and the Schnorr prechallenge is the wire's. What
`IvpReads` becomes once `lowest_128_bits` and the map-to-curve's square root are pinned in
circuit; `IvpReadsExact.toReads` is the inclusion. -/
def IvpReadsExact {nc : ℕ}
    (S : IvpSide C V ops)
    (σ : SRS C.Point)
    (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField)
    (claims : IvpClaims C.BaseField sf)
    (o : IvpOutput C.BaseField) :
    Prop :=
  let pre := fqRun C cvk cp (publicCommitment C σ cvk pub)
  let r := ipaRunAt C pre.warm (S.decode claims.deferred.combinedInnerProduct) cp.opening
  let run := runInput C σ cvk cp pub
  pre.digestElem = o.spongeDigest.val V ∧
  Reads128 V claims.plonk.chals.beta pre.beta ∧
  Reads128 V claims.plonk.chals.gamma pre.gamma ∧
  Reads128 V claims.plonk.chals.alpha pre.alpha ∧
  Reads128 V claims.plonk.chals.zeta pre.zeta ∧
  ∀ ξ₀, Reads128 V claims.xi ξ₀ →
    List.Forall₂ (Reads128 V) o.bulletproofChallenges r.2.1.toList ∧
    (((↑o.success : CVar C.BaseField).val V = 1) ↔
      schnorrAt C σ (C.toGroup r.1) (r.2.1.map fun m => endoExpand C.sponge.lam m.val)
        (endoExpand C.sponge.lam r.2.2.val)
        (S.decode claims.deferred.combinedInnerProduct) (S.decode claims.deferred.b)
        (combineCommitments C (endoExpand C.sponge.lam ξ₀.val) run.commitments.toArray)
        run.proof)

/-- The exact read implies the read, the base field being wider than 128 bits. -/
theorem IvpReadsExact.toReads {nc : ℕ}
    (hbig : 2 ^ 128 < C.base)
    {S : IvpSide C V ops}
    {σ : SRS C.Point}
    {cvk : KimchiVK C nc}
    {cp : KimchiProof C nc σ.k}
    {pub : Array C.ScalarField}
    {claims : IvpClaims C.BaseField sf}
    {o : IvpOutput C.BaseField}
    (h : IvpReadsExact S σ cvk cp pub claims o) :
    IvpReads S σ cvk cp pub claims o := by
  obtain ⟨hd, hβ, hγ, hα, hζ, hξ⟩ := h
  have hinj := castInj128_of_lt _ hbig
  refine ⟨hd, ⟨_, hβ, PrechallengeAlias.refl _ _⟩, ⟨_, hγ, PrechallengeAlias.refl _ _⟩,
    fun m hm => Reads128.unique hinj hα hm ▸ PrechallengeAlias.refl _ _,
    fun m hm => Reads128.unique hinj hζ hm ▸ PrechallengeAlias.refl _ _, fun ξ₀ hξ₀ => ?_⟩
  obtain ⟨hns, hiff⟩ := hξ ξ₀ hξ₀
  exact ⟨_, _, _, _, Or.inl rfl, hns,
    List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun m _ => PrechallengeAlias.refl _ m),
    PrechallengeAlias.refl _ _, Vector.toList_map, hiff⟩

end Exact

section ExactFr

variable {p : ℕ} [Fact p.Prime]

/-- `FopReadsWire` with its slack closed: `r` is the wire's `r` prechallenge exactly, and
`xiCorrect` reading `1` identifies the `ξ` claim with the wire's `ξ` prechallenge exactly.
`FopReadsExact.toWire` is the inclusion. -/
def FopReadsExact {sf : Type}
    (P : FopParams (ZMod p))
    (n : ℕ)
    (ω dv : ZMod p)
    (ms : List Bool)
    (cvs : List (List (ZMod p)))
    (u : UnfinalizedProof (ZMod p) sf)
    (w : AllEvals (ZMod p))
    (ζ α β γ permV cipV bV : ZMod p)
    (unshiftV : ZMod p → ZMod p)
    (V : Valuation (ZMod p))
    (o : FopOutput (ZMod p)) :
    Prop :=
  let pre := frPrechallenges P.sponge
    (frTranscript (u.spongeDigestBeforeEvaluations.val V) dv (w.ftEval1.val V)
      (w.pub.map fun x => #v[x.val V]) (w.evals.map fun x => #v[x.val V]))
  ∃ (ξ₀ r' : Prechallenge) (ĉ : List Prechallenge),
    Reads128 V u.deferredValues.xi ξ₀ ∧ r'.val = pre.2 ∧
    ((↑o.xiCorrect : CVar (ZMod p)).val V = 0 ∨ (↑o.xiCorrect : CVar (ZMod p)).val V = 1) ∧
    ((↑o.xiCorrect : CVar (ZMod p)).val V = 1 ↔ ξ₀.val = pre.1) ∧
    List.Forall₂ (Reads128 V) u.deferredValues.bulletproofChallenges ĉ ∧
    FopChecks P n ω ms cvs w ζ α β γ permV cipV bV unshiftV V o (endoExpand P.endoLam ξ₀.val)
      (endoExpand P.endoLam r'.val) (ĉ.map fun c => endoExpand P.endoLam c.val)

/-- The exact read implies the wire read. -/
theorem FopReadsExact.toWire {sf : Type}
    {P : FopParams (ZMod p)}
    {n : ℕ}
    {ω dv : ZMod p}
    {ms : List Bool}
    {cvs : List (List (ZMod p))}
    {u : UnfinalizedProof (ZMod p) sf}
    {w : AllEvals (ZMod p)}
    {ζ α β γ permV cipV bV : ZMod p}
    {unshiftV : ZMod p → ZMod p}
    {V : Valuation (ZMod p)}
    {o : FopOutput (ZMod p)}
    (h : FopReadsExact P n ω dv ms cvs u w ζ α β γ permV cipV bV unshiftV V o) :
    FopReadsWire P n ω dv ms cvs u w ζ α β γ permV cipV bV unshiftV V o := by
  obtain ⟨ξ₀, r', ĉ, hξ, hr, hbit, hxi, hĉ, hchecks⟩ := h
  exact ⟨ξ₀, r', ĉ, hξ, hr ▸ PrechallengeAlias.refl _ _, hbit,
    fun h1 => (hxi.1 h1) ▸ PrechallengeAlias.refl _ _, hĉ, hchecks⟩

end ExactFr

/-! ## The two halves' reads at their own cells -/

section AtCells

variable {C : CommitmentCurve} {sf sf' : Type}

/-- The group half's read (`verify`'s, exact): some `incrementally_verify_proof` output
satisfying `IvpReadsExact` at the half's side and claim cells, whose success bit is the
exported one and whose digest and round prechallenges the statement's claims equal —
`verify`'s two assertions. -/
def GroupHalf.Reads (E : Env C) (cp : KimchiProof C 1 E.σ.k) (pub : Array C.ScalarField)
    (G : GroupHalf C sf) : Prop :=
  ∃ o : IvpOutput C.BaseField,
    IvpReadsExact G.side E.σ E.cvk cp pub G.claims.deferredValues.toIvpClaims o ∧
    o.success = G.success ∧
    G.claims.spongeDigestBeforeEvaluations.val G.V = o.spongeDigest.val G.V ∧
    G.claims.deferredValues.bulletproofChallenges.map (·.val.val G.V)
      = o.bulletproofChallenges.map (·.val.val G.V)

/-- The scalar half's read: `FopReadsExact` with every parameter derived — `FopParams.ofEnv`,
the key's domain, the proof's recursion digest — and every value it checks at taken from the
half's cells: the `α`, `ζ` cells read as prechallenges, expanded at the sponge's eigenvalue
(the shape of `finalizeOtherProofStep_spec_fp`), `β`, `γ` as the cells' values, the three
shifted claims through the side's decode. -/
def ScalarHalf.Reads (E : Env C) (cp : KimchiProof C 1 E.σ.k) (Sc : ScalarHalf C sf' E.σ.k) :
    Prop :=
  let dv := Sc.claims.deferredValues
  ∀ a₀ z₀ : Prechallenge, Reads128 Sc.V dv.plonk.alpha a₀ → Reads128 Sc.V dv.plonk.zeta z₀ →
  FopReadsExact (p := C.scalar) (FopParams.ofEnv E Sc.side.toks) E.cvk.n E.cvk.omega
    (recDigest C (cp.olds.map (·.u))) Sc.mask.toList (Sc.prevChallenges.toList.map Vector.toList)
    Sc.claims Sc.evals
    (endoExpand C.sponge.lam z₀.val) (endoExpand C.sponge.lam a₀.val)
    (dv.plonk.beta.val.val Sc.V) (dv.plonk.gamma.val.val Sc.V)
    (Sc.side.decode dv.plonk.perm) (Sc.side.decode dv.combinedInnerProduct)
    (Sc.side.decode dv.b) id Sc.V Sc.out

end AtCells

/-! ## The ties between the two halves -/

section Ties

variable {C : CommitmentCurve} {sf sf' : Type}

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
    (G : GroupHalf C sf) (Sc : ScalarHalf C sf' E.σ.k) : Prop where
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
    List.Forall₂ (Reads128 G.V) G.claims.deferredValues.bulletproofChallenges ms ∧
    List.Forall₂ (Reads128 Sc.V) Sc.claims.deferredValues.bulletproofChallenges ms
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
    m.val = (frPrechallenges C.frParams (frTranscript (runOracles C E.σ E.cvk cp pub).digest
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
private theorem linEvals_one {C : CommitmentCurve} {k : ℕ} (cp : KimchiProof C 1 k)
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
private theorem zipSeg_toList_one {C : CommitmentCurve} (comm : Vector C.Point 1)
    (ev : PointEvaluations (Vector C.ScalarField 1)) :
    (zipSeg C comm ev).toList = [(comm[0], ev.zeta[0], ev.zetaOmega[0])] := by
  simp [zipSeg, Vector.toList_ofFn, List.ofFn_succ]

/-- The tail rows as a list: the four regions' lists (the vector append is typed at the
literal `tailRowCount`, which `Vector.toList_append` does not see through). -/
private theorem tailRows_toList {C : CommitmentCurve} {k : ℕ} (cvk : KimchiVK C 1)
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
              (mdsOfParams C.frParams) o.alpha o.beta o.gamma o.zeta pe.zeta[0] (linEvals e),
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

/-- **The two bits are the wire's acceptance at honest claims.** Without `SgOk`: the two bits
read `1` iff the claims are the wire's own values and the opening's Schnorr equation holds at
the wire's transcript — `verifyWith`'s first conjunct. -/
theorem twoHalves_iff_schnorr
    (E : Env C)
    (hbase : 2 ^ 128 < C.base)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C 1 E.σ.k)
    (pub : Array C.ScalarField)
    -- the group half
    (G : GroupHalf C sf)
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
      ↔ Sc.ClaimsHonest E cp pub ∧
        schnorrAt C E.σ tr.1 tr.2.1 tr.2.2 (cipOf run)
          (combinedB (fun i => tr.2.1[i]) run.evalscale run.pointFn)
          (combineCommitments C run.polyscale run.commitments.toArray) run.proof := by
  intro run tr
  -- the group half's read
  obtain ⟨o, hx, hsucc, hdig, hbpc⟩ := hg
  simp only [IvpReadsExact, DeferredValues.toIvpClaims] at hx
  obtain ⟨hdE, hβG, hγG, hαG, hζG, hξG⟩ := hx
  -- the shared prechallenges
  obtain ⟨a₀, hαGa, hαSa⟩ := ht.alpha
  obtain ⟨z₀, hζGz, hζSz⟩ := ht.zeta
  obtain ⟨b₀, hβGb, hβSb⟩ := ht.beta
  obtain ⟨g₀, hγGg, hγSg⟩ := ht.gamma
  obtain ⟨ξ₀, hξGx, hξSx⟩ := ht.xi
  obtain ⟨hns, hiff⟩ := hξG ξ₀ hξGx
  rw [hsucc] at hiff
  have hinjG := castInj128_of_lt _ hbase
  have hinjS := castInj128_of_lt _ hscalar
  -- the scalar half's read, at the shared `α`, `ζ`
  have hs := hs a₀ z₀ hαSa hζSz
  simp only [FopReadsExact, FopChecks, FopParams.ofEnv, id_eq] at hs
  obtain ⟨ξ₀', r', ĉ, hξS, hr', -, hxiIff, hĉ, hcipC, hbC, hpermC, hfin, -⟩ := hs
  obtain rfl : ξ₀ = ξ₀' := Reads128.unique hinjS hξSx hξS
  -- the scalar half's inputs are the run's
  have hζ : endoExpand C.sponge.lam z₀.val = (runOracles C E.σ E.cvk cp pub).zeta := by
    simp only [runOracles, fqOracles, FqRun.expand]
    rw [Reads128.unique hinjG hζGz hζG]
  have hα : endoExpand C.sponge.lam a₀.val = (runOracles C E.σ E.cvk cp pub).alpha := by
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
  rw [hd, ht.ftEval1, ht.pubEvals, ht.evals] at hr' hxiIff
  have hr : endoExpand C.sponge.lam r'.val = run.evalscale := by
    show _ = (frOracles C cp _ _).r
    rw [frOracles_eq_frPrechallenges, hr']
  have hxi : (↑Sc.out.xiCorrect : CVar C.ScalarField).val Sc.V = 1
      ↔ ∃ m : Prechallenge, Reads128 Sc.V Sc.claims.deferredValues.xi m ∧
        m.val = (frPrechallenges C.frParams (frTranscript (runOracles C E.σ E.cvk cp pub).digest
            (recDigest C (cp.olds.map (·.u))) cp.ftEval1 (runPubEvals C E.σ E.cvk cp pub)
            cp.evals)).1 := by
    rw [hxiIff]
    constructor
    · exact fun h => ⟨ξ₀, hξS, h⟩
    · rintro ⟨m, hm, hmv⟩
      rw [Reads128.unique hinjS hξS hm, hmv]
  have hξrun : (∃ m : Prechallenge, Reads128 Sc.V Sc.claims.deferredValues.xi m ∧
        m.val = (frPrechallenges C.frParams (frTranscript (runOracles C E.σ E.cvk cp pub).digest
            (recDigest C (cp.olds.map (·.u))) cp.ftEval1 (runPubEvals C E.σ E.cvk cp pub)
            cp.evals)).1) →
      endoExpand C.sponge.lam ξ₀.val = run.polyscale := by
    rintro ⟨m, hm, hmv⟩
    rw [Reads128.unique hinjS hξS hm, hmv]
    show _ = (frOracles C cp _ _).xi
    rw [frOracles_eq_frPrechallenges]
  -- the round challenges: the cell lists' readings are equations of lists
  obtain ⟨ms, hmsG, hmsS⟩ := ht.chals
  rw [forall₂_reads128_iff] at hmsG hmsS hns hĉ
  have hĉeq : ĉ = (ipaRunAt C (fqRun C E.cvk cp (publicCommitment C E.σ E.cvk pub)).warm
      (G.side.decode G.claims.deferredValues.combinedInnerProduct) cp.opening).2.1.toList :=
    (List.map_injective_iff.mpr hinjS.prechallenge_injective (hĉ.symm.trans hmsS)).trans
      (List.map_injective_iff.mpr hinjG.prechallenge_injective (hmsG.symm.trans (hbpc.trans hns)))
  -- the four checks, in wire terms
  rw [hζ, hα, hβ, hγ, hev, hpz, hpzo, ht.ftEval1] at hcipC
  rw [hζ] at hbC
  rw [hζ, hα, hβ, hγ, hev] at hpermC
  have hcipIff : endoExpand C.sponge.lam ξ₀.val = run.polyscale →
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
                (fun m => endoExpand C.sponge.lam m.val))[i]) run.evalscale run.pointFn := by
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
  simp only [ScalarHalf.ClaimsHonest, ClaimsHonest, run, tr, transcriptFrom_eq, hwarm, hproof]
  rw [hfin]
  simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
  rw [hxi, hbIff, hpermIff]
  constructor
  · rintro ⟨hsG, hxiV, hb, hcip, hperm⟩
    have hξv := hξrun hxiV
    have hcip' := (hcipIff hξv).1 hcip
    have hcipG : G.side.decode G.claims.deferredValues.combinedInnerProduct = cipOf run :=
      ht.cip.symm.trans hcip'
    rw [hcipG] at hiff hb
    rw [hξv, ← ht.b, hb] at hiff
    exact ⟨⟨hcip', hb, hperm, hxiV⟩, hiff.1 hsG⟩
  · rintro ⟨⟨hcip, hb, hperm, hxiV⟩, hschnorr⟩
    have hξv := hξrun hxiV
    have hcipG : G.side.decode G.claims.deferredValues.combinedInnerProduct = cipOf run :=
      ht.cip.symm.trans hcip
    rw [hcipG] at hiff ⊢
    rw [hξv, ← ht.b, hb] at hiff
    exact ⟨hiff.2 hschnorr, hxiV, hb, (hcipIff hξv).2 hcip, hperm⟩

/-- **The two halves accept exactly when the wire verifier does at honest claims, given the
deferred `sg` equation.** In the environment `E`, for the proof `(cp, pub)`: with the group
half reading exactly and the scalar half reading exactly at their cells, tied, and the
guards, the success bit and the `finalized` bit read `1` and `SgOk` holds iff `kimchiVerify`
accepts and the claims are the wire's own values. (`kimchiVerify` recomputes the claims and
never sees the cells, so the honest-claims conjunct is what `finalized` adds.) -/
theorem twoHalves_kimchiVerify
    (E : Env C)
    (hbase : 2 ^ 128 < C.base)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C 1 E.σ.k)
    (pub : Array C.ScalarField)
    (hguard : Guards C E.cvk cp pub)
    -- the group half
    (G : GroupHalf C sf)
    (hg : G.Reads E cp pub)
    -- the scalar half
    (Sc : ScalarHalf C sf' E.σ.k)
    (hs : Sc.Reads E cp)
    -- across the two
    (ht : HalvesTies E cp pub G Sc) :
    ((↑G.success : CVar C.BaseField).val G.V = 1
        ∧ (↑Sc.out.finalized : CVar C.ScalarField).val Sc.V = 1)
        ∧ SgOk E cp pub
      ↔ kimchiVerify C E.σ E.cvk cp pub = true ∧ Sc.ClaimsHonest E cp pub := by
  have h := twoHalves_iff_schnorr E hbase hscalar cp pub G hg Sc hs ht
  -- the body reflection: under the guards, the warm-sponge IPA finish on the run's input
  simp only [transcriptFrom_eq] at h
  rw [h, kimchiVerify_reflects, and_iff_right hguard]
  simp only [SgOk, verifyFrom, transcriptFrom_eq, verifyWith_eq]
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
  decode x := (stepShiftOps.reading (V := V) (by decide)).unshiftV (x.val.val V)
  toks := Linearization.fpTokens

/-- The wrap circuit's group half of a step proof: `wrapSide` at the circuit's valuation. -/
def GroupHalf.wrap (V : Valuation Fq) (claims : UnfinalizedProof Fq (Type1 (FVar Fq)))
    (success : BoolVar Fq) : GroupHalf IpaVesta.curve (Type1 (FVar Fq)) :=
  ⟨V, IpaScalarOps.wrap, wrapSide V, claims, success⟩

/-- The step circuit's scalar half of a step proof: `fopStep` at the circuit's valuation, at
the round count `k` of the finalized proof's SRS (`StepIPARounds` when deployed). -/
def ScalarHalf.step {k : ℕ} (V : Valuation Fp) (claims : UnfinalizedProof Fp (Type1 (FVar Fp)))
    (evals : AllEvals Fp) (mask : Vector Bool MaxProofsVerified)
    (prevChallenges : Vector (Vector Fp k) MaxProofsVerified) (out : FopOutput Fp) :
    ScalarHalf IpaVesta.curve (Type1 (FVar Fp)) k :=
  ⟨V, fopStep V, claims, evals, mask, prevChallenges, out⟩

/-- At a step proof the claim tie is the `Fp` cell's value equal to the `Fq` cell's value as
an integer: both sides unshift at `255` bits, and the unshift is injective. -/
theorem vesta_claim_tie {Vg : Valuation Fq} {Vs : Valuation Fp}
    (x : Type1 (FVar Fp))
    (y : Type1 (FVar Fq)) :
    (fopStep Vs).decode x = (wrapSide Vg).decode y ↔ x.val.val Vs = ((y.val.val Vg).val : Fp) := by
  simp only [fopStep, stepShiftOps.reading, wrapSide, wrapDecode, Type1.fromShifted,
    Pasta.Shifted.unshiftType1]
  constructor
  · intro h
    have h2 : (2 : Fp) ≠ 0 := by decide
    exact mul_left_cancel₀ h2 (add_right_cancel (add_right_cancel h))
  · intro h
    rw [h]

/-- **A step proof's two halves accept exactly when `kimchiVerify` does.** The wrap circuit's
group half, then the step circuit's scalar half, tied, with the guards. -/
theorem twoHalves_kimchiVerify_vesta
    (E : Env IpaVesta.curve)
    (cp : KimchiProof IpaVesta.curve 1 E.σ.k)
    (pub : Array Fp)
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    -- the wrap circuit: its valuation, its statement's claims, its success bit, its read
    (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof Fq (Type1 (FVar Fq)))
    (successG : BoolVar Fq)
    (hg : (GroupHalf.wrap Vg claimsG successG).Reads E cp pub)
    -- the next step circuit: its valuation, its cells, its output, its read
    (Vs : Valuation Fp)
    (claimsS : UnfinalizedProof Fp (Type1 (FVar Fp)))
    (evals : AllEvals Fp)
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
  twoHalves_kimchiVerify E (by norm_num [PALLAS_SCALAR_CARD]) (by norm_num [PALLAS_BASE_CARD])
    cp pub hguard _ hg _ hs ht

end StepProof

end Pickles
