import Kimchi.Verifier.Kimchi

/-!
# The wire boundary: serde-typed records and their parse

The records here mirror proof-systems' serde records for the kimchi proof and verifier key.
Fixed dimensions are `Vector`s, since serde rejects a wrong length at deserialization;
per-chunk payloads are unchecked `Array`s. `KimchiProof.check` and `KimchiVK.check` parse
them into the checked records `Kimchi.Verifier.KimchiProof` and `Kimchi.Verifier.KimchiVK`,
which carry the chunk count in their types, so a checked record cannot hold a ragged proof.

## What the parse checks

The parse transcribes the length checks of `kimchi/src/verifier.rs`: every evaluation vector
at the run's chunk count, the quotient's chunk bound, and carried public evaluations beyond
one chunk. On those, rejecting ragged input matches the upstream verifier's error returns.
It also pins lengths the upstream verifier never checks; the note above `KimchiProof.check`
lists these strengthenings.

## Clients

There is no verifier here. A client parses at the run's chunk count (`runNc`) and calls
`Kimchi.Verifier.kimchiVerify` on the checked records. `Kimchi.Verifier.Kimchi` does not
import this module, so the verifier body reads checked data only.
-/

open Bulletproof

namespace Kimchi.Verifier.Wire

open CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Verifier (PointEvaluations ProofEvaluations PubEvalSrc)

variable (C : Ipa.KimchiCurve)

/-! ## The wire records -/

/-- A wire polynomial commitment: its per-chunk points, of unchecked length. `checkChunks`
validates the count against the run's chunk count. -/
private abbrev PolyComm (C : Ipa.KimchiCurve) := Array C.Point

/-- A wire old accumulator: the previous opening's commitment as a chunk vector and its
expanded round challenges, both unchecked. -/
structure RecursionChallenge (C : Ipa.KimchiCurve) where
  /-- The commitment; the parse pins it to one chunk. -/
  comm : PolyComm C
  /-- The round challenges; the parse pins them to the opening's round count. -/
  chals : Array C.ScalarField

/-- The kimchi proof wire record for the basic gate set: fixed dimensions are `Vector`s,
chunk payloads unchecked arrays. It carries no lookup data. -/
structure KimchiProof (C : Ipa.KimchiCurve) where
  /-- The 15 witness-column commitments. -/
  wComm : Vector (PolyComm C) wCols
  /-- The permutation-aggregation commitment. -/
  zComm : PolyComm C
  /-- The quotient commitment; the parse bounds it to seven chunks per run chunk. -/
  tComm : PolyComm C
  /-- The claimed evaluations, per column family and per chunk. -/
  evals : ProofEvaluations (Array C.ScalarField)
  /-- The carried public evaluations, held beside `evals` rather than inside it because the
  natural field name is a Lean keyword. The parse requires them beyond one chunk; when
  present they replace the barycentric computation at any chunk count. -/
  pubEvals : Option (PointEvaluations (Array C.ScalarField))
  /-- `ft(ζω)` (Maller's optimization) — the ft row is single-chunk. -/
  ftEval1 : C.ScalarField
  /-- The batched IPA opening proof in its wire form; the parse checks its round count. -/
  opening : Ipa.Wire.Proof C
  /-- The old accumulators, unchecked. -/
  prevChallenges : Array (RecursionChallenge C)

/-- The kimchi verifier-key wire record: fixed dimensions are `Vector`s, chunk payloads
unchecked arrays. The SRS stays separate; a client derives the chunk count from the domain
and the SRS (`runNc`). -/
structure KimchiVK (C : Ipa.KimchiCurve) where
  /-- The domain size exponent: `n = 2 ^ domainLog2`. -/
  domainLog2 : ℕ
  /-- The domain generator `ω`. -/
  omega : C.ScalarField
  /-- The 7 permutation commitments. -/
  sigmaComm : Vector (PolyComm C) permCols
  /-- The 15 coefficient commitments. -/
  coefficientsComm : Vector (PolyComm C) coeffCols
  /-- The generic selector's commitment. -/
  genericComm : PolyComm C
  /-- The poseidon selector's commitment, the one selector whose wire key differs from its
  field name; the fixture decoder maps it. -/
  poseidonComm : PolyComm C
  /-- The completeAdd selector's commitment. -/
  completeAddComm : PolyComm C
  /-- The varBaseMul selector's commitment. -/
  mulComm : PolyComm C
  /-- The endoMul selector's commitment. -/
  emulComm : PolyComm C
  /-- The endoScalar selector's commitment. -/
  endomulScalarComm : PolyComm C
  /-- The 7 permutation shifts. -/
  shifts : Vector C.ScalarField permCols
  /-- The number of zero-knowledge rows, carried as data rather than derived from the chunk
  count. -/
  zkRows : ℕ
  /-- The accumulator count the key was built with. -/
  prevChallenges : ℕ
  /-- The endomorphism coefficient `ftEval0` reads: not serialized, a model input like
  `digest`. -/
  endo : C.ScalarField
  /-- The precomputed key digest, an input rather than computed from the key. -/
  digest : C.BaseField
  /-- The Lagrange-basis commitments: SRS-derived data, a model input like `digest`. -/
  lagrangeBasis : Array (PolyComm C)

/-- A chunk vector validated to the run's chunk count. -/
private def checkChunks {α : Type*} (nc : ℕ) (a : Array α) : Option (Vector α nc) :=
  if h : a.size = nc then some ⟨a, h⟩ else none

/-- Validate an evaluation pair's chunk vectors. -/
private def checkPointEvals {F : Type*} (nc : ℕ) (e : PointEvaluations (Array F)) :
    Option (PointEvaluations (Vector F nc)) := do
  return { zeta := ← checkChunks nc e.zeta, zetaOmega := ← checkChunks nc e.zetaOmega }

/-- Validate every evaluation pair of the record. -/
private def checkEvals {F : Type*} (nc : ℕ) (e : ProofEvaluations (Array F)) :
    Option (ProofEvaluations (Vector F nc)) := do
  return { w := ← e.w.mapM (checkPointEvals nc)
           z := ← checkPointEvals nc e.z
           s := ← e.s.mapM (checkPointEvals nc)
           coefficients := ← e.coefficients.mapM (checkPointEvals nc)
           genericSelector := ← checkPointEvals nc e.genericSelector
           poseidonSelector := ← checkPointEvals nc e.poseidonSelector
           completeAddSelector := ← checkPointEvals nc e.completeAddSelector
           mulSelector := ← checkPointEvals nc e.mulSelector
           emulSelector := ← checkPointEvals nc e.emulSelector
           endomulScalarSelector := ← checkPointEvals nc e.endomulScalarSelector }

/-! ## The parse's strengthenings

The upstream verifier checks two lengths: every evaluation vector against the chunk count,
and the quotient commitment's chunk count from above. The parse also pins the witness and
permutation-aggregation commitments to the run's chunk count, which upstream never checks:
ragged vectors there flow into the batch equations instead of being rejected. The checked
record is uniform by type, so an upstream-accepted run with ragged commitments has no Lean
counterpart. Such a run should fail the batched opening, but that is an argument, not a
check. `KimchiVK.check` pins every committed column of the key the same way, which upstream
likewise never checks; honest keys are uniform.

The quotient commitment is not pinned non-empty: upstream bounds its chunk count from above
only, so the empty quotient parses.
-/

/-- **The proof check**, at the run's chunk count `nc` and the SRS's round count `k`. Every
evaluation vector must have `nc` chunks and the quotient at most `7 * nc`; the witness and
permutation-aggregation commitments must have `nc` chunks, each old accumulator one chunk
and `k` challenges, and the opening `k` rounds. Public evaluations are required unless
`nc = 1`. The pins upstream does not check are the strengthenings in the note above. -/
def KimchiProof.check {C : Ipa.KimchiCurve} (nc k : ℕ) (p : KimchiProof C) :
    Option (Kimchi.Verifier.KimchiProof C nc k) := do
  let wComm ← p.wComm.mapM (checkChunks nc)
  let zComm ← checkChunks nc p.zComm
  let opening ← p.opening.check k
  if htc : p.tComm.size ≤ 7 * nc then
    let evals ← checkEvals nc p.evals
    let pubEvals ← match p.pubEvals with
      | some pe => (checkPointEvals nc pe).map .carried
      | none => if h : nc = 1 then some (.barycentric h) else none
    -- an accumulator is one chunk at `k` round challenges, the deployed case; splitting a
    -- challenge polynomial longer than the SRS into several chunks is not transcribed
    let olds ← p.prevChallenges.mapM fun rc => do
      let comm ← checkChunks 1 rc.comm
      let u ← checkChunks k rc.chals
      return ({ sg := comm[0], u } : Kimchi.Verifier.Accumulator C k)
    return { wComm, zComm, tComm := p.tComm, tComm_le := htc, evals, pubEvals,
             ftEval1 := p.ftEval1, opening := opening, olds }
  else none

/-- **The key check**: every committed column validated to `nc` chunks, the Lagrange basis
included in full. The basis is SRS-derived and chunked uniformly, so ragged basis data
is rejected. -/
def KimchiVK.check {C : Ipa.KimchiCurve} (nc : ℕ) (vk : KimchiVK C) :
    Option (Kimchi.Verifier.KimchiVK C nc) := do
  return { domainLog2 := vk.domainLog2, omega := vk.omega
           sigmaComm := ← vk.sigmaComm.mapM (checkChunks nc)
           coefficientsComm := ← vk.coefficientsComm.mapM (checkChunks nc)
           genericComm := ← checkChunks nc vk.genericComm
           poseidonComm := ← checkChunks nc vk.poseidonComm
           completeAddComm := ← checkChunks nc vk.completeAddComm
           mulComm := ← checkChunks nc vk.mulComm
           emulComm := ← checkChunks nc vk.emulComm
           endomulScalarComm := ← checkChunks nc vk.endomulScalarComm
           shifts := vk.shifts, zkRows := vk.zkRows, prevChallenges := vk.prevChallenges
           endo := vk.endo, digest := vk.digest
           lagrangeBasis := ← vk.lagrangeBasis.mapM (checkChunks nc) }

/-- The run's chunk count, the upstream verifier's formula: one chunk when the domain is no
larger than the SRS, else the domain size over the SRS size. Clients parse at this count. -/
def runNc (σ : SRS C.Point) (vk : KimchiVK C) : ℕ :=
  if vk.domainLog2 < σ.k then 1 else 2 ^ (vk.domainLog2 - σ.k)

end Kimchi.Verifier.Wire
