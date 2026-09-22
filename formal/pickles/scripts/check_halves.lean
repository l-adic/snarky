import PicklesFixture
import Pickles.TwoHalves
import Pickles.StepProof
import Snarky.Kimchi.Backend.Compile
import KimchiFixture.Cache
import BulletproofFixture.SRSLoader
import CompElliptic.Fields.Pasta

/-!
# The circuit halves, satisfied on proofs the PureScript suite produced

The two-halves capstones relate a circuit's success bits to `kimchiVerify` for any table
that satisfies the circuit. They say nothing about whether a real proof produces such a
table. This driver runs the modelled half through the Lean prover interpreter on the
inputs of a real proof — the advice code, which nothing else in the tree exercises — and
decides whether the table it produced satisfies every constraint, with the success bits
read back off it.

A scalar half finalizes the proof one level down: the step circuit's finalizes the *step*
proof its verified wrap proof wrapped, the wrap circuit's finalizes the *wrap* proof its
step proof verified in a slot — each proof's scalar-side checks live in the other field.
So a step-half run takes a wrap entry of the cache, follows its `step` link, and lays out
`finalize_other_proof`'s input from the two: the claims, the digest and the branch data
from the wrap statement (the wrap entry's public input), the evaluations and accumulators
from the step proof. A wrap-half run takes a step entry, follows a slot's `prevs` link to
the wrap proof it verified, and lays the input out from that slot of the step statement
and the wrap proof. The same pairs drive the two group halves: the step circuit's
(`verifyProof`, on the step→wrap pair: the wrap statement and proof, the slot's
unfinalized proof) and the wrap circuit's (`incrementallyVerifyProof` on the conditional
sponge, on the wrap→step pair: the wrap statement's claims, the step statement and proof,
the step proof's accumulators under the branch data's mask), each with the verified key's
commitments and the Lagrange bases as constants.

Per run: the interpreter completes (a), the table satisfies the assembled system (b),
the success bits read 1 (c) — `finalized` and its four conjuncts for a scalar half, the
opening's `success` for the group half — and, per step-half run, `kimchiVerify` accepts
both proofs (d) — against the SRS they were made with (`srs-cache/`, cut to each proof's
round count) and the Lagrange basis computed from it, memoised under `lagrange-cache/`.

The carry (e): a proof's deferred `sg` obligation is an old accumulator of the next proof on
its curve — wrap k−1's in wrap k's, through the step between them; step k−1's in step k's,
through the wrap between them. Per linked pair, `Pickles.Carry` is decided on the two checked
proofs (the accumulator is the predecessor's `sg` with the wire's round challenges of the
predecessor), `AccOk` on the accumulator, `sgOk` on the predecessor, and the two verdicts
must agree (`sgOk_iff_accOk` on the data). An unlinked accumulator — a front pad, a
base-case slot — must satisfy `AccOk` on its own: the dummy's `sg` commits the dummy
challenges. So no accumulator in the file is taken from the prover's list on trust.

The theorems (f): per wrap→step pair the hypotheses of `Pickles.stepProof_kimchiVerify_vesta`
that are facts about data (`theoremHyps`), per step→wrap pair those of
`Pickles.wrapProof_kimchiVerify_pallas` (`wrapTheoremHyps`) — each with the statement's two
circuits as `compile` builds them, so either theorem's assumptions are shown to hold together
on a proof the real prover made.

Run: `PROOF_CACHE=<file> lake exe check-halves` from `formal/`; the default is
`SimpleChain.json`. `SRS_CACHE_DIR` and `LAGRANGE_CACHE_DIR` relocate the two caches.
`HALVES` narrows the run to a comma-separated subset of `step`, `wrap`, `step-group`,
`wrap-group`, `verify`, `carry`, `theorem` (the default is all seven). The `step` and
`verify` lanes run at the entry's chunk count; the others, whose environment fixes one chunk,
reject a chunked entry.
-/

open Lean Snarky Snarky.Kimchi PicklesFixture Kimchi.Fixture Bulletproof
open CompElliptic.Fields.Pasta

/-- Wrap proofs: Pallas commitments, statement cells in the wrap field. -/
abbrev CW := IpaPallas.curve
/-- Step proofs: Vesta commitments, statement cells in the step field. -/
abbrev CS := IpaVesta.curve

/-- A wrap-field cell as the step-field value it carries: the shifted scalars are `Type1`
representatives, the challenges are 128-bit, the digests are full elements — all
transported by value. -/
def toStep (x : CW.ScalarField) : Fp := (x.val : Fp)

/-- A step-field cell as the wrap-field value it carries — a digest, a 128-bit challenge, a
split half or a Type1 register, all transported by value. -/
def toWrap (x : CS.ScalarField) : Fq := (x.val : Fq)

/-- The wrap statement's packed branch data `4·domain_log2 + m₀ + 2·m₁`: `domain_log2` and
the two mask bits in slot order. The mask reads slot `i` as "at least `2 − i` proofs", so
the real accumulators sit in the LAST slots and padding goes in front; a step statement of
`n ≤ 2` slots reads the last `n` bits. -/
def unpackBranchData (bd : ℕ) : ℕ × Vector ℕ 2 := (bd / 4, #v[bd % 2, (bd / 2) % 2])

/-- A finalized proof's evaluations off its checked wire record, at one chunk: `ft(ζω)`, the
carried public pair, the record. -/
def allEvalsOf (C : Ipa.KimchiCurve) {k : ℕ} (cp : Kimchi.Verifier.KimchiProof C 1 k) :
    Except String (Pickles.AllEvals C.ScalarField) := do
  let pub ← match cp.pubEvals with
    | .carried pe => pure (pe.map fun (v : Vector C.ScalarField 1) => v[0])
    | .barycentric _ => throw "the proof carries no public evaluations (one-chunk wire form)"
  return { ftEval1 := cp.ftEval1, pub
           evals := cp.evals.map fun (v : Vector C.ScalarField 1) => v[0] }

/-- A finalized proof's evaluations off its checked wire record at `nc` chunks: `ft(ζω)`,
the carried public chunks, the record's chunks. -/
def chunkedEvalsOf (C : Ipa.KimchiCurve) {nc k : ℕ} (cp : Kimchi.Verifier.KimchiProof C nc k) :
    Except String (Pickles.ChunkedEvals nc C.ScalarField) := do
  let pub ← match cp.pubEvals with
    | .carried pe => pure pe
    | .barycentric _ => throw "the proof carries no public evaluations (one-chunk wire form)"
  return ⟨cp.ftEval1, pub, cp.evals⟩

/-- A wrap statement off a wrap proof's public input, carried into `F` by `conv`
(`Pickles.WrapStatement.packed`'s order): `cip, b, ζ^{2^k}, ζⁿ, perm` at 0–4, `β, γ` at 5–6,
`α, ζ, ξ` at 7–9, the three digests at 10–12 (the step proof's sponge digest first), the `k`
round challenges from 13, the packed branch data `4·domain_log2 + m₀ + 2·m₁` last, unpacked
(`unpackBranchData`). -/
def wrapStatementOf {F : Type} [Field F] (conv : Fq → F) (k : ℕ) (c : Array Fq) :
    Except String (Pickles.WrapStatement k F Bool (Type1 F)) := do
  unless 14 + k ≤ c.size do throw s!"wrap public input: {c.size} cells at {k} rounds"
  let g (i : ℕ) : F := conv (c.getD i 0)
  let (domainLog2, mask) := unpackBranchData (c.getD (13 + k) 0).val
  return { proofState :=
             { deferredValues :=
                 { plonk := { alpha := ⟨g 7⟩, beta := ⟨g 5⟩, gamma := ⟨g 6⟩, zeta := ⟨g 8⟩,
                              perm := ⟨g 4⟩, zetaToSrsLength := ⟨g 2⟩, zetaToDomainSize := ⟨g 3⟩ }
                   combinedInnerProduct := ⟨g 0⟩, b := ⟨g 1⟩, xi := ⟨g 9⟩
                   bulletproofChallenges := Vector.ofFn fun j => ⟨g (13 + j)⟩
                   branchData := { domainLog2 := (domainLog2 : F)
                                   proofsVerifiedMask := mask.map (· == 1) } }
               spongeDigestBeforeEvaluations := g 10
               messagesForNextWrapProof := g 11 }
           messagesForNextStepProof := g 12 }

/-- A step statement off a step proof's public input, carried into `F` by `conv`, at `k`
rounds per slot and `n` slots (`Pickles.StepStatement.packed`'s order): per slot the five
split claims `cip, b, ζ^{2^k}, ζⁿ, perm` as `(half, parity)` pairs at 0–9, the digest at 10,
`β, γ` at 11–12, `α, ζ, ξ` at 13–15, the `k` round challenges from 16, `should_finalize`
last; then `messages_for_next_step_proof` and the `n` `messages_for_next_wrap_proof`
digests. -/
def stepStatementOf {F : Type} [Field F] (conv : Fp → F) (k n : ℕ) (c : Array Fp) :
    Except String (Pickles.StepStatement k n F Bool (Type2 (SplitField F Bool))) := do
  let slotSize := 17 + k
  unless c.size = n * slotSize + 1 + n do
    throw s!"step public input: {c.size} cells, expected {n * slotSize + 1 + n} at {n} slots \
      of {k} rounds"
  let g (i : ℕ) : F := conv (c.getD i 0)
  let bit (i : ℕ) : Bool := decide (c.getD i 0 = 1)
  let slot (s : ℕ) : Pickles.UnfinalizedProof k F Bool (Type2 (SplitField F Bool)) :=
    let b := s * slotSize
    let split (i : ℕ) : Type2 (SplitField F Bool) := ⟨⟨g (b + 2 * i), bit (b + 2 * i + 1)⟩⟩
    { deferredValues :=
        { plonk := { alpha := ⟨g (b + 13)⟩, beta := ⟨g (b + 11)⟩, gamma := ⟨g (b + 12)⟩,
                     zeta := ⟨g (b + 14)⟩, perm := split 4, zetaToSrsLength := split 2,
                     zetaToDomainSize := split 3 }
          combinedInnerProduct := split 0, b := split 1, xi := ⟨g (b + 15)⟩
          bulletproofChallenges := Vector.ofFn fun j => ⟨g (b + 16 + j)⟩ }
      shouldFinalize := bit (b + 16 + k)
      spongeDigestBeforeEvaluations := g (b + 10) }
  return { proofState := { unfinalizedProofs := Vector.ofFn fun i => slot i
                           messagesForNextStepProof := g (n * slotSize) }
           messagesForNextWrapProof := Vector.ofFn fun i => g (n * slotSize + 1 + i) }

/-- A checked one-chunk proof's cells for a group half: its commitments as affine points, the
opening with `z₁`, `z₂` through `shift` (the side's shifted register). -/
def ivpProofOf (C : Ipa.KimchiCurve) {k : ℕ} {sf : Type} (shift : C.ScalarField → sf)
    (cp : Kimchi.Verifier.KimchiProof C 1 k) :
    Except String (Pickles.IvpProof k C.BaseField sf) := do
  let pt (P : C.Point) : AffinePoint C.BaseField := ⟨P.x, P.y⟩
  let tComm : Vector (AffinePoint C.BaseField) 7 ←
    if h : cp.tComm.size = 7 then pure ⟨cp.tComm.map pt, by simp [h]⟩
    else throw s!"t_comm: {cp.tComm.size} chunks, expected 7"
  return { wComm := cp.wComm.map fun (v : Vector C.Point 1) => pt v[0]
           zComm := pt cp.zComm[0]
           tComm
           opening := { lr := cp.opening.lr.map fun q => (pt q.1, pt q.2)
                        z1 := shift cp.opening.z1, z2 := shift cp.opening.z2
                        delta := pt cp.opening.delta, sg := pt cp.opening.sg } }

/-- A checked proof's accumulators' `sg`, as `m` affine points: the proof's own in the LAST
slots (`unpackBranchData`), `pad` in front of them. A proof carries one accumulator per real
predecessor of its rule, which a statement padded to the system's width exceeds — a
heterogeneous system has rules with fewer predecessors than slots — and a padding slot's
keep bit is off, so its point is never absorbed; it only has to be a point. -/
def sgOldOf (C : Ipa.KimchiCurve) {k : ℕ} (m : ℕ) (pad : C.Point)
    (cp : Kimchi.Verifier.KimchiProof C 1 k) :
    Except String (Vector (AffinePoint C.BaseField) m) :=
  let pt (P : C.Point) : AffinePoint C.BaseField := ⟨P.x, P.y⟩
  let sgs := cp.olds.map fun a => pt a.sg
  if sgs.size ≤ m then
    let all := Array.replicate (m - sgs.size) (pt pad) ++ sgs
    if h : all.size = m then pure ⟨all, h⟩ else throw s!"accumulators: {sgs.size} of {m}"
  else throw s!"accumulators: {sgs.size}, more than the {m} slots"

/-- The step side's `finalize_other_proof` input from a wrap entry and the checked step proof
it wrapped, at the step proof's `k` rounds: the unfinalized proof off the wrap statement
(`wrapStatementOf`), the evaluations off the step proof, the mask and `domain_log2` off the
branch data, and the step proof's accumulators' challenges in the LAST slots
(`unpackBranchData`), a zero vector in an absent one, which its mask bit leaves unread. -/
def stepFopInput (w : Cache.Entry CW) {k nc : ℕ} (cpS : Kimchi.Verifier.KimchiProof CS nc k) :
    Except String (StepFop k nc) := do
  let st ← wrapStatementOf toStep k w.publicInput
  let dv := st.proofState.deferredValues
  let u : Pickles.UnfinalizedProof k Fp Bool (Type1 Fp) :=
    { deferredValues := dv.toDeferredValues, shouldFinalize := true
      spongeDigestBeforeEvaluations := st.proofState.spongeDigestBeforeEvaluations }
  let accs := cpS.olds.toList.map (·.u)
  let slots := (List.replicate (Pickles.MaxProofsVerified - accs.length) (Vector.replicate k 0)
    ++ accs).take Pickles.MaxProofsVerified
  let prev : Vector (Vector Fp k) Pickles.MaxProofsVerified ←
    if h : slots.length = Pickles.MaxProofsVerified then pure ⟨slots.toArray, by simp [h]⟩
    else throw s!"accumulators: {accs.length}, more than {Pickles.MaxProofsVerified}"
  return (u, ← chunkedEvalsOf CS cpS, dv.branchData.proofsVerifiedMask, prev,
    dv.branchData.domainLog2)

/-- One run of a half on its input: `build` and `prove` the harness on it, read
the named bits off the table, and decide whether the table satisfies the assembled system. -/
def runHalf {p : ℕ} [Fact p.Prime] {a av β : Type} [CircuitType (ZMod p) a av]
    (side : Kimchi.Fixture.PS.Side p)
    (harness : av → CircuitM (ZMod p) (KimchiConstraint (ZMod p)) β)
    (bitsOf : β → List (String × BoolVar (ZMod p))) (inp : a) :
    IO (Bool × List (String × ℕ)) := do
  let nv := CircuitType.size (ZMod p) a
  let m := harness (inputVar (F := ZMod p) (a := a))
  let t0 ← IO.monoMsNow
  let built := build m nv
  let nc := built.constraints.length
  let t1 ← IO.monoMsNow
  let st := seed (F := ZMod p) (avar := av) inp
  match prove m st.nv st.env with
  | .error e => throw (IO.userError s!"prove failed: {repr e}")
  | .ok pr =>
    let t2 ← IO.monoMsNow
    let read (b : BoolVar (ZMod p)) : ℕ := ((b : CVar (ZMod p)).val pr.assignments.get).val
    let bits := (bitsOf pr.result).map fun (n, b) => (n, read b)
    -- `indexRoundTrip` on the proved table, phase by phase
    let (rows, gates, pubVars) := gateDataOf (reduceBuilt built) (allocRange 0 nv).toList
    let nrows := rows.length
    let t3 ← IO.monoMsNow
    let env' ← match reduceSolved built pr.assignments with
      | .error e => throw (IO.userError s!"reduction failed: {repr e}") | .ok e => pure e
    let (wit, pubs) := makeWitness env' rows pubVars
    let nwit := wit.length
    let t4 ← IO.monoMsNow
    let raw := assembledRaw rows gates nv wit pubs
    let sat ← match Kimchi.Fixture.PS.build side raw with
      | .error e => throw (IO.userError s!"index build failed: {e}")
      | .ok inst =>
        let t5 ← IO.monoMsNow
        let sat : Bool :=
          haveI : NeZero inst.n := inst.nz
          decide (Kimchi.Index.Satisfies inst.idx inst.wit.pub inst.wit.tab)
        let t6 ← IO.monoMsNow
        IO.println s!"    phases: build {t1 - t0} ms ({nc} constraints, {built.nextVar} vars) · \
          prove {t2 - t1} ms · rows {t3 - t2} ms ({nrows} rows) · witness {t4 - t3} ms \
          ({nwit} rows) · index build {t5 - t4} ms (n = {inst.n}) · decide {t6 - t5} ms"
        pure sat
    return (sat, bits)

/-- The scalar half's five bits. -/
def fopBits {F : Type} (o : Pickles.FopOutput F) : List (String × BoolVar F) :=
  [("finalized", o.finalized), ("xiCorrect", o.xiCorrect), ("bCorrect", o.bCorrect),
   ("cipCorrect", o.cipCorrect), ("plonkOk", o.plonkOk)]

/-- The step half on its records at a known domain. -/
def runStep {k nc : ℕ} (zkRows : ℕ) (dom : Pickles.KnownDomain Fp) (inp : StepFop k nc) :
    IO (Bool × List (String × ℕ)) :=
  runHalf (a := StepFop k nc) Kimchi.Fixture.PS.fpSide (fopStepOnAt zkRows [dom]) fopBits inp

/-- The wrap half on its records at a domain. -/
def runWrap {k : ℕ} (domainLog2 : ℕ) (inp : Pickles.WrapFop k) : IO (Bool × List (String × ℕ)) :=
  runHalf (a := Pickles.WrapFop k) Kimchi.Fixture.PS.fqSide (fopWrapOnAt domainLog2) fopBits inp

/-- The step circuit's group half on its records: the wrap key's commitments as constants,
the `x_hat` tables at the Lagrange bases, the SRS's blinding base. -/
def runGroup {ks kw : ℕ} (vk : Kimchi.Verifier.Wire.KimchiVK CW) (basis : Array CW.Point)
    (h : CW.Point) (inp : Pickles.StepGroup ks kw Fp Bool) : IO (Bool × List (String × ℕ)) :=
  runHalf (a := Pickles.StepGroup ks kw Fp Bool) Kimchi.Fixture.PS.fpSide
    (groupStepOn vk (stepXhatTable basis) (xhatStepCell h)) (fun b => [("success", b)]) inp

/-- The wrap circuit's group half on its records: the step key's commitments as constants,
the Lagrange bases, the SRS's blinding base. -/
def runGroupWrap {ks kw n : ℕ} (vk : Kimchi.Verifier.Wire.KimchiVK CS) (basis : Array CS.Point)
    (h : CS.Point) (inp : Pickles.WrapGroup ks kw n Fq Bool) : IO (Bool × List (String × ℕ)) :=
  runHalf (a := Pickles.WrapGroup ks kw n Fq Bool) Kimchi.Fixture.PS.fqSide
    (groupWrapOn vk basis (xhatWrapCell h)) (fun b => [("success", b)]) inp

/-- The wrap circuit's group-half input from a wrap entry, the step entry it wrapped and the
checked step proof at `ks` rounds, at the step statement's `n` slots: the wrap statement,
the step statement carried by value into the wrap field, the step proof (`z₁`, `z₂` as their
Type1 registers `(s − 2^255 − 1)/2`), its `n` accumulators' `sg`. -/
def wrapGroupInput (w : Cache.Entry CW) (s : Cache.Entry CS) (n : ℕ) (pad : CS.Point) {ks : ℕ}
    (cpS : Kimchi.Verifier.KimchiProof CS 1 ks) :
    Except String (Pickles.WrapGroup ks Pickles.WrapIPARounds n Fq Bool) := do
  let statement ← wrapStatementOf id ks w.publicInput
  let st ← stepStatementOf toWrap Pickles.WrapIPARounds n s.publicInput
  let pr ← ivpProofOf CS (fun z => ⟨toWrap (Pasta.Shifted.shiftType1 255 z)⟩) cpS
  return { statement, stepStatement := st, proof := pr, sgOld := ← sgOldOf CS n pad cpS }

/-- The step circuit's group-half input from a wrap entry, a step entry's slot that verified
it and the checked wrap proof at `kw` rounds: the wrap statement carried by value into the
step field, the slot of the step statement, the wrap proof (`z₁`, `z₂` as their Type2
registers `s − 2^255`, split into a half and a parity bit), its two accumulators' `sg`, and
`is_base_case = false`: the slot is a real one. -/
def stepGroupInput (w : Cache.Entry CW) (s : Cache.Entry CS) (slot : ℕ) (pad : CW.Point)
    {kw : ℕ} (cpW : Kimchi.Verifier.KimchiProof CW 1 kw) :
    Except String (Pickles.StepGroup Pickles.StepIPARounds kw Fp Bool) := do
  let statement ← wrapStatementOf toStep Pickles.StepIPARounds w.publicInput
  let n := (s.publicInput.size - 1) / (18 + kw)
  let st ← stepStatementOf id kw n s.publicInput
  let some u := st.proofState.unfinalizedProofs.toList[slot]? | throw s!"slot {slot} of {n}"
  let split (z : CW.ScalarField) : Type2 (SplitField Fp Bool) :=
    let t := (Pasta.Shifted.shiftType2 255 z).val
    ⟨⟨((t / 2 : ℕ) : Fp), decide (t % 2 = 1)⟩⟩
  let pr ← ivpProofOf CW split cpW
  return { statement, claims := u, proof := pr
           sgOld := ← sgOldOf CW Pickles.MaxProofsVerified pad cpW, isBaseCase := false }

/-- The wrap side's `finalize_other_proof` input from a step entry's slot and the checked wrap
proof that slot verified, at the wrap proof's `k` rounds: the slot of the step statement
(`stepStatementOf`) with each split claim as its `Type2` register `2·half + parity`, the
evaluations and the `MaxProofsVerified` accumulators off the wrap proof. -/
def wrapFopInput (s : Cache.Entry CS) (slot : ℕ) {k : ℕ}
    (cpW : Kimchi.Verifier.KimchiProof CW 1 k) : Except String (Pickles.WrapFop k) := do
  let n := (s.publicInput.size - 1) / (18 + k)
  let st ← stepStatementOf toWrap k n s.publicInput
  let some u2 := st.proofState.unfinalizedProofs.toList[slot]? | throw s!"slot {slot} of {n}"
  let t (x : Type2 (SplitField Fq Bool)) : Type2 Fq :=
    ⟨2 * x.val.sDiv2 + (if x.val.sOdd then 1 else 0)⟩
  let dv := u2.deferredValues
  let u : Pickles.UnfinalizedProof k Fq Bool (Type2 Fq) :=
    { deferredValues :=
        { plonk := { alpha := dv.plonk.alpha, beta := dv.plonk.beta, gamma := dv.plonk.gamma,
                     zeta := dv.plonk.zeta, perm := t dv.plonk.perm,
                     zetaToSrsLength := t dv.plonk.zetaToSrsLength,
                     zetaToDomainSize := t dv.plonk.zetaToDomainSize }
          combinedInnerProduct := t dv.combinedInnerProduct, b := t dv.b, xi := dv.xi
          bulletproofChallenges := dv.bulletproofChallenges }
      shouldFinalize := true
      spongeDigestBeforeEvaluations := u2.spongeDigestBeforeEvaluations }
  let accs := cpW.olds.map (·.u)
  let prev : Vector (Vector Fq k) Pickles.MaxProofsVerified ←
    if h : accs.size = Pickles.MaxProofsVerified then pure ⟨accs, h⟩
    else throw s!"wrap accumulators: {accs.size}, expected {Pickles.MaxProofsVerified}"
  return { claims := u, evals := ← allEvalsOf CW cpW, prev }

/-- The curve's SRS cut to `k` rounds, loaded from `srs-cache/<name>.srs` once per `k`
(decompressing the file's points dominates a load). -/
def srsAt (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (k : ℕ) : IO (SRS C.Point) := do
  if let some σ := (← loaded.get).lookup k then return σ
  let srsDir := (← IO.getEnv "SRS_CACHE_DIR").getD "../srs-cache"
  let σ ← Fixture.SRSLoader.loadSRS C sqrt k s!"{srsDir}/{name}.srs"
  loaded.modify ((k, σ) :: ·)
  return σ

/-- The Lagrange basis an entry's key needs — as many as its public input has cells — at its
domain and `nc` chunks, computed from `σ` and memoised per curve, domain and chunk count under
`lagrange-cache/`. -/
def basisFor (C : Ipa.KimchiCurve) (name : String) (σ : SRS C.Point) (nc : ℕ)
    (e : Cache.Entry C) : IO (Array (Vector C.Point nc)) := do
  let memoDir := (← IO.getEnv "LAGRANGE_CACHE_DIR").getD "lagrange-cache"
  Fixture.lagrangeBasisCached C s!"{memoDir}/{name}-2^{e.vk.domainLog2}-{nc}c.json" σ nc
    (2 ^ e.vk.domainLog2) e.vk.omega e.publicInput.size

/-- A cache entry's checked wire records at the SRS `σ`, its key completed with the Lagrange
basis: the records checked at the run's chunk count and `σ`'s round count. -/
def checkedAny (C : Ipa.KimchiCurve) (name : String) (σ : SRS C.Point) (e : Cache.Entry C) :
    IO ((nc : ℕ) × Kimchi.Verifier.KimchiVK C nc × Kimchi.Verifier.KimchiProof C nc σ.k) := do
  let nc := Kimchi.Verifier.Wire.runNc C σ e.vk
  let vk := { e.vk with lagrangeBasis := (← basisFor C name σ nc e).map Vector.toArray }
  match vk.check nc, e.proof.check nc σ.k with
  | some cvk, some cp => return ⟨nc, cvk, cp⟩
  | _, _ => throw (IO.userError "the cache entry's records failed the wire check")

/-- `checkedAny` at one chunk, the chunk count the halves' environment fixes. -/
def checkedAt (C : Ipa.KimchiCurve) (name : String) (σ : SRS C.Point) (e : Cache.Entry C) :
    IO (Kimchi.Verifier.KimchiVK C 1 × Kimchi.Verifier.KimchiProof C 1 σ.k) := do
  let ⟨nc, cvk, cp⟩ ← checkedAny C name σ e
  if h : nc = 1 then return (h ▸ cvk, h ▸ cp)
  else throw (IO.userError s!"the entry runs at {nc} chunks; this lane is one-chunk")

/-- The wire verifier on a cache entry, against the curve's SRS cut to the proof's round
count. -/
def verifies (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (e : Cache.Entry C) : IO Bool := do
  let σ ← srsAt C name sqrt loaded e.proof.opening.lr.size
  let ⟨_, cvk, cp⟩ ← checkedAny C name σ e
  return Kimchi.Verifier.kimchiVerify C σ cvk cp e.publicInput

/-- The environment of an entry's key at its SRS, built once per key. Deciding
`Env.Invariants` computes the key's Lagrange points from the SRS — the one costly invariant —
so the environment is kept and handed back for every later entry under the same key. -/
def envFor (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (envs : IO.Ref (List (String × Pickles.Env C 1)))
    (e : Cache.Entry C) : IO (Pickles.Env C 1) := do
  let key := s!"{e.vkDigest}/{e.proof.opening.lr.size}/{e.publicInput.size}"
  if let some E := (← envs.get).lookup key then return E
  let σ ← srsAt C name sqrt loaded e.proof.opening.lr.size
  let (cvk, _) ← checkedAt C name σ e
  if hE : Pickles.Env.Invariants σ cvk then
    let E : Pickles.Env C 1 := Pickles.Env.ofInvariants σ cvk hE
    envs.modify ((key, E) :: ·)
    return E
  else throw (IO.userError "the key or the SRS breaks an environment invariant: the key's \
    endo is not the curve's, zk_rows < 3 or above the domain, the generator is not primitive \
    on the domain, there is no round, the blinding base is the identity, there is no \
    Lagrange basis or one larger than the domain, or the Lagrange basis is not the SRS's")

/-- The carry of `pred`'s deferred obligation into `succ`'s old accumulator `slot`, both on
`C`: `Carry` decided on the two checked proofs, `AccOk` on the accumulator, `sgOk` on `pred`,
and the last two agreeing, as `sgOk_iff_accOk` says they must under `Carry`. -/
def carriesInto (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (envs : IO.Ref (List (String × Pickles.Env C 1)))
    (pred succ : Cache.Entry C) (slot : ℕ) : IO Bool := do
  let E ← envFor C name sqrt loaded envs pred
  unless succ.proof.opening.lr.size = E.σ.k do
    throw (IO.userError s!"round counts differ: {E.σ.k} and {succ.proof.opening.lr.size}")
  let (_, cp) ← checkedAt C name E.σ pred
  let (_, cp') ← checkedAt C name E.σ succ
  if h : slot < cp'.olds.size then
    -- `carry` and `sgOk` share the predecessor's transcript (`carrySgOk_eq`); `accOk` is
    -- the successor's own accumulator and stays a computation of its own, since its
    -- agreeing with `sgOk` is what the carry says
    let (c, s) := Pickles.carrySgOk E.σ E.cvk cp pred.publicInput cp' ⟨slot, h⟩
    let a := Pickles.accOk E.σ cp'.olds[slot]
    IO.println s!"    carry={c} accOk={a} sgOk(pred)={s}"
    return c && a && s && (s == a)
  else throw (IO.userError s!"slot {slot} beyond the {cp'.olds.size} accumulators")

/-- `Leaf.offBand` at a scalar order, decided: a full leaf's value avoids the sixteen values
around `2·(scalar − 2^254)` at which the ladder degenerates. -/
def offBandB {p : ℕ} [Fact p.Prime] (scalar : ℕ) (V : Valuation (ZMod p)) :
    Pickles.Leaf (ZMod p) 1 → Bool
  | .full s _ _ =>
    let v := (s.val V).val
    let δ := scalar - 2 ^ 254
    decide (v < 2 * δ - 4 ∨ 2 * δ + 11 < v)
  | _ => true

/-- The hypotheses of `Pickles.stepProof_kimchiVerify_vesta` that are facts about data,
decided on a wrap entry and the step entry it wrapped — so the theorem's assumptions are
shown to hold together on a proof the real prover made, and its conclusion is checked at the
public input it names:

* the environment's invariants hold of the step key and its SRS (`Env.Invariants`);
* the file's step domains form a `KnownDomains` with this key's among them, and the wrap
  statement's `domain_log2` is the key's (`hdom`);
* the packed step statement, carried into the wrap field, reads back as the step proof's
  public input (`wrapPublicInput`), and its full scalars are off the band (what the group
  circuit's own assertion needs to be satisfiable);
* the SRS avoids the key's Lagrange relations (`havoid`), decided on the key's Lagrange
  points (`Env.decidableAvoids`), which the environment's invariants tie to the SRS;
* the wrap statement's `messages_for_next_wrap_proof` is the digest `wrapVerifyAt` asserts:
  the padding, the slots' expanded round challenges, the step opening's `sg`;
* `Guards`, `SgOk`, and the conclusion `kimchiVerify`, at that public input.

Booleanity is no hypothesis of the theorem any more — the statement's boolean cells are
constrained by the `x_hat` gadget, the mask by the branch data's input check — and both sets
of rows are among the ones decided here. -/
def theoremHyps (w : Cache.Entry CW) (s : Cache.Entry CS) (steps : Array (Cache.Entry CS))
    (loaded : IO.Ref (List (ℕ × SRS CS.Point)))
    (envs : IO.Ref (List (String × Pickles.Env CS 1))) : IO Bool := do
  let E ← envFor CS "vesta" vestaBase.sqrt? loaded envs s
  let σ := E.σ
  let cvk := E.cvk
  let (_, cp) ← checkedAt CS "vesta" σ s
  do
    let cands := (steps.toList.map fun t =>
      (⟨t.vk.domainLog2, t.vk.omega⟩ : Pickles.KnownDomain Fp)).eraseDups
    let some doms := Pickles.KnownDomains.ofList? E cands s.vk.domainLog2
      | IO.println s!"    ✗ the file's step domains {cands.map (·.log2)} are no KnownDomains \
          at this key (2^{s.vk.domainLog2})"
        return false
    let n := (s.publicInput.size - 1) / (18 + Pickles.WrapIPARounds)
    let wst ← match wrapStatementOf id σ.k w.publicInput with
      | .error e => throw (IO.userError s!"wrap statement: {e}") | .ok r => pure r
    let st ← match stepStatementOf toWrap Pickles.WrapIPARounds n s.publicInput with
      | .error e => throw (IO.userError s!"step statement: {e}") | .ok r => pure r
    let dv := wst.proofState.deferredValues
    let hdom := decide (dv.branchData.domainLog2 = (doms.keyLog2 : Fq))
    -- the statement as constant cells: every reading below is the value's own
    let stVar : Pickles.StepStatement Pickles.WrapIPARounds n (FVar Fq) (BoolVar Fq)
        (Type2 (SplitField (FVar Fq) (BoolVar Fq))) := CircuitType.constVar (F := Fq) st
    let V : Valuation Fq := fun _ => 0
    let pub := Pickles.wrapPublicInput E V stVar
    let pubOk := decide (pub = s.publicInput)
    let offOk := (Pickles.wrapLeavesAt E stVar).all (offBandB CS.scalar V)
    -- the message digest `wrapVerifyAt` asserts
    let params := IpaVesta.curve.sponge.params
    let expanded := st.proofState.unfinalizedProofs.toList.map fun u =>
      u.deferredValues.bulletproofChallenges.toList.map fun c =>
        Poseidon.FqSponge.endoExpand (F := Fq) (IpaPallas.curve.lam : Fq) c.val.val
    let sg := cp.opening.sg
    let digest := (Poseidon.squeeze params (Poseidon.absorb params (wrapMsgSpongeState n)
      (expanded.flatten ++ [sg.x, sg.y]))).1
    let msgOk := decide (digest = wst.proofState.messagesForNextWrapProof)
    let guards := decide (¬ (cvk.lagrangeBasis.size < pub.size ∨ cvk.n < pub.size ∨
      cp.olds.size ≠ cvk.prevChallenges))
    let sg' := Pickles.sgOk E.σ E.cvk cp pub
    let kv := Kimchi.Verifier.kimchiVerify CS σ cvk cp pub
    -- `havoid`, the theorem's own hypothesis, decided on the key's Lagrange points
    let avoidOk := @decide (E.σ.Avoids E.lagrangeRelations)
      (E.decidableAvoids Pickles.pastaShapeVesta)
    IO.println s!"    env=true rounds={σ.k} domains={cands.map (·.log2)} \
      key=2^{doms.keyLog2} hdom={hdom} \
      pub={pubOk} ({pub.size} cells) offBand={offOk} avoids={avoidOk} msgDigest={msgOk} \
      guards={guards} \
      sgOk={sg'} kimchiVerify={kv}"
    -- `hsatS`: the theorem's scalar circuit, as `compile` builds it — the input's check (the
    -- branch data's; the rest of the input is unchecked) and then `scalarCircuit`, which
    -- asserts `finalized`
    let (u, _, mask, prev, d) ← match stepFopInput w cp with
      | .error e => throw (IO.userError s!"step input: {e}") | .ok r => pure r
    let ev ← match allEvalsOf CS cp with
      | .error e => throw (IO.userError s!"step evaluations: {e}") | .ok r => pure r
    let sinp : Pickles.StepProof.ScalarIn σ.k :=
      { branch := ⟨d, mask⟩, fop := ⟨{ claims := u, evals := ev, prev }⟩ }
    let (satS, _) ← runHalf (a := Pickles.StepProof.ScalarIn σ.k) Kimchi.Fixture.PS.fpSide
      (fun (v : Pickles.StepProof.ScalarVar σ.k) => do
        CheckedType.check (c := KimchiConstraint Fp) (val := Pickles.StepProof.ScalarIn σ.k) v
        Pickles.StepProof.scalarCircuit E doms v)
      (fun _ => []) sinp
    IO.println s!"    scalarCircuit (input check, body, finalized asserted): satisfies={satS}"
    -- `hsatG`: the theorem's group circuit — the verify block with its success bit and its
    -- message digest asserted — on the wrap statement, the step statement and proof, and
    -- the slots' expanded round challenges; its key cells are the step key's, as constants,
    -- and its sponge after the index digest is that key's
    let ginp ← match wrapGroupInput w s n (σ.g ⟨0, Nat.two_pow_pos _⟩) cp with
      | .error e => throw (IO.userError s!"wrap group input: {e}") | .ok r => pure r
    let newBp : Vector (Vector Fq Pickles.WrapIPARounds) n :=
      st.proofState.unfinalizedProofs.map fun u =>
        u.deferredValues.bulletproofChallenges.map fun c =>
          Poseidon.FqSponge.endoExpand (F := Fq) (IpaPallas.curve.lam : Fq) c.val.val
    let (satG, _) ← runHalf (a := Pickles.StepProof.GroupIn σ.k Pickles.WrapIPARounds n)
      Kimchi.Fixture.PS.fqSide
      (fun (v : Pickles.StepProof.GroupVar σ.k Pickles.WrapIPARounds n) => do
        let sv ← wrapIndexSponge s.vk
        Pickles.StepProof.groupCircuit E (keyComms xhatWrapCell s.vk) sv
          (SpongeVar.ofConstants (wrapMsgSpongeState n)) v)
      (fun _ => []) ⟨{ group := ginp, newBp }⟩
    IO.println s!"    groupCircuit: satisfies={satG}"
    return hdom && pubOk && offOk && msgOk && guards && sg' && kv && avoidOk && satS && satG

/-- The hypotheses of `Pickles.wrapProof_kimchiVerify_pallas` that are facts about data,
decided on a step entry's slot and the wrap entry that slot verified — the twin of
`theoremHyps`:

* the environment's invariants hold of the wrap key and its SRS (`Env.Invariants`);
* the packed wrap statement, carried into the step field, reads back as the cells of the wrap
  proof's public input that a circuit reads (`stepPublicInput`), the wire's ten further cells
  are zero, and its full scalars are off the band (what the group circuit's own assertion
  needs to be satisfiable);
* the SRS avoids the step relations (`havoid`), decided on the key's Lagrange points
  (`decidableAvoidsStepRelations`);
* `Guards`, `SgOk`, and the conclusion `kimchiVerify`, at that public input;
* both circuits, as `compile` builds them, are satisfied: `WrapProof.scalarCircuit` with
  `finalized` asserted, `WrapProof.groupCircuit` with its success bit asserted at a slot that
  must verify. -/
def wrapTheoremHyps (w : Cache.Entry CW) (s : Cache.Entry CS) (slot : ℕ)
    (loaded : IO.Ref (List (ℕ × SRS CW.Point)))
    (envs : IO.Ref (List (String × Pickles.Env CW 1))) : IO Bool := do
  let E ← envFor CW "pallas" pallasBase.sqrt? loaded envs w
  let σ := E.σ
  let cvk := E.cvk
  let (_, cp) ← checkedAt CW "pallas" σ w
  let wst ← match wrapStatementOf toStep Pickles.StepIPARounds w.publicInput with
    | .error e => throw (IO.userError s!"wrap statement: {e}") | .ok r => pure r
  -- the statement as constant cells: every reading below is the value's own
  let stVar : Pickles.WrapStatement Pickles.StepIPARounds (FVar Fp) (BoolVar Fp)
      (Type1 (FVar Fp)) := CircuitType.constVar (F := Fp) wst
  let V : Valuation Fp := fun _ => 0
  let pub := Pickles.stepPublicInput E V stVar
  -- the wire's input is the cells read, then ten zero cells (`kimchiVerify_append_zeros`)
  let pubOk := decide (pub ++ Array.replicate 10 0 = w.publicInput)
  let offOk := (Pickles.stepLeavesAt E stVar).all (offBandB CW.scalar V)
  let avoidOk := @decide (E.σ.Avoids (Pickles.stepRelationsAt E stVar))
    (Pickles.decidableAvoidsStepRelations E stVar)
  let guards := decide (¬ (cvk.lagrangeBasis.size < pub.size ∨ cvk.n < pub.size ∨
    cp.olds.size ≠ cvk.prevChallenges))
  let sg' := Pickles.sgOk E.σ E.cvk cp pub
  let kv := Kimchi.Verifier.kimchiVerify CW σ cvk cp pub
  IO.println s!"    env=true rounds={σ.k} key=2^{cvk.domainLog2} pub={pubOk} \
    ({pub.size} cells + 10 zeros) offBand={offOk} avoids={avoidOk} guards={guards} \
    sgOk={sg'} kimchiVerify={kv}"
  -- `hsatS`: the theorem's scalar circuit, which asserts `finalized`
  let finp ← match wrapFopInput s slot cp with
    | .error e => throw (IO.userError s!"wrap input: {e}") | .ok r => pure r
  let (satS, _) ← runHalf (a := Pickles.WrapProof.ScalarIn σ.k) Kimchi.Fixture.PS.fqSide
    (fun (v : Pickles.WrapProof.ScalarVar σ.k) => Pickles.WrapProof.scalarCircuit E v)
    (fun _ => []) ⟨finp⟩
  IO.println s!"    scalarCircuit (finalized asserted): satisfies={satS}"
  -- `hsatG`: the theorem's group circuit — `verify` with its success bit asserted — on the
  -- wrap statement, the slot's claims and the wrap proof; its key cells are the wrap key's,
  -- as constants, and its sponge after the index digest is that key's
  let ginp ← match stepGroupInput w s slot (σ.g ⟨0, Nat.two_pow_pos _⟩) cp with
    | .error e => throw (IO.userError s!"step group input: {e}") | .ok r => pure r
  let (satG, _) ← runHalf (a := Pickles.WrapProof.GroupIn Pickles.StepIPARounds σ.k)
    Kimchi.Fixture.PS.fpSide
    (fun (v : Pickles.WrapProof.GroupVar Pickles.StepIPARounds σ.k) => do
      let sv ← stepIndexSponge w.vk
      Pickles.WrapProof.groupCircuit E (keyComms xhatStepCell w.vk) sv v)
    (fun _ => []) ⟨ginp⟩
  IO.println s!"    groupCircuit: satisfies={satG}"
  return pubOk && offOk && avoidOk && guards && sg' && kv && satS && satG

/-- An unlinked old accumulator — a front pad or a base-case slot — satisfies `AccOk` on its
own. -/
def padOk (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (e : Cache.Entry C) (slot : ℕ) : IO Bool := do
  let σ ← srsAt C name sqrt loaded e.proof.opening.lr.size
  let (_, cp) ← checkedAt C name σ e
  if h : slot < cp.olds.size then return Pickles.accOk σ cp.olds[slot]
  else throw (IO.userError s!"slot {slot} beyond the {cp.olds.size} accumulators")

def main : IO Unit := do
  let path := (← IO.getEnv "PROOF_CACHE").getD
    "../packages/pickles/test/fixtures/proof-cache/SimpleChain.json"
  let raw ← IO.FS.readFile path
  let (wraps, _) ← match Cache.parseFile CW Kimchi.Fixture.PS.fqSide.endo pallasBase.sqrt? raw with
    | .error e => throw (IO.userError s!"wrap side: {e}") | .ok r => pure r
  let (steps, _) ← match Cache.parseFile CS Kimchi.Fixture.PS.fpSide.endo vestaBase.sqrt? raw with
    | .error e => throw (IO.userError s!"step side: {e}") | .ok r => pure r
  IO.println s!"{path}: {wraps.size} wrap proofs, {steps.size} step proofs"
  let lanes := (← IO.getEnv "HALVES").getD
    "step,wrap,step-group,wrap-group,verify,carry,theorem"
  let halves := lanes.splitOn ","
  let on (h : String) : Bool := halves.contains h
  let limit := ((← IO.getEnv "LIMIT").bind String.toNat?).getD wraps.size
  let vestaSRS ← IO.mkRef ([] : List (ℕ × SRS CS.Point))
  let pallasSRS ← IO.mkRef ([] : List (ℕ × SRS CW.Point))
  let vestaEnvs ← IO.mkRef ([] : List (String × Pickles.Env CS 1))
  let pallasEnvs ← IO.mkRef ([] : List (String × Pickles.Env CW 1))
  let mut allOk := true
  let mut runs := 0
  -- One timed run of a half, its verdict folded into `allOk`.
  let report (what : String) (run : IO (Bool × List (String × ℕ))) : IO Bool := do
    let t0 ← IO.monoMsNow
    let (sat, bits) ← run
    let t1 ← IO.monoMsNow
    let ok := sat ∧ bits.all (·.2 = 1)
    IO.println s!"  {if ok then "✓" else "✗"} {what}: satisfies={sat} \
      bits={bits.map fun (n, v) => s!"{n}={v}"} {t1 - t0} ms"
    return ok
  -- One timed verdict.
  let reportBool (what : String) (run : IO Bool) : IO Bool := do
    let t0 ← IO.monoMsNow
    let ok ← run
    let t1 ← IO.monoMsNow
    IO.println s!"  {if ok then "✓" else "✗"} {what} {t1 - t0} ms"
    return ok
  for w in wraps.toList.take limit do
    let some (d, pi) := w.step | continue
    let some s := steps.find? (fun s => s.vkDigest = d ∧ s.publicInputKey = pi)
      | IO.println s!"  ✗ wrap {w.vkDigest.take 10}…: its step {d.take 10}… is not in the file"
        allOk := false
        continue
    let pair := s!"wrap→step {d.take 10}…"
    if on "step" then
      let σS ← srsAt CS "vesta" vestaBase.sqrt? vestaSRS s.proof.opening.lr.size
      let ⟨nc, cvkS, cpS⟩ ← checkedAny CS "vesta" σS s
      let inp ← match stepFopInput w cpS with
        | .error e => throw (IO.userError s!"step input: {e}") | .ok r => pure r
      let ok ← report s!"step half on {pair} (domain 2^{s.vk.domainLog2}, {nc} chunk(s), \
          zk_rows {cvkS.zkRows})"
        (runStep cvkS.zkRows ⟨s.vk.domainLog2, s.vk.omega⟩ inp)
      runs := runs + 1
      unless ok do allOk := false
    if on "verify" then
      let t0 ← IO.monoMsNow
      let stepOk ← verifies CS "vesta" vestaBase.sqrt? vestaSRS s
      let wrapOk ← verifies CW "pallas" pallasBase.sqrt? pallasSRS w
      let t1 ← IO.monoMsNow
      IO.println s!"  {if stepOk ∧ wrapOk then "✓" else "✗"} kimchiVerify on {pair}: \
        step={stepOk} wrap={wrapOk} {t1 - t0} ms"
      runs := runs + 1
      unless stepOk ∧ wrapOk do allOk := false
    if on "theorem" then
      let ok ← reportBool s!"theorem hypotheses on {pair}"
        (theoremHyps w s steps vestaSRS vestaEnvs)
      runs := runs + 1
      unless ok do allOk := false
    if on "wrap-group" then
      let n := (s.publicInput.size - 1) / (18 + Pickles.WrapIPARounds)
      let r := s.proof.opening.lr.size
      let σS ← srsAt CS "vesta" vestaBase.sqrt? vestaSRS r
      let (_, cpS) ← checkedAt CS "vesta" σS s
      let ginp ← match wrapGroupInput w s n (σS.g ⟨0, Nat.two_pow_pos _⟩) cpS with
        | .error e => throw (IO.userError s!"wrap group input: {e}") | .ok i => pure i
      let basis := (← basisFor CS "vesta" σS 1 s).map (·[(0 : Fin 1)])
      let ok ← report s!"wrap group half on {pair} ({n} slot(s), {r} rounds)"
        (runGroupWrap s.vk basis σS.h ginp)
      runs := runs + 1
      unless ok do allOk := false
  for s in steps.toList.take limit do
    for (ref, slot) in s.prevs.toList.zipIdx do
      let some (d, pi) := ref | continue
      let some w := wraps.find? (fun w => w.vkDigest = d ∧ w.publicInputKey = pi)
        | IO.println s!"  ✗ step {s.vkDigest.take 10}… slot {slot}: its wrap {d.take 10}… \
            is not in the file"
          allOk := false
          continue
      let pair := s!"step→wrap {d.take 10}… (slot {slot})"
      let r := w.proof.opening.lr.size
      if on "wrap" then
        let σW ← srsAt CW "pallas" pallasBase.sqrt? pallasSRS r
        let (_, cpW) ← checkedAt CW "pallas" σW w
        let inp ← match wrapFopInput s slot cpW with
          | .error e => throw (IO.userError s!"wrap input: {e}") | .ok i => pure i
        let ok ← report s!"wrap half on {pair} (domain 2^{w.vk.domainLog2}, {r} rounds)"
          (runWrap w.vk.domainLog2 inp)
        runs := runs + 1
        unless ok do allOk := false
      if on "step-group" then
        let σW ← srsAt CW "pallas" pallasBase.sqrt? pallasSRS r
        let (_, cpW) ← checkedAt CW "pallas" σW w
        let ginp ← match stepGroupInput w s slot (σW.g ⟨0, Nat.two_pow_pos _⟩) cpW with
          | .error e => throw (IO.userError s!"step group input: {e}") | .ok i => pure i
        let basis := (← basisFor CW "pallas" σW 1 w).map (·[(0 : Fin 1)])
        let ok ← report s!"step group half on {pair}" (runGroup w.vk basis σW.h ginp)
        runs := runs + 1
        unless ok do allOk := false
      if on "theorem" then
        let ok ← reportBool s!"theorem hypotheses on {pair}"
          (wrapTheoremHyps w s slot pallasSRS pallasEnvs)
        runs := runs + 1
        unless ok do allOk := false
  if on "carry" then
    -- Wrap k−1 → wrap k through the step between them: the step's slot `j` is the wrap's
    -- accumulator `pad + j`; the pads in front and the base-case slots are unlinked.
    for w in wraps.toList.take limit do
      let some (d, pi) := w.step | continue
      let some s := steps.find? (fun s => s.vkDigest = d ∧ s.publicInputKey = pi) | continue
      let tag := s!"wrap {w.vkDigest.take 10}…/{w.publicInputKey.take 10}…"
      let pad := w.proof.prevChallenges.size - s.prevs.size
      for j in List.range pad do
        let ok ← reportBool s!"pad accumulator {j} of {tag}: AccOk"
          (padOk CW "pallas" pallasBase.sqrt? pallasSRS w j)
        runs := runs + 1
        unless ok do allOk := false
      for (ref, j) in s.prevs.toList.zipIdx do
        match ref with
        | none =>
          let ok ← reportBool s!"base-case accumulator {pad + j} of {tag}: AccOk"
            (padOk CW "pallas" pallasBase.sqrt? pallasSRS w (pad + j))
          runs := runs + 1
          unless ok do allOk := false
        | some (d', pi') =>
          let some w' := wraps.find? (fun w => w.vkDigest = d' ∧ w.publicInputKey = pi')
            | IO.println s!"  ✗ {tag}: its predecessor wrap {d'.take 10}… is not in the file"
              allOk := false
              continue
          let ok ← reportBool s!"carry wrap→wrap into accumulator {pad + j} of {tag}"
            (carriesInto CW "pallas" pallasBase.sqrt? pallasSRS pallasEnvs w' w (pad + j))
          runs := runs + 1
          unless ok do allOk := false
    -- Step k−1 → step k through the wrap between them: slot `j` is accumulator `j`.
    for s in steps.toList.take limit do
      let tag := s!"step {s.vkDigest.take 10}…/{s.publicInputKey.take 10}…"
      for (ref, j) in s.prevs.toList.zipIdx do
        match ref with
        | none =>
          let ok ← reportBool s!"base-case accumulator {j} of {tag}: AccOk"
            (padOk CS "vesta" vestaBase.sqrt? vestaSRS s j)
          runs := runs + 1
          unless ok do allOk := false
        | some (d, pi) =>
          let some w' := wraps.find? (fun w => w.vkDigest = d ∧ w.publicInputKey = pi)
            | IO.println s!"  ✗ {tag} slot {j}: its wrap {d.take 10}… is not in the file"
              allOk := false
              continue
          let some (d2, pi2) := w'.step
            | IO.println s!"  ✗ {tag} slot {j}: its wrap wrapped no step"
              allOk := false
              continue
          let some s' := steps.find? (fun s => s.vkDigest = d2 ∧ s.publicInputKey = pi2)
            | IO.println s!"  ✗ {tag} slot {j}: its predecessor step {d2.take 10}… is not in \
                the file"
              allOk := false
              continue
          let ok ← reportBool s!"carry step→step into accumulator {j} of {tag}"
            (carriesInto CS "vesta" vestaBase.sqrt? vestaSRS vestaEnvs s' s j)
          runs := runs + 1
          unless ok do allOk := false
  unless runs > 0 do throw (IO.userError "no linked pairs to run")
  unless allOk do throw (IO.userError "check-halves FAILED")
  IO.println s!"✓ {runs} run(s): every table satisfies its system, every bit reads 1, \
    kimchiVerify accepts every proof, every accumulator is carried"
