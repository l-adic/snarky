import PicklesFixture
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

Run: `PROOF_CACHE=<file> lake exe check-halves` from `formal/`; the default is
`SimpleChain.json`. `SRS_CACHE_DIR` and `LAGRANGE_CACHE_DIR` relocate the two caches.
`HALVES` narrows the run to a comma-separated subset of `step`, `wrap`, `step-group`,
`wrap-group`, `verify` (the default is all five).
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

/-- One chunk of a one-chunk evaluation. -/
def oneChunk {F : Type} (nm : String) (a : Array F) : Except String F :=
  if h : a.size = 1 then pure a[0] else throw s!"{nm}: expected one chunk, got {a.size}"

/-- The evaluation block in the layout's order — the public pair, 15 `w`, 15 coefficient,
`z`, 6 `σ`, 6 selector pairs — each pair `(ζ, ζω)` at one chunk. -/
def evalCells (C : Ipa.KimchiCurve) (p : Kimchi.Verifier.Wire.KimchiProof C) :
    Except String (Vector C.ScalarField 88) := do
  let pair (nm : String) (e : Kimchi.Verifier.PointEvaluations (Array C.ScalarField)) :
      Except String (List C.ScalarField) := do
    pure [← oneChunk nm e.zeta, ← oneChunk nm e.zetaOmega]
  let some pub := p.pubEvals
    | throw "the proof carries no public evaluations (one-chunk wire form)"
  let mut cells : List C.ScalarField := []
  cells := cells ++ (← pair "public" pub)
  for e in p.evals.w.toList do cells := cells ++ (← pair "w" e)
  for e in p.evals.coefficients.toList do cells := cells ++ (← pair "coefficients" e)
  cells := cells ++ (← pair "z" p.evals.z)
  for e in p.evals.s.toList do cells := cells ++ (← pair "s" e)
  cells := cells ++ (← pair "generic" p.evals.genericSelector)
  cells := cells ++ (← pair "poseidon" p.evals.poseidonSelector)
  cells := cells ++ (← pair "completeAdd" p.evals.completeAddSelector)
  cells := cells ++ (← pair "mul" p.evals.mulSelector)
  cells := cells ++ (← pair "emul" p.evals.emulSelector)
  cells := cells ++ (← pair "endomulScalar" p.evals.endomulScalarSelector)
  if h : cells.length = 88 then pure ⟨cells.toArray, by simp [h]⟩
  else throw s!"evaluation block: {cells.length} cells"

/-- `finalize_other_proof`'s input from a wrap entry and the step entry it wrapped.

The wrap statement's cells (`Pickles.WrapStatement.packed`): `cip, b, ζ^{2^k}, ζⁿ, perm` at
0–4, `β, γ` at 5–6, `α, ζ, ξ` at 7–9, the three digests at 10–12 (the step proof's sponge
digest first), the 16 round challenges at 13–28, the packed branch data
`4·domain_log2 + m₀ + 2·m₁` at 29. -/
def assemble (w : Cache.Entry CW) (s : Cache.Entry CS) :
    Except String (FopInput Fp × Pickles.KnownDomain Fp) := do
  let c := w.publicInput
  unless 30 ≤ c.size do throw s!"wrap public input: {c.size} cells"
  let g (i : ℕ) : Fp := toStep (c.getD i 0)
  let claims : Vector Fp 26 := Vector.ofFn fun i =>
    match (i : ℕ) with
    | 0 => g 7 | 1 => g 5 | 2 => g 6 | 3 => g 8
    | 4 => g 2 | 5 => g 3 | 6 => g 4 | 7 => g 0 | 8 => g 1 | 9 => g 9
    | k => g (13 + (k - 10))
  let bd := (c.getD 29 0).val
  -- Two accumulator slots of 16 challenges each, the proof's accumulators in the LAST
  -- slots: the mask reads slot `i` as "at least `2 − i` proofs", so padding goes in front.
  -- An absent accumulator is a zero slot, which its mask bit leaves unread.
  let prev : List (List Fp) := s.proof.prevChallenges.toList.map (·.chals.toList)
  let slots := (List.replicate (2 - prev.length) [] ++ prev).take 2
  let prevCells : List Fp :=
    slots.flatMap fun ch => (ch ++ List.replicate 16 (0 : Fp)).take 16
  let prevChallenges : Vector Fp 32 ←
    if h : prevCells.length = 32 then pure ⟨prevCells.toArray, by simp [h]⟩
    else throw s!"previous challenges: {prevCells.length} cells"
  return ({ claims
            mask := #v[(bd % 2 : ℕ), ((bd / 2) % 2 : ℕ)]
            domainLog2 := (bd / 4 : ℕ)
            evals := ← evalCells CS s.proof
            ftEval1 := s.proof.ftEval1
            prevChallenges
            digest := g 10 },
          ⟨s.vk.domainLog2, s.vk.omega⟩)

/-- One run of a half on a named input bundle: `build` and `prove` the harness on it, read
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
    -- `provedSatisfies`, phase by phase
    let (rows, gates, pubVars) := gateDataOf built nv
    let nrows := rows.length
    let t3 ← IO.monoMsNow
    let env' ← match reduceProved built pr.assignments with
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

/-- The step half on a step-side bundle at a known domain. -/
def runStep (dom : Pickles.KnownDomain Fp) (inp : FopInput Fp) : IO (Bool × List (String × ℕ)) :=
  runHalf (a := FopInput Fp) Kimchi.Fixture.PS.fpSide (fopStepOnAt [dom]) fopBits inp

/-- The wrap half on a wrap-side bundle at a domain and a round count. -/
def runWrap (domainLog2 r : ℕ) (inp : FopWrapInput r Fq) : IO (Bool × List (String × ℕ)) :=
  runHalf (a := FopWrapInput r Fq) Kimchi.Fixture.PS.fqSide (fopWrapOnAt domainLog2 r) fopBits inp

/-- The step circuit's group half on a wrap proof: the wrap key's commitments as constants,
the `x_hat` tables at the Lagrange bases, the SRS's blinding base. -/
def runGroup (vk : Kimchi.Verifier.Wire.KimchiVK CW) (basis : Array CW.Point) (h : CW.Point)
    (inp : GroupStepInput Fp) : IO (Bool × List (String × ℕ)) :=
  runHalf (a := GroupStepInput Fp) Kimchi.Fixture.PS.fpSide
    (groupStepOn vk (stepXhatTable basis) (xhatStepCell h)) (fun b => [("success", b)]) inp

/-- The wrap circuit's group half on a step proof: the step key's commitments as constants,
the Lagrange bases, the SRS's blinding base. -/
def runGroupWrap (n r : ℕ) (vk : Kimchi.Verifier.Wire.KimchiVK CS) (basis : Array CS.Point)
    (h : CS.Point) (inp : GroupWrapInput n r Fq) : IO (Bool × List (String × ℕ)) :=
  runHalf (a := GroupWrapInput n r Fq) Kimchi.Fixture.PS.fqSide
    (groupWrapOn vk basis (xhatWrapCell h)) (fun b => [("success", b)]) inp

/-- The wrap circuit's group-half input from a wrap entry and the step proof it wrapped, at
the step statement's `n` slots and the step proof's `r` rounds: the wrap statement's 29
packed scalars as they are, the step statement carried by value into the wrap field, the
step proof's commitments and opening (`z₁`, `z₂` as their Type1 registers `(s − 2^255 − 1)/2`),
its `n` accumulators' commitments as `sg_old`, and their keep bits off the wrap statement's
branch data — `mask_i` packed at bit `1 − i` of the slot order, the accumulators listed in
reverse slot order. -/
def assembleGroupWrap (n r : ℕ) (w : Cache.Entry CW) (s : Cache.Entry CS) :
    Except String (GroupWrapInput n r Fq) := do
  let c := w.publicInput
  unless 30 ≤ c.size do throw s!"wrap public input: {c.size} cells"
  let statement : Vector Fq 29 := Vector.ofFn fun i => c.getD i 0
  let sc := s.publicInput
  unless sc.size = 33 * n + 1 do
    throw s!"step public input: {sc.size} cells, expected {33 * n + 1} at {n} slots"
  let stepStatement : Vector Fq (33 * n + 1) := Vector.ofFn fun i => toWrap (sc.getD i 0)
  let coords (P : CS.Point) : List Fq := [P.x, P.y]
  let chunk (nm : String) (a : Array CS.Point) : Except String CS.Point :=
    if h : a.size = 1 then pure a[0] else throw s!"{nm}: expected one chunk, got {a.size}"
  let type1 (z : CS.ScalarField) : Fq := toWrap (Pasta.Shifted.shiftType1 255 z)
  unless s.proof.opening.lr.size = r do
    throw s!"step opening: {s.proof.opening.lr.size} rounds, expected {r}"
  let mut cells : List Fq := []
  for cm in s.proof.wComm.toList do cells := cells ++ coords (← chunk "w_comm" cm)
  cells := cells ++ coords (← chunk "z_comm" s.proof.zComm)
  for P in s.proof.tComm.toList do cells := cells ++ coords P
  for lr in s.proof.opening.lr.toList do cells := cells ++ coords lr.1 ++ coords lr.2
  cells := cells ++ [type1 s.proof.opening.z1, type1 s.proof.opening.z2]
    ++ coords s.proof.opening.delta ++ coords s.proof.opening.sg
  let proof : Vector Fq (52 + 4 * r) ←
    if h : cells.length = 52 + 4 * r then pure ⟨cells.toArray, by simp [h]⟩
    else throw s!"step proof block: {cells.length} cells"
  let accs := s.proof.prevChallenges.toList
  unless accs.length = n ∧ n ≤ 2 do
    throw s!"step accumulators: {accs.length}, expected {n} (at most two)"
  let mut sgs : List Fq := []
  for rc in accs do sgs := sgs ++ coords (← chunk "sg_old" rc.comm)
  let sgOld : Vector Fq (2 * n) ←
    if h : sgs.length = 2 * n then pure ⟨sgs.toArray, by simp [h]⟩
    else throw s!"sg_old: {sgs.length} cells"
  let bd := (c.getD 29 0).val
  let mask : Vector Fq n := Vector.ofFn fun i => (((bd / 2 ^ (i + 2 - n)) % 2 : ℕ) : Fq)
  return { statement, stepStatement, proof, sgOld, mask }

/-- The step circuit's group-half input from a step entry's slot and the wrap proof that
slot verified: the wrap statement's cells (the wrap proof's public input carried by value
into the step field, the branch data unpacked into `domain_log2` and the two mask bits),
the slot of the step statement as it is, the wrap proof's commitments and opening (`z₁`,
`z₂` as their Type2 registers `s − 2^255`, split into a half and a parity bit), its two
accumulators' commitments as `sg_old`, and `is_base_case = 0`: the slot is a real one. -/
def assembleGroup (s : Cache.Entry CS) (slot : ℕ) (w : Cache.Entry CW) :
    Except String (GroupStepInput Fp) := do
  let c := w.publicInput
  unless 30 ≤ c.size do throw s!"wrap public input: {c.size} cells"
  let bd := (c.getD 29 0).val
  let statement : Vector Fp 32 := Vector.ofFn fun i =>
    match (i : ℕ) with
    | 29 => ((bd / 4 : ℕ) : Fp) | 30 => ((bd % 2 : ℕ) : Fp) | 31 => (((bd / 2) % 2 : ℕ) : Fp)
    | k => toStep (c.getD k 0)
  let sc := s.publicInput
  let base := slot * 32
  unless base + 32 ≤ sc.size do
    throw s!"step public input: {sc.size} cells, slot {slot} needs {base + 32}"
  let unfinalized : Vector Fp 32 := Vector.ofFn fun i => sc.getD (base + i) 0
  let coords (P : CW.Point) : List Fp := [P.x, P.y]
  let chunk (nm : String) (a : Array CW.Point) : Except String CW.Point :=
    if h : a.size = 1 then pure a[0] else throw s!"{nm}: expected one chunk, got {a.size}"
  let split (z : CW.ScalarField) : List Fp :=
    let t := (Pasta.Shifted.shiftType2 255 z).val
    [((t / 2 : ℕ) : Fp), ((t % 2 : ℕ) : Fp)]
  let mut cells : List Fp := []
  for cm in w.proof.wComm.toList do cells := cells ++ coords (← chunk "w_comm" cm)
  cells := cells ++ coords (← chunk "z_comm" w.proof.zComm)
  for P in w.proof.tComm.toList do cells := cells ++ coords P
  for lr in w.proof.opening.lr.toList do cells := cells ++ coords lr.1 ++ coords lr.2
  cells := cells ++ split w.proof.opening.z1 ++ split w.proof.opening.z2
    ++ coords w.proof.opening.delta ++ coords w.proof.opening.sg
  let proof : Vector Fp 114 ←
    if h : cells.length = 114 then pure ⟨cells.toArray, by simp [h]⟩
    else throw s!"wrap proof block: {cells.length} cells"
  let mut sgs : List Fp := []
  for rc in w.proof.prevChallenges.toList do sgs := sgs ++ coords (← chunk "sg_old" rc.comm)
  let sgOld : Vector Fp 4 ←
    if h : sgs.length = 4 then pure ⟨sgs.toArray, by simp [h]⟩
    else throw s!"sg_old: {sgs.length} cells, expected two accumulators"
  return { statement, unfinalized, proof, sgOld, isBaseCase := 0 }

/-- `finalize_other_proof`'s wrap-side input from a step entry's slot and the wrap proof that
slot verified.

The step statement (`Pickles.PackedStatement`) lays a slot out in `17 + r` cells: the five
shifted claims `cip, b, ζ^{2^k}, ζⁿ, perm` as `(half, parity)` pairs at 0–9, the digest at
10, `β, γ` at 11–12, `α, ζ, ξ` at 13–15, the `r` round challenges from 16, `should_finalize`
last. A split claim's wrap-field cell is its `Type2` register `2·half + parity`. The
evaluations and the two accumulators are the wrap proof's; the wrap side reads both
accumulators, so the proof must carry exactly two of `r` challenges. -/
def assembleWrap (r : ℕ) (s : Cache.Entry CS) (slot : ℕ) (w : Cache.Entry CW) :
    Except String (FopWrapInput r Fq) := do
  let c := s.publicInput
  let base := slot * (17 + r)
  unless base + 17 + r ≤ c.size do
    throw s!"step public input: {c.size} cells, slot {slot} needs {base + 17 + r}"
  let g (i : ℕ) : Fq := toWrap (c.getD (base + i) 0)
  let t (i : ℕ) : Fq := 2 * g (2 * i) + g (2 * i + 1)
  let claims : Vector Fq (10 + r) := Vector.ofFn fun i =>
    match (i : ℕ) with
    | 0 => g 13 | 1 => g 11 | 2 => g 12 | 3 => g 14
    | 4 => t 2 | 5 => t 3 | 6 => t 4 | 7 => t 0 | 8 => t 1 | 9 => g 15
    | k => g (16 + (k - 10))
  let prev : List (List Fq) := w.proof.prevChallenges.toList.map (·.chals.toList)
  unless prev.length = 2 ∧ prev.all (·.length = r) do
    throw s!"wrap accumulators: {prev.map (·.length)}, expected two of {r}"
  let prevCells := prev.flatten
  let prevChallenges : Vector Fq (2 * r) ←
    if h : prevCells.length = 2 * r then pure ⟨prevCells.toArray, by simp [h]⟩
    else throw s!"previous challenges: {prevCells.length} cells"
  return { claims, evals := ← evalCells CW w.proof, ftEval1 := w.proof.ftEval1, prevChallenges
           digest := g 10 }

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
domain, computed from `σ` and memoised per curve and domain under `lagrange-cache/`. -/
def basisFor (C : Ipa.KimchiCurve) (name : String) (σ : SRS C.Point) (e : Cache.Entry C) :
    IO (Array C.Point) := do
  let memoDir := (← IO.getEnv "LAGRANGE_CACHE_DIR").getD "lagrange-cache"
  let n := 2 ^ e.vk.domainLog2
  if h : n ≤ 2 ^ σ.k then
    Fixture.lagrangeBasisCached C s!"{memoDir}/{name}-2^{e.vk.domainLog2}.json" σ n h
      e.vk.omega e.publicInput.size
  else throw (IO.userError s!"domain 2^{e.vk.domainLog2} above the SRS at 2^{σ.k}")

/-- The wire verifier on a cache entry, its key completed with the Lagrange basis: the
records checked at the run's chunk count and the SRS's round count, then `kimchiVerify`.
The entry's SRS is the curve's file cut to the proof's round count. -/
def verifies (C : Ipa.KimchiCurve) (name : String) (sqrt : C.BaseField → Option C.BaseField)
    (loaded : IO.Ref (List (ℕ × SRS C.Point))) (e : Cache.Entry C) : IO Bool := do
  let σ ← srsAt C name sqrt loaded e.proof.opening.lr.size
  let basis ← basisFor C name σ e
  let vk := { e.vk with lagrangeBasis := basis.map (#[·]) }
  let nc := Kimchi.Verifier.Wire.runNc C σ vk
  match vk.check nc, e.proof.check nc σ.k with
  | some cvk, some cp => return Kimchi.Verifier.kimchiVerify C σ cvk cp e.publicInput
  | _, _ => throw (IO.userError "the cache entry's records failed the wire check")

def main : IO Unit := do
  let path := (← IO.getEnv "PROOF_CACHE").getD
    "../packages/pickles/test/fixtures/proof-cache/SimpleChain.json"
  let raw ← IO.FS.readFile path
  let (wraps, _) ← match Cache.parseFile CW Kimchi.Fixture.PS.fqSide.endo pallasBase.sqrt? raw with
    | .error e => throw (IO.userError s!"wrap side: {e}") | .ok r => pure r
  let (steps, _) ← match Cache.parseFile CS Kimchi.Fixture.PS.fpSide.endo vestaBase.sqrt? raw with
    | .error e => throw (IO.userError s!"step side: {e}") | .ok r => pure r
  IO.println s!"{path}: {wraps.size} wrap proofs, {steps.size} step proofs"
  let halves := ((← IO.getEnv "HALVES").getD "step,wrap,step-group,wrap-group,verify").splitOn ","
  let on (h : String) : Bool := halves.contains h
  let limit := ((← IO.getEnv "LIMIT").bind String.toNat?).getD wraps.size
  let vestaSRS ← IO.mkRef ([] : List (ℕ × SRS CS.Point))
  let pallasSRS ← IO.mkRef ([] : List (ℕ × SRS CW.Point))
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
  for w in wraps.toList.take limit do
    let some (d, pi) := w.step | continue
    let some s := steps.find? (fun s => s.vkDigest = d ∧ s.publicInputKey = pi)
      | IO.println s!"  ✗ wrap {w.vkDigest.take 10}…: its step {d.take 10}… is not in the file"
        allOk := false
        continue
    let pair := s!"wrap→step {d.take 10}…"
    if on "step" then
      let (inp, dom) ← match assemble w s with
        | .error e => throw (IO.userError s!"assemble: {e}") | .ok r => pure r
      let ok ← report s!"step half on {pair} (domain 2^{s.vk.domainLog2})" (runStep dom inp)
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
    if on "wrap-group" then
      let n := (s.publicInput.size - 1) / 33
      let r := s.proof.opening.lr.size
      let ginp ← match assembleGroupWrap n r w s with
        | .error e => throw (IO.userError s!"assemble (wrap group half): {e}") | .ok i => pure i
      let σS ← srsAt CS "vesta" vestaBase.sqrt? vestaSRS r
      let basis ← basisFor CS "vesta" σS s
      let ok ← report s!"wrap group half on {pair} ({n} slot(s), {r} rounds)"
        (runGroupWrap n r s.vk basis σS.h ginp)
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
        let inp ← match assembleWrap r s slot w with
          | .error e => throw (IO.userError s!"assemble (wrap side): {e}") | .ok i => pure i
        let ok ← report s!"wrap half on {pair} (domain 2^{w.vk.domainLog2}, {r} rounds)"
          (runWrap w.vk.domainLog2 r inp)
        runs := runs + 1
        unless ok do allOk := false
      if on "step-group" then
        let ginp ← match assembleGroup s slot w with
          | .error e => throw (IO.userError s!"assemble (group half): {e}") | .ok i => pure i
        let σW ← srsAt CW "pallas" pallasBase.sqrt? pallasSRS r
        let basis ← basisFor CW "pallas" σW w
        let ok ← report s!"step group half on {pair}" (runGroup w.vk basis σW.h ginp)
        runs := runs + 1
        unless ok do allOk := false
  unless runs > 0 do throw (IO.userError "no linked pairs to run")
  unless allOk do throw (IO.userError "check-halves FAILED")
  IO.println s!"✓ {runs} run(s): every table satisfies its system, every bit reads 1, \
    kimchiVerify accepts every proof"
