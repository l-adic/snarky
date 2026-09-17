import PicklesFixture
import KimchiFixture.Cache
import CompElliptic.Fields.Pasta

/-!
# The circuit halves, satisfied on proofs the PureScript suite produced

The two-halves capstones relate a circuit's success bits to `kimchiVerify` for any table
that satisfies the circuit. They say nothing about whether a real proof produces such a
table. This driver runs the modelled half through the Lean prover interpreter on the
inputs of a real proof — the advice code, which nothing else in the tree exercises — and
decides whether the table it produced satisfies every constraint, with the success bits
read back off it.

The scalar half of the step circuit finalizes the *step* proof its verified wrap proof
wrapped: that proof's scalar-side checks live in the step field. So one run takes a wrap
entry of the cache, follows its `step` link to the step proof, and lays out
`finalize_other_proof`'s input from the two: the deferred-value claims, the digest and
the branch data from the wrap statement (the wrap entry's public input), the evaluations
and old accumulators from the step proof.

Per run: the interpreter completes (a), the table satisfies the assembled system (b),
`finalized` and its four conjuncts read 1 (c). `kimchiVerify` on the same entries is a
separate driver.

Run: `PROOF_CACHE=<file> lake exe check-halves` from `formal/`; the default is
`SimpleChain.json`.
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

/-- One chunk of a one-chunk evaluation. -/
def oneChunk (nm : String) (a : Array Fp) : Except String Fp :=
  if h : a.size = 1 then pure a[0] else throw s!"{nm}: expected one chunk, got {a.size}"

/-- The evaluation block in the layout's order — the public pair, 15 `w`, 15 coefficient,
`z`, 6 `σ`, 6 selector pairs — each pair `(ζ, ζω)` at one chunk. -/
def evalCells (p : Kimchi.Verifier.Wire.KimchiProof CS) : Except String (Vector Fp 88) := do
  let pair (nm : String) (e : Kimchi.Verifier.PointEvaluations (Array Fp)) :
      Except String (List Fp) := do
    pure [← oneChunk nm e.zeta, ← oneChunk nm e.zetaOmega]
  let some pub := p.pubEvals
    | throw "the step proof carries no public evaluations (one-chunk wire form)"
  let mut cells : List Fp := []
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
            evals := ← evalCells s.proof
            ftEval1 := s.proof.ftEval1
            prevChallenges
            digest := g 10 },
          ⟨s.vk.domainLog2, s.vk.omega⟩)

/-- One run of the step half: the interpreter's verdict, the decided satisfiability, and
the five bits. -/
def runStep (dom : Pickles.KnownDomain Fp) (inp : FopInput Fp) :
    IO (Bool × List (String × ℕ)) := do
  let nv := CircuitType.size Fp (FopInput Fp)
  let iv : FopInput (FVar Fp) := inputVar (F := Fp) (a := FopInput Fp)
  let m := fopStepOnAt [dom] iv
  let built := build m nv
  let st := seed (F := Fp) (avar := FopInput (FVar Fp)) inp
  match prove m st.nv st.env with
  | .error e => throw (IO.userError s!"prove failed: {repr e}")
  | .ok p =>
    let read (b : BoolVar Fp) : ℕ := ((b : CVar Fp).val p.assignments.get).val
    let bits := [("finalized", read p.result.finalized), ("xiCorrect", read p.result.xiCorrect),
      ("bCorrect", read p.result.bCorrect), ("cipCorrect", read p.result.cipCorrect),
      ("plonkOk", read p.result.plonkOk)]
    match provedSatisfies Kimchi.Fixture.PS.fpSide built p.assignments nv with
    | .error e => throw (IO.userError s!"reduction failed: {repr e}")
    | .ok sat => return (sat, bits)

def main : IO Unit := do
  let path := (← IO.getEnv "PROOF_CACHE").getD
    "../packages/pickles/test/fixtures/proof-cache/SimpleChain.json"
  let raw ← IO.FS.readFile path
  let (wraps, _) ← match Cache.parseFile CW Kimchi.Fixture.PS.fqSide.endo pallasBase.sqrt? raw with
    | .error e => throw (IO.userError s!"wrap side: {e}") | .ok r => pure r
  let (steps, _) ← match Cache.parseFile CS Kimchi.Fixture.PS.fpSide.endo vestaBase.sqrt? raw with
    | .error e => throw (IO.userError s!"step side: {e}") | .ok r => pure r
  IO.println s!"{path}: {wraps.size} wrap proofs, {steps.size} step proofs"
  let mut allOk := true
  let mut runs := 0
  for w in wraps do
    let some (d, pi) := w.step | continue
    let some s := steps.find? (fun s => s.vkDigest = d ∧ s.publicInputKey = pi)
      | IO.println s!"  ✗ wrap {w.vkDigest.take 10}…: its step {d.take 10}… is not in the file"
        allOk := false
        continue
    let (inp, dom) ← match assemble w s with
      | .error e => throw (IO.userError s!"assemble: {e}") | .ok r => pure r
    let t0 ← IO.monoMsNow
    let (sat, bits) ← runStep dom inp
    let t1 ← IO.monoMsNow
    let bitsOk := bits.all (·.2 = 1)
    IO.println s!"  {if sat ∧ bitsOk then "✓" else "✗"} step half on wrap→step \
      {d.take 10}… (domain 2^{s.vk.domainLog2}): satisfies={sat} \
      bits={bits.map fun (n, v) => s!"{n}={v}"} {t1 - t0} ms"
    runs := runs + 1
    unless sat ∧ bitsOk do allOk := false
  unless runs > 0 do throw (IO.userError "no wrap→step pairs to run")
  unless allOk do throw (IO.userError "check-halves FAILED")
  IO.println s!"✓ {runs} step-half run(s): every table satisfies its system, every bit reads 1"
