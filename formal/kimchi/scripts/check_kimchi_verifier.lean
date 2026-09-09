import KimchiFixture.Kimchi
import Kimchi.Verifier.Wire
import Lean.Data.Json

/-! The executable kimchi verifier against production proofs (`tools/fixture-dump`'s
`kimchi_proof_dump` / `kimchi_proof_dump_nc2`).

One verifier (`kimchiVerify`, over checked records at chunk count `nc`), exercised
through the client-side `verifyWire` composition below — parse the wire records with
`Wire.{KimchiVK,KimchiProof}.check`, then verify. Fixtures spanning both curves,
`nc ∈ {1, 2}`, both public-evaluation sources, `max_poly_size` at `n`, `n/2` and above
`n`, and the recursion path on a deployed pickles proof:

* `fixtures/kimchi_proof_vesta.json` — the one-chunk proof (`nc = 1`) without carried
  public evaluations (o1js / OCaml `to_repr` drop them at `nc = 1`), so the verifier
  recomputes them barycentrically — the `PubEvalSrc.barycentric` branch;
* `fixtures/kimchi_proof_vesta_pub.json` — the same proof with the carried
  `evals.public` (which `ProverProof::create` populates even at `nc = 1`, prover.rs:1048,
  and the verifier's first branch consumes at any chunk count, verifier.rs:332) — the
  `PubEvalSrc.carried` branch, its corruption case below flipping the verdict;
* `fixtures/kimchi_proof_{vesta,pallas}_nc2.json` — production `nc = 2` proofs on both
  curves (half-domain SRS, two chunks per column, carried public evaluations);
* `fixtures/kimchi_proof_pallas_pickles.json` — a deployed pickles wrap proof (OCaml
  through the Rust prover, `tree_proof_return` at two proofs; `kimchi_proof_dump_pickles`
  re-encodes it from the side-loaded fixture, the terminator's public input and its
  accumulator list) with its two old accumulators, at the wrap domain `2^14` below the
  `2^15` Tock SRS: the recursion path, and production's sub-SRS one-chunk regime.

Each run checks the accept bit, then two negative matrices:

* **verify-level corruptions** (the mutant still parses; the verdict must flip to
  REJECT): evaluation chunks on the ζ and ζω sides and beyond chunk 0 (`z` chunk 1, a
  witness-column chunk 1), the quotient commitment at chunk 0 and at the high chunk
  (`7·nc − 1`, the second `ft_comm` collapse group — exists only at `nc = 2`),
  an EMPTIED quotient commitment (which parses — production bounds `t_comm.len()` from
  above only, verifier.rs:260 — and must fail the ft identity), `ft_eval1`, (where
  carried) a public-evaluation chunk, and (where the proof carries accumulators) an old
  accumulator's commitment, one of its challenges, and the whole list dropped against
  the key's count;
* **parse rejections** (`Wire.check` must return `none` — ragged or mis-pinned wire
  input, matching production's `Err` returns): a ragged evaluation chunk vector, a
  missing `evals_public` at `nc > 1` (production's `MissingPublicInputEvaluation`,
  verifier.rs:334–335), an oversized `t_comm` (`> 7·nc`), a wrong opening round count
  (an `lr` pair popped — this failure arises in the IPA-side `Ipa.Wire.Proof.check`
  and propagates through `KimchiProof.check`), a ragged VK chunk vector, and (where
  the proof carries accumulators) an accumulator with a short challenge vector or a
  two-chunk commitment.

The emptied quotient carries one extra, positive assertion: that it PARSES. `verifyWire`
is check-then-verify, so a parse rejection would flip its verdict for the wrong reason —
the assertion is what keeps that corruption from agreeing vacuously if a
`0 < t_comm.size` wire guard is ever reinstated (negative control NC-5).

Every transcription judgment in the verifier (chunk absorb orders, the segment
flattening of the batch, the `ft_comm` double collapse, the carried-public precedence)
either reproduces production's accept bit here or fails. -/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi.Verifier

/-- The client-side composition: parse the wire records at the run's chunk count and
hand the checked records to the protocol verifier —
check-then-verify, the wire module's intended use. Ragged or mis-pinned input is
rejected, matching production's `Err` returns. -/
def verifyWire (C : Ipa.CommitmentCurve) (σ : Bulletproof.SRS C.Point)
    (vk : Wire.KimchiVK C) (p : Wire.KimchiProof C)
    (pub : Array C.ScalarField) : Bool :=
  match vk.check (Wire.runNc C σ vk), p.check (Wire.runNc C σ vk) σ.k with
  | some cvk, some cp => kimchiVerify C σ cvk cp pub
  | _, _ => false

/-- One chunked-verifier fixture run: decode (both formats), verify, and check the
corruption and parse-rejection matrices. Throws on any unexpected verdict.

`heavy` bounds the verify-based corruption matrix to acceptance plus the nc-specific
high-chunk corruption: at large `nc` each `kimchiVerify` is a `~7·nc`-chunk batch MSM
in the interpreter, so re-running the full matrix per corruption is prohibitively slow.
The skipped corruption KINDS (chunk-0 evals, `ft_eval1`, the base `t_comm` chunk) are
already exercised at `nc ≤ 2`; the kept high-chunk `t_comm` corruption keeps the nc > 2
run non-vacuous. The parse-rejection matrix is cheap (`Wire.check` short-circuits before
`kimchiVerify`), so it runs in full regardless. -/
def runChunked (C : Ipa.CommitmentCurve)
    (path : String) (expectPublic : Bool) (heavy : Bool := false) (olds : ℕ := 0) :
    IO Unit := do
  let raw ← IO.FS.readFile path
  let r : Except String
      (_ × Wire.KimchiVK C × Wire.KimchiProof C × Array C.ScalarField) := do
    let j ← Json.parse raw
    let vk ← Kimchi.Fixture.parseVK C j
    let mps ← match (← (← j.getObjVal? "max_poly_size").getStr?).toNat? with
      | some v => pure v
      | none => throw "field max_poly_size is not a numeral"
    -- `Nat.log2` truncates a non-two-power `max_poly_size` (external-audit C-4);
    -- production domains are radix-2, so fixture values are exact powers.
    let σ ← parseSRSAt C (Nat.log2 mps) j
    let proof ← Kimchi.Fixture.parseKimchiProof C j
    let pub ← parseArrOf (parseZMod (n := C.scalar)) (← j.getObjVal? "public")
    return (σ, vk, proof, pub)
  match r with
  | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  | .ok (σ, vk, proof, pub) =>
    unless proof.pubEvals.isSome == expectPublic do
      throw (IO.userError s!"{path}: unexpected evals_public presence")
    unless proof.prevChallenges.size = olds do
      throw (IO.userError s!"{path}: expected {olds} old accumulators, \
        got {proof.prevChallenges.size}")
    let nc := Wire.runNc C σ vk
    let verify (p : Wire.KimchiProof C) : Bool := verifyWire C σ vk p pub
    IO.println s!"{path}: verifying (nc = {nc}, {proof.prevChallenges.size} accumulators)…"
    (← IO.getStdout).flush
    let ok := verify proof
    IO.println s!"{path}: chunked verify (nc = {nc}): \
      {if ok then "ACCEPT" else "REJECT (BUG)"}"
    (← IO.getStdout).flush
    -- one chunk of the z evaluation bumped, on either evaluation point
    let bumpZ (zetaSide : Bool) (c : ℕ) : Wire.KimchiProof C :=
      { proof with evals := { proof.evals with z :=
          if zetaSide then
            { proof.evals.z with zeta := proof.evals.z.zeta.modify c (· + 1) }
          else
            { proof.evals.z with zetaOmega := proof.evals.z.zetaOmega.modify c (· + 1) } } }
    -- The empty quotient commitment (audit O-2), used twice below: once as a
    -- verify-level corruption, once as the parse-side non-vacuity control for it.
    let emptyT : Wire.KimchiProof C := { proof with tComm := #[] }
    -- verify-level corruptions: each mutant still parses; the verdict must flip.
    let mut corrupts : Array (String × Bool) := #[]
    -- The nc-specific high-chunk corruption (the second ft_comm collapse group). Kept
    -- even under `heavy`, so the nc > 2 run is non-vacuous.
    if 1 < nc then
      unless proof.tComm.size = 7 * nc do
        throw (IO.userError s!"{path}: expected a full quotient ({7 * nc} chunks), \
          got {proof.tComm.size} — the high-chunk corruption would be a no-op")
      corrupts := corrupts.push
        (s!"corrupted t comm (chunk {7 * nc - 1}, second collapse group)",
          !verify { proof with tComm := proof.tComm.modify (7 * nc - 1) (· + σ.h) })
    -- The full verify-based matrix — skipped when `heavy` (see the def docstring).
    unless heavy do
      corrupts := corrupts.push ("corrupted z eval (ζ, chunk 0)", !verify (bumpZ true 0))
      corrupts := corrupts.push ("corrupted t comm (chunk 0)",
        !verify { proof with tComm := proof.tComm.modify 0 (· + σ.h) })
      -- The empty quotient. Production bounds `t_comm.len()` from above only
      -- (verifier.rs:260), so this parses — and must be REJECTED at verify time, where
      -- the quotient side of the ft collapse becomes the empty sum `0`.
      corrupts := corrupts.push ("emptied t comm (the empty quotient, parses)",
        !verify emptyT)
      corrupts := corrupts.push ("corrupted ft_eval1",
        !verify { proof with ftEval1 := proof.ftEval1 + 1 })
      if 1 < nc then
        -- the degrees of freedom chunking introduced: ζω side, chunks beyond 0
        corrupts := corrupts.push ("corrupted z eval (ζ, chunk 1)", !verify (bumpZ true 1))
        corrupts := corrupts.push ("corrupted z eval (ζω, chunk 0)", !verify (bumpZ false 0))
        let w0 := proof.evals.w[0]
        corrupts := corrupts.push ("corrupted w[0] eval (ζ, chunk 1)",
          !verify { proof with evals := { proof.evals with
            w := proof.evals.w.set 0 { w0 with zeta := w0.zeta.modify 1 (· + 1) } } })
      match proof.pubEvals with
      | some pe =>
        corrupts := corrupts.push ("corrupted public eval (ζ, chunk 0)",
          !verify { proof with pubEvals := some { pe with zeta := pe.zeta.modify 0 (· + 1) } })
      | none =>
        IO.println "  - corrupted public eval: skipped (no carried evals at nc = 1)"
    -- The old accumulators, where the proof carries any (the recursion path): the
    -- commitment absorbed into the fq-sponge and opened at the head of the batch, the
    -- challenges digested into the fr-sponge and defining that row's claims, and the
    -- count guard against the key's — each must flip the verdict.
    -- (`withAcc f` rewrites the first accumulator by `f`.)
    let withAcc (f : Wire.RecursionChallenge C → Wire.RecursionChallenge C) :
        Wire.KimchiProof C :=
      { proof with prevChallenges := proof.prevChallenges.modify 0 f }
    if 0 < proof.prevChallenges.size then
      corrupts := corrupts.push ("corrupted old accumulator commitment",
        !verify (withAcc fun rc => { rc with comm := rc.comm.modify 0 (· + σ.h) }))
      corrupts := corrupts.push ("corrupted old accumulator challenge (round 0)",
        !verify (withAcc fun rc => { rc with chals := rc.chals.modify 0 (· + 1) }))
      corrupts := corrupts.push ("dropped old accumulators (count ≠ the key's)",
        !verify { proof with prevChallenges := #[] })
    for (name, rejected) in corrupts do
      IO.println s!"  {if rejected then "✓ REJECT" else "✗ ACCEPT (SOUNDNESS BUG)"}: {name}"
      (← IO.getStdout).flush
    -- parse rejections: `Wire.check` must return `none` on ragged/mis-pinned input.
    -- The first also runs through `verifyWire`, exercising the composition's
    -- `none => false` branch.
    let ragged : Wire.KimchiProof C := { proof with evals := { proof.evals with z :=
      { proof.evals.z with zeta := proof.evals.z.zeta.pop } } }
    let overT : Wire.KimchiProof C := { proof with tComm := proof.tComm.push σ.h }
    let badLr : Wire.KimchiProof C :=
      { proof with opening := { proof.opening with lr := proof.opening.lr.pop } }
    let raggedVK : Wire.KimchiVK C :=
      { vk with sigmaComm := vk.sigmaComm.set 0 (vk.sigmaComm[0]).pop }
    let mut parses : Array (String × Bool) := #[
      ("ragged z eval chunk vector", (ragged.check nc σ.k).isNone && !verify ragged),
      ("oversized t_comm (size > 7·nc)", (overT.check nc σ.k).isNone),
      ("wrong opening round count (lr pair popped; the IPA-side check)",
        (badLr.check nc σ.k).isNone),
      ("ragged VK chunk vector (sigma_comm[0])", (raggedVK.check nc).isNone)]
    if 1 < nc then
      let noPub : Wire.KimchiProof C := { proof with pubEvals := none }
      parses := parses.push ("missing evals_public at nc > 1", (noPub.check nc σ.k).isNone)
    if 0 < proof.prevChallenges.size then
      let shortChals := withAcc fun rc => { rc with chals := rc.chals.pop }
      let twoChunk := withAcc fun rc => { rc with comm := rc.comm.push σ.h }
      parses := parses.push ("old accumulator with a short challenge vector",
        (shortChals.check nc σ.k).isNone)
      parses := parses.push ("old accumulator with a two-chunk commitment",
        (twoChunk.check nc σ.k).isNone)
    for (name, rejected) in parses do
      IO.println s!"  {if rejected then "✓ none" else "✗ parsed (BUG)"}: {name}"
    -- Non-vacuity of the emptied-quotient corruption above (audit O-2). `verify` is
    -- check-then-verify, so a parse rejection would flip that verdict for the WRONG
    -- reason. Production bounds `t_comm.len()` from above only (verifier.rs:260), so the
    -- empty quotient must PARSE here and its rejection must be the ft identity's — the
    -- quotient side of the collapse being the empty sum `0`. Reinstating a
    -- `0 < t_comm.size` wire guard fails on THIS line (negative control NC-5).
    let emptyParses := (emptyT.check nc σ.k).isSome
    IO.println s!"  {if emptyParses then "✓ parses" else "✗ none (VACUOUS CONTROL)"}: \
      emptied t comm reaches the verifier"
    unless ok && emptyParses && corrupts.all (·.2) && parses.all (·.2) do
      throw (IO.userError s!"{path}: chunked kimchi verifier check FAILED")

abbrev CV := IpaVesta.curve
abbrev CP := IpaPallas.curve

-- Compiled entry point: `lake exe check-kimchi-verifier` (a `#eval main` here would run
-- the check interpreted at elaboration time — the slow path this exe target replaces).
def main : IO Unit := do
  let dir := (← IO.getEnv "KIMCHI_FIXTURES_DIR").getD "fixtures"
  -- `KIMCHI_FIXTURE_FILTER=<substring>` runs only the fixtures whose path contains it
  -- (for profiling one run); `KIMCHI_PICKLES_FIXTURE=1` adds the pickles proof, which the
  -- driver cannot yet afford (its 2^15-point opening check grows past 14 GB compiled).
  let filter ← IO.getEnv "KIMCHI_FIXTURE_FILTER"
  let withPickles := (← IO.getEnv "KIMCHI_PICKLES_FIXTURE").isSome
  let run (C : Ipa.CommitmentCurve) (path : String) (expectPublic : Bool)
      (heavy : Bool := false) (olds : ℕ := 0) : IO Unit := do
    let wanted : Bool := match filter with
      | some f => decide ((path.splitOn f).length > 1)
      | none => true
    if wanted then runChunked C path expectPublic heavy olds
    else IO.println s!"{path}: skipped (KIMCHI_FIXTURE_FILTER)"
  -- nc = 1: the deployed wire form (barycentric public evals), then the carried-public
  -- twin (the PubEvalSrc.carried branch at one chunk).
  run CV s!"{dir}/kimchi_proof_vesta.json" false
  run CV s!"{dir}/kimchi_proof_vesta_pub.json" true
  -- nc = 2 on both curves.
  run CV s!"{dir}/kimchi_proof_vesta_nc2.json" true
  run CP s!"{dir}/kimchi_proof_pallas_nc2.json" true
  -- Live EndoMul + VarBaseMul selectors at an empty public input (the audit's C-3 /
  -- V-1 mask): acceptance here pins the α-weighted constraint order and the
  -- scalar-register sign of both scalar-multiplication gates, and exercises the
  -- empty-public branch (public commitment = the all-ones blinding mask).
  run CV s!"{dir}/kimchi_proof_vesta_emul.json" false
  -- The recursion path on a deployed artifact: a pickles wrap proof (OCaml through the
  -- Rust prover, `tree_proof_return` at two proofs) with its two old accumulators, at
  -- the wrap domain 2^14 below the 2^15 Tock SRS — the sub-SRS one-chunk regime. Opt-in:
  -- every verify is a 2^15-point opening check, beyond the driver's memory today.
  if withPickles then
    run CP s!"{dir}/kimchi_proof_pallas_pickles.json" false (heavy := true) (olds := 2)
  IO.println s!"✓ the executable kimchi verifiers accept the production proofs (nc = 1 \
    barycentric and carried, nc = 2 on both curves, the live-EndoMul/VarBaseMul \
    empty-public proof{if withPickles then ", and a pickles wrap proof with its old \
    accumulators" else "; the pickles proof is out by default pending the driver's \
    memory"}), reject corruptions, and refuse to parse ragged wire data"
