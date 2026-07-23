import KimchiFixture.Kimchi
import Kimchi.Verifier.Wire
import Lean.Data.Json

/-! The executable kimchi verifier against production proofs (`tools/fixture-dump`'s
`kimchi_proof_dump` / `kimchi_proof_dump_nc2`).

One verifier (`kimchiVerify`, over checked records at chunk count `nc`), exercised
through the client-side `verifyWire` composition below — parse the wire records with
`Wire.{KimchiVK,KimchiProof}.check`, then verify. Six fixtures spanning both curves,
`nc ∈ {1, 2, 8}`, both public-evaluation sources, `max_poly_size` at and off `n/2`, and
identity (point-at-infinity) commitments:

* `fixtures/kimchi_proof_vesta.json` — the one-chunk proof (`nc = 1`) without carried
  public evaluations (o1js / OCaml `to_repr` drop them at `nc = 1`), so the verifier
  recomputes them barycentrically — the `PubEvalSrc.barycentric` branch;
* `fixtures/kimchi_proof_vesta_pub.json` — the same proof with the carried
  `evals.public` (which `ProverProof::create` populates even at `nc = 1`, prover.rs:1048,
  and the verifier's first branch consumes at any chunk count, verifier.rs:332) — the
  `PubEvalSrc.carried` branch, its corruption case below flipping the verdict;
* `fixtures/kimchi_proof_{vesta,pallas}_nc2.json` — production `nc = 2` proofs on both
  curves (half-domain SRS, two chunks per column, carried public evaluations);
* `fixtures/kimchi_proof_vesta_nc8.json` — an `nc = 8` proof (`max_poly_size = n/8`,
  `n = 64`, a full `56`-chunk quotient), for nc > 2 and `max_poly_size ≠ n/2`. (`nc = 3`
  is unproducible — a non-power-of-two `max_poly_size` misaligns the segment chunking
  and the prover rejects it.);
* `fixtures/kimchi_proof_vesta_identity.json` — a generic-only proof whose unused
  coefficient columns commit to the group identity (the `[0, 0]` `𝒪` sentinel), consumed
  in the opening batch — so the verifier's identity-point handling on the MSM path is
  exercised (not the sponge-absorption path; see audit M1).

Each run checks the accept bit, then two negative matrices:

* **verify-level corruptions** (the mutant still parses; the verdict must flip to
  REJECT): evaluation chunks on the ζ and ζω sides and beyond chunk 0 (`z` chunk 1, a
  witness-column chunk 1), the quotient commitment at chunk 0 and at the high chunk
  (`7·nc − 1`, the second `ft_comm` collapse group — exists only at `nc = 2`),
  `ft_eval1`, and (where carried) a public-evaluation chunk;
* **parse rejections** (`Wire.check` must return `none` — ragged or mis-pinned wire
  input, matching production's `Err` returns): a ragged evaluation chunk vector, a
  missing `evals_public` at `nc > 1` (production's `MissingPublicInputEvaluation`,
  verifier.rs:334–335), an oversized `t_comm` (`> 7·nc`), a wrong opening round count
  (an `lr` pair popped — this failure arises in the IPA-side `Ipa.Wire.Proof.check`
  and propagates through `KimchiProof.check`), and a ragged VK chunk vector.

Every transcription judgment in the verifier (chunk absorb orders, the segment
flattening of the batch, the `ft_comm` double collapse, the carried-public precedence)
either reproduces production's accept bit here or fails. -/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi.Verifier

/-- The client-side composition: parse the wire records at the run's chunk count
(under the SRS pin) and hand the checked records to the protocol verifier —
check-then-verify, the wire module's intended use. Ragged or mis-pinned input is
rejected, matching production's `Err` returns. -/
def verifyWire (C : Ipa.CommitmentCurve) (σ : Bulletproof.SRS C.Point)
    (vk : Wire.KimchiVK C) (p : Wire.KimchiProof C)
    (pub : Array C.ScalarField) : Bool :=
  if σ.k ≤ vk.domainLog2 then
    match vk.check (Wire.runNc C σ vk), p.check (Wire.runNc C σ vk) σ.k with
    | some cvk, some cp => kimchiVerify C σ cvk cp pub
    | _, _ => false
  else false

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
    (path : String) (expectPublic : Bool) (heavy : Bool := false) : IO Unit := do
  let raw ← IO.FS.readFile path
  let r : Except String
      (_ × Wire.KimchiVK C × Wire.KimchiProof C × Array C.ScalarField) := do
    let j ← Json.parse raw
    let vk ← Kimchi.Fixture.parseVK C j
    let mps ← match (← (← j.getObjVal? "max_poly_size").getStr?).toNat? with
      | some v => pure v
      | none => throw "field max_poly_size is not a numeral"
    let σ ← parseSRSAt C (Nat.log2 mps) j
    let proof ← Kimchi.Fixture.parseKimchiProof C j
    let pub ← parseArrOf (parseZMod (n := C.scalar)) (← j.getObjVal? "public")
    return (σ, vk, proof, pub)
  match r with
  | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  | .ok (σ, vk, proof, pub) =>
    unless proof.pubEvals.isSome == expectPublic do
      throw (IO.userError s!"{path}: unexpected evals_public presence")
    let nc := Wire.runNc C σ vk
    let verify (p : Wire.KimchiProof C) : Bool := verifyWire C σ vk p pub
    let ok := verify proof
    IO.println s!"{path}: chunked verify (nc = {nc}): \
      {if ok then "ACCEPT" else "REJECT (BUG)"}"
    -- one chunk of the z evaluation bumped, on either evaluation point
    let bumpZ (zetaSide : Bool) (c : ℕ) : Wire.KimchiProof C :=
      { proof with evals := { proof.evals with z :=
          if zetaSide then
            { proof.evals.z with zeta := proof.evals.z.zeta.modify c (· + 1) }
          else
            { proof.evals.z with zetaOmega := proof.evals.z.zetaOmega.modify c (· + 1) } } }
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
    for (name, rejected) in corrupts do
      IO.println s!"  {if rejected then "✓ REJECT" else "✗ ACCEPT (SOUNDNESS BUG)"}: {name}"
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
    for (name, rejected) in parses do
      IO.println s!"  {if rejected then "✓ none" else "✗ parsed (BUG)"}: {name}"
    unless ok && corrupts.all (·.2) && parses.all (·.2) do
      throw (IO.userError s!"{path}: chunked kimchi verifier check FAILED")

abbrev CV := IpaVesta.curve
abbrev CP := IpaPallas.curve

def main : IO Unit := do
  let dir := (← IO.getEnv "KIMCHI_FIXTURES_DIR").getD "fixtures"
  -- nc = 1: the deployed wire form (barycentric public evals), then the carried-public
  -- twin (the PubEvalSrc.carried branch at one chunk).
  runChunked CV s!"{dir}/kimchi_proof_vesta.json" false
  runChunked CV s!"{dir}/kimchi_proof_vesta_pub.json" true
  -- a generic-only proof: its unused coefficient columns commit to the identity (point
  -- at infinity, the [0,0] sentinel), so this exercises the verifier's identity handling
  -- on the opening-batch MSM path (not the sponge-absorption path; see audit M1).
  runChunked CV s!"{dir}/kimchi_proof_vesta_identity.json" false
  -- nc = 2 on both curves, then nc = 8 (max_poly_size ≠ n/2) on Vesta. The nc = 8 run
  -- uses the bounded corruption matrix (heavy := true): each verify there is a
  -- 56-chunk batch MSM.
  runChunked CV s!"{dir}/kimchi_proof_vesta_nc2.json" true
  runChunked CP s!"{dir}/kimchi_proof_pallas_nc2.json" true
  runChunked CV s!"{dir}/kimchi_proof_vesta_nc8.json" true
    (heavy := true)
  IO.println "✓ the executable kimchi verifiers accept the production proofs (nc = 1 \
    barycentric and carried, nc = 2 on both curves, nc = 8), reject corruptions, and \
    refuse to parse ragged wire data"

#eval main
