import KimchiFixture.Kimchi
import Kimchi.Verifier.Wire
import Lean.Data.Json

/-! The executable kimchi verifier against production proofs (`tools/fixture-dump`'s
`kimchi_proof_dump` / `kimchi_proof_dump_nc2`).

ONE verifier (`kimchiVerify`, over checked records at chunk count `nc`), exercised
through the client-side `verifyWire` composition below — parse the wire records with
`Wire.{KimchiVK,KimchiProof}.check`, then verify. Three fixtures:

* `fixtures/kimchi_proof_vesta.json` — the one-chunk proof (`nc = 1`, the singleton
  case of the general verifier);
* `fixtures/kimchi_proof_{vesta,pallas}_nc2.json` — production `nc = 2` proofs on both
  curves (half-domain SRS, two chunks per column, proof-carried public evaluations).

Each run checks the accept bit, then two negative matrices:

* **verify-level corruptions** (the mutant still parses; the verdict must flip to
  REJECT): evaluation chunks on the ζ AND ζω sides and beyond chunk 0 (`z` chunk 1, a
  witness-column chunk 1), the quotient commitment at chunk 0 AND at the HIGH chunk
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
corruption and parse-rejection matrices. Throws on any unexpected verdict. -/
def runChunked (C : Ipa.CommitmentCurve) (frParams : Poseidon.Params C.ScalarField)
    (path : String) (expectPublic : Bool) : IO Unit := do
  let raw ← IO.FS.readFile path
  let r : Except String
      (_ × Wire.KimchiVK C × Wire.KimchiProof C × Array C.ScalarField) := do
    let j ← Json.parse raw
    let vk ← Kimchi.Fixture.parseVK C frParams j
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
    -- verify-level corruptions: each mutant still parses; the verdict must flip
    let mut corrupts : Array (String × Bool) := #[
      ("corrupted z eval (ζ, chunk 0)", !verify (bumpZ true 0)),
      ("corrupted t comm (chunk 0)",
        !verify { proof with tComm := proof.tComm.modify 0 (· + σ.h) }),
      ("corrupted ft_eval1", !verify { proof with ftEval1 := proof.ftEval1 + 1 })]
    if 1 < nc then
      -- the degrees of freedom chunking introduced: ζω side, chunks beyond 0, and
      -- the second ft_comm collapse group
      corrupts := corrupts.push ("corrupted z eval (ζ, chunk 1)", !verify (bumpZ true 1))
      corrupts := corrupts.push ("corrupted z eval (ζω, chunk 0)", !verify (bumpZ false 0))
      let w0 := proof.evals.w[0]
      corrupts := corrupts.push ("corrupted w[0] eval (ζ, chunk 1)",
        !verify { proof with evals := { proof.evals with
          w := proof.evals.w.set 0 { w0 with zeta := w0.zeta.modify 1 (· + 1) } } })
      unless proof.tComm.size = 7 * nc do
        throw (IO.userError s!"{path}: expected a full quotient ({7 * nc} chunks), \
          got {proof.tComm.size} — the high-chunk corruption would be a no-op")
      corrupts := corrupts.push
        (s!"corrupted t comm (chunk {7 * nc - 1}, second collapse group)",
          !verify { proof with tComm := proof.tComm.modify (7 * nc - 1) (· + σ.h) })
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
  -- The chunked verifier: the one-chunk fixture (no regression), then nc = 2 on both
  -- curves.
  runChunked CV Wire.KimchiVesta.frParams s!"{dir}/kimchi_proof_vesta.json" false
  runChunked CV Wire.KimchiVesta.frParams s!"{dir}/kimchi_proof_vesta_nc2.json" true
  runChunked CP Wire.KimchiPallas.frParams s!"{dir}/kimchi_proof_pallas_nc2.json" true
  IO.println "✓ the executable kimchi verifiers accept the production proofs (nc = 1 \
    and nc = 2, both curves), reject corruptions, and refuse to parse ragged wire data"

#eval main
