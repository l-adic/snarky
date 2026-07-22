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

Each run checks the accept bit and a corruption matrix: an evaluation chunk, the
quotient commitment, `ft_eval1`, and (where carried) a public-evaluation chunk must
each flip the verdict to REJECT.

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
corruption rejections. Returns an error description or `none`. -/
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
    let ok := verifyWire C σ vk proof pub
    let badEval := { proof with
      evals := { proof.evals with
        z := { proof.evals.z with zeta := proof.evals.z.zeta.modify 0 (· + 1) } } }
    let badComm := { proof with tComm := proof.tComm.modify 0 (· + σ.h) }
    let badFt := { proof with ftEval1 := proof.ftEval1 + 1 }
    let r1 := !verifyWire C σ vk badEval pub
    let r2 := !verifyWire C σ vk badComm pub
    let r3 := !verifyWire C σ vk badFt pub
    let r4 ← match proof.pubEvals with
      | some pe =>
        let badPub := { proof with
          pubEvals := some { pe with zeta := pe.zeta.modify 0 (· + 1) } }
        pure (!verifyWire C σ vk badPub pub)
      | none => pure true
    IO.println s!"{path}: chunked verify: {if ok then "ACCEPT" else "REJECT"}, \
      corrupted z eval chunk: {if r1 then "REJECT (expected)" else "ACCEPT (BUG)"}, \
      corrupted t comm: {if r2 then "REJECT (expected)" else "ACCEPT (BUG)"}, \
      corrupted ft_eval1: {if r3 then "REJECT (expected)" else "ACCEPT (BUG)"}, \
      corrupted public eval: {if r4 then "REJECT (expected)" else "ACCEPT (BUG)"}"
    unless ok && r1 && r2 && r3 && r4 do
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
    and nc = 2, both curves) and reject corruptions"

#eval main
