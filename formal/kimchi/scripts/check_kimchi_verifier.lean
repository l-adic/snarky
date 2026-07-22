import KimchiFixture.Chunked
import Lean.Data.Json

/-! The executable kimchi verifiers against production proofs (`tools/fixture-dump`'s
`kimchi_proof_dump` / `kimchi_proof_dump_nc2`):

* the `nc = 1` verifier (`kimchiVerify`) must ACCEPT the one-chunk wire proof
  (`fixtures/kimchi_proof_vesta.json`) and reject corruptions — the original composed
  adjudication of `Kimchi/Verifier/Kimchi.lean`;
* the CHUNKED verifier (`Chunked.kimchiVerify`) must accept the SAME one-chunk fixture
  through the singleton-chunk decoding — the no-regression adjudication of
  `Kimchi/Verifier/Chunked.lean` — and the production `nc = 2` fixtures on BOTH curves
  (`fixtures/kimchi_proof_{vesta,pallas}_nc2.json`: half-domain SRS, two chunks per
  column, proof-carried public evaluations), rejecting corruptions of an evaluation
  chunk, the quotient commitment, `ft_eval1`, and a carried public-evaluation chunk.

Every transcription judgment in the chunked verifier (chunk absorb orders, the segment
flattening of the batch, the `ft_comm` double collapse, the carried-public precedence)
either reproduces production's accept bit here or fails. -/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi.Verifier

/-- One chunked-verifier fixture run: decode (both formats), verify, and check the
corruption rejections. Returns an error description or `none`. -/
def runChunked (C : Ipa.CommitmentCurve) (frParams : Poseidon.Params C.ScalarField)
    (path : String) (expectPublic : Bool) : IO Unit := do
  let raw ← IO.FS.readFile path
  let r : Except String
      (_ × Chunked.KimchiVK C × Chunked.KimchiProof C × Array C.ScalarField) := do
    let j ← Json.parse raw
    let vk ← Kimchi.Fixture.Chunked.parseVK C frParams j
    let mps ← match (← (← j.getObjVal? "max_poly_size").getStr?).toNat? with
      | some v => pure v
      | none => throw "field max_poly_size is not a numeral"
    let σ ← parseSRSAt C (Nat.log2 mps) j
    let proof ← Kimchi.Fixture.Chunked.parseKimchiProof C j
    let pub ← parseArrOf (parseZMod (n := C.scalar)) (← j.getObjVal? "public")
    return (σ, vk, proof, pub)
  match r with
  | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  | .ok (σ, vk, proof, pub) =>
    unless proof.pubEvals.isSome == expectPublic do
      throw (IO.userError s!"{path}: unexpected evals_public presence")
    let ok := Chunked.kimchiVerify C σ vk proof pub
    let badEval := { proof with
      evals := { proof.evals with
        z := { proof.evals.z with zeta := proof.evals.z.zeta.modify 0 (· + 1) } } }
    let badComm := { proof with tComm := proof.tComm.modify 0 (· + σ.h) }
    let badFt := { proof with ftEval1 := proof.ftEval1 + 1 }
    let r1 := !Chunked.kimchiVerify C σ vk badEval pub
    let r2 := !Chunked.kimchiVerify C σ vk badComm pub
    let r3 := !Chunked.kimchiVerify C σ vk badFt pub
    let r4 ← match proof.pubEvals with
      | some pe =>
        let badPub := { proof with
          pubEvals := some { pe with zeta := pe.zeta.modify 0 (· + 1) } }
        pure (!Chunked.kimchiVerify C σ vk badPub pub)
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
  runChunked CV Chunked.KimchiVesta.frParams s!"{dir}/kimchi_proof_vesta.json" false
  runChunked CV Chunked.KimchiVesta.frParams s!"{dir}/kimchi_proof_vesta_nc2.json" true
  runChunked CP Chunked.KimchiPallas.frParams s!"{dir}/kimchi_proof_pallas_nc2.json" true
  IO.println "✓ the executable kimchi verifiers accept the production proofs (nc = 1 \
    and nc = 2, both curves) and reject corruptions"

#eval main
